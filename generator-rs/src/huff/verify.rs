// Compiles the generated Huff with huff-neo and runs it in revm on the fork
// it targets: every output word of the contract a width is called through is
// checked against the reference permutation (the t = 4 hash entry against the
// reference sponge) on the shared vectors plus random inputs, and the gas of
// the call is measured next to the model's. Split parts are deployed like
// DeployParts.sol does, last to first, each initcode but the last with the
// address of the part after it appended as a 32-byte word.
//
// Generated files come from memory, the others (Utils.huff, Eip8024.huff)
// from the repository, so nothing needs to be written.

use std::collections::{HashMap, HashSet};
use std::path::{Component, Path, PathBuf};
use std::sync::Arc;

use huff_neo_core::Compiler;
use huff_neo_utils::error::CompilerError;
use huff_neo_utils::evm_version::{EVMVersion, SupportedEVMVersions};
use huff_neo_utils::file::file_provider::FileProvider;
use huff_neo_utils::file::file_source::FileSource;
use huff_neo_utils::file::remapper::Remapper;
use huff_neo_utils::file::unpack_files::UnpackError;
use rayon::prelude::*;
use revm::context::result::{ExecutionResult, Output};
use revm::context::tx::TxEnvBuilder;
use revm::context::{BlockEnv, CfgEnv, TxEnv};
use revm::context_interface::transaction::{AccessList, AccessListItem};
use revm::database::{CacheDB, EmptyDB};
use revm::handler::{MainnetContext, MainnetEvm};
use revm::interpreter::{CallInputs, CallOutcome};
use revm::primitives::hardfork::SpecId;
use revm::primitives::{Address, Bytes, TxKind, address, hex, keccak256};
use revm::state::AccountInfo;
use revm::{Context, ExecuteCommitEvm, InspectEvm, Inspector, MainBuilder};

use super::fork::Fork;
use super::{Target, Width};
use crate::bail;
use crate::error::{Error, Result};
use crate::field::{U256, reduce};
use crate::reference::{hash_sponge, permutation};
use crate::round_constants::generate_params;
use crate::vectors::{Prng, test_inputs};

/// random inputs per width on top of the shared vectors, full 256-bit words
/// so the entry's reduction is exercised as well
const RANDOM_INPUTS: usize = 16;
const SEED: u64 = 0x7665_7269_6679;

const CALLER: Address = address!("0x1000000000000000000000000000000000000001");

// ---- compile ---------------------------------------------------------------

/// Huff sources: the generated files in memory over the repository.
#[derive(Debug)]
struct Sources {
    root: PathBuf,
    files: HashMap<String, String>,
}

/// `a/./b/../c` as `a/c`
fn normalize(path: &Path) -> String {
    let mut parts: Vec<&str> = Vec::new();
    for c in path.components() {
        match c {
            Component::CurDir | Component::RootDir | Component::Prefix(_) => {}
            Component::ParentDir => {
                parts.pop();
            }
            Component::Normal(p) => parts.push(p.to_str().unwrap_or_default()),
        }
    }
    parts.join("/")
}

impl Sources {
    fn read(&self, path: &str) -> Option<String> {
        if let Some(text) = self.files.get(path) {
            return Some(text.clone());
        }
        std::fs::read_to_string(self.root.join(path)).ok()
    }
}

impl FileProvider for Sources {
    fn read_file(&self, pb: PathBuf) -> std::result::Result<Arc<FileSource>, CompilerError> {
        let path = normalize(&pb);
        match self.read(&path) {
            Some(source) => Ok(Arc::new(FileSource {
                path,
                source: Some(source),
                access: None,
                dependencies: vec![],
            })),
            None => Err(CompilerError::FileUnpackError(UnpackError::MissingFile(
                path,
            ))),
        }
    }

    fn transform_paths(
        &self,
        sources: &[String],
    ) -> std::result::Result<Vec<PathBuf>, CompilerError> {
        Ok(sources.iter().map(PathBuf::from).collect())
    }
}

/// huff-neo has no Amsterdam; the EIP-8024 opcodes are __VERBATIM bytes
fn evm_version(fork: &Fork) -> EVMVersion {
    EVMVersion::new(match fork.name {
        "paris" => SupportedEVMVersions::Paris,
        "shanghai" => SupportedEVMVersions::Shanghai,
        "cancun" => SupportedEVMVersions::Cancun,
        "prague" => SupportedEVMVersions::Prague,
        _ => SupportedEVMVersions::Osaka,
    })
}

struct Compiled {
    initcode: Vec<u8>,
    runtime: Vec<u8>,
}

fn compile(sources: &Arc<Sources>, path: &str, fork: &Fork) -> Result<Compiled> {
    let fail = |err: &dyn std::fmt::Display| Error(format!("huff-neo, {path}: {err}"));
    let evm = evm_version(fork);
    let provider: Arc<dyn FileProvider> = sources.clone();
    let compiler = Compiler {
        evm_version: &evm,
        sources: Arc::new(vec![path.to_string()]),
        output: None,
        alternative_main: None,
        alternative_constructor: None,
        construct_args: None,
        constant_overrides: None,
        bytecode: false,
        cached: false,
        file_provider: provider.clone(),
        relax_jumps: false,
        // the fork's limit is revm's to enforce
        no_size_limit: true,
    };
    let file = provider
        .read_file(PathBuf::from(path))
        .map_err(|e| fail(&e))?;
    let remapper = Remapper::new(sources.root.to_string_lossy());
    let file =
        Compiler::recurse_deps(file, &remapper, provider, HashSet::new()).map_err(|e| fail(&e))?;
    let artifact = compiler.gen_artifact(file).map_err(|e| fail(&e))?;
    let decode = |code: &str| hex::decode(code).map_err(|e| fail(&e));
    Ok(Compiled {
        initcode: decode(&artifact.bytecode)?,
        runtime: decode(&artifact.runtime)?,
    })
}

// ---- execute ---------------------------------------------------------------

/// Gas of the outermost call frame, the number a forge trace shows for it.
#[derive(Default)]
struct FrameGas(u64);

impl<CTX> Inspector<CTX> for FrameGas {
    fn call_end(&mut self, _: &mut CTX, _: &CallInputs, outcome: &mut CallOutcome) {
        // the outermost frame ends last
        self.0 = outcome.result.gas.total_gas_spent();
    }
}

type Evm = MainnetEvm<MainnetContext<CacheDB<EmptyDB>>, FrameGas>;

fn spec(fork: &Fork) -> SpecId {
    match fork.name {
        "paris" => SpecId::MERGE,
        "shanghai" => SpecId::SHANGHAI,
        "cancun" => SpecId::CANCUN,
        "prague" => SpecId::PRAGUE,
        "osaka" => SpecId::OSAKA,
        _ => SpecId::AMSTERDAM,
    }
}

/// An EVM of the fork with one funded caller.
struct Chain {
    evm: Evm,
    nonce: u64,
}

impl Chain {
    fn new(fork: &Fork) -> Chain {
        let mut cfg = CfgEnv::new().with_spec_and_mainnet_gas_params(spec(fork));
        cfg.limit_contract_code_size = Some(fork.code_size);
        cfg.limit_contract_initcode_size = Some(fork.initcode_size);
        cfg.tx_gas_limit_cap = Some(u64::MAX);
        let block = BlockEnv {
            gas_limit: u64::MAX,
            basefee: 0,
            ..BlockEnv::default()
        };
        let mut db = CacheDB::new(EmptyDB::default());
        db.insert_account_info(
            CALLER,
            AccountInfo {
                balance: revm::primitives::U256::MAX,
                ..AccountInfo::default()
            },
        );
        let ctx: MainnetContext<CacheDB<EmptyDB>> = Context::new(db, spec(fork));
        let evm = ctx
            .with_cfg(cfg)
            .with_block(block)
            .build_mainnet_with_inspector(FrameGas::default());
        Chain { evm, nonce: 0 }
    }

    fn tx(&self, kind: TxKind, data: Vec<u8>) -> TxEnvBuilder {
        TxEnv::builder()
            .caller(CALLER)
            .kind(kind)
            .data(Bytes::from(data))
            .gas_limit(1 << 32)
            .gas_price(0)
            .nonce(self.nonce)
    }

    fn deploy(&mut self, initcode: Vec<u8>) -> Result<Address> {
        let tx = self.tx(TxKind::Create, initcode).build_fill();
        let result = self
            .evm
            .transact_commit(tx)
            .map_err(|e| Error(format!("deploy: {e:?}")))?;
        self.nonce += 1;
        match result {
            ExecutionResult::Success {
                output: Output::Create(_, Some(address)),
                ..
            } => Ok(address),
            other => bail!("deploy failed: {other:?}"),
        }
    }

    /// The output and the gas of the call frame, `warm` in the access list.
    fn call(&mut self, to: Address, data: Vec<u8>, warm: &[Address]) -> Result<(Vec<u8>, u64)> {
        let access: Vec<AccessListItem> = warm
            .iter()
            .map(|&address| AccessListItem {
                address,
                storage_keys: vec![],
            })
            .collect();
        let tx = self
            .tx(TxKind::Call(to), data)
            .access_list(AccessList(access))
            .build_fill();
        self.evm.inspector.0 = 0;
        // inspect_tx drops the state the call leaves
        let result = self
            .evm
            .inspect_tx(tx)
            .map_err(|e| Error(format!("call: {e:?}")))?
            .result;
        match result {
            ExecutionResult::Success {
                output: Output::Call(out),
                ..
            } => Ok((out.to_vec(), self.evm.inspector.0)),
            other => bail!("call failed: {other:?}"),
        }
    }
}

fn words(xs: &[U256]) -> Vec<u8> {
    xs.iter().flat_map(|x| x.to_be_bytes::<32>()).collect()
}

fn from_words(out: &[u8]) -> Vec<U256> {
    out.chunks(32).map(U256::from_be_slice).collect()
}

// ---- verify ----------------------------------------------------------------

/// Measured and model gas of one call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Gas {
    pub measured: u64,
    pub model: u64,
}

impl Gas {
    pub fn diff(&self) -> i64 {
        self.measured as i64 - self.model as i64
    }
}

impl std::fmt::Display for Gas {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} (model {}, {:+})",
            self.measured,
            self.model,
            self.diff()
        )
    }
}

#[derive(Debug, Clone)]
pub struct Report {
    pub t: usize,
    pub fork: &'static str,
    pub calls: usize,
    /// runtime bytes of each contract, Part0 first
    pub bytes: Vec<usize>,
    /// the call, every hop cold
    pub gas: Gas,
    /// a split width with every part in the access list
    pub warm: Option<Gas>,
    /// t = 4 hash entry: hash_1, hash_2, hash_3 (`gas` is hash_2) and the
    /// entry around the full permutation
    pub hashes: Option<[Gas; 3]>,
    pub permutation: Option<Gas>,
}

impl std::fmt::Display for Report {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let bytes: Vec<String> = self.bytes.iter().map(|b| b.to_string()).collect();
        write!(
            f,
            "t={} on {}: verified {} calls, {} runtime bytes, ",
            self.t,
            self.fork,
            self.calls,
            bytes.join(" + "),
        )?;
        match self.hashes {
            Some(hashes) => {
                for (i, gas) in hashes.iter().enumerate() {
                    write!(f, "hash_{} {gas}, ", i + 1)?;
                }
            }
            None => write!(f, "call gas {}", self.gas)?,
        }
        if let Some(warm) = self.warm {
            write!(f, " with cold hops, {warm} warm")?;
        }
        if let Some(perm) = self.permutation {
            write!(f, "permutation entry {perm}")?;
        }
        Ok(())
    }
}

/// the inputs of a width: the shared vectors, then random full words
fn inputs(t: usize) -> Vec<Vec<U256>> {
    let mut rand = Prng::new(SEED ^ t as u64);
    let mut inputs = test_inputs(t);
    for _ in 0..RANDOM_INPUTS {
        inputs.push((0..t).map(|_| rand.next_u256()).collect());
    }
    inputs
}

/// The one gas of every call (the code has no data-dependent gas).
fn same_gas(gas: &[u64], what: &str) -> Result<u64> {
    match gas.iter().min() {
        Some(&min) if gas.iter().all(|&g| g == min) => Ok(min),
        Some(&min) => bail!(
            "{what}: gas varies from {min} to {}",
            gas.iter().max().unwrap_or(&min)
        ),
        None => bail!("{what}: no calls"),
    }
}

/// Calls the permutation entry at `to` on every input and checks the output
/// against the reference; returns the gas of the calls.
fn check_permutation(
    chain: &mut Chain,
    to: Address,
    warm: &[Address],
    t: usize,
    what: &str,
) -> Result<Vec<u64>> {
    let params = generate_params(t);
    let mut gas = Vec::new();
    for (i, input) in inputs(t).iter().enumerate() {
        let (out, g) = chain.call(to, words(input), warm)?;
        let reduced: Vec<U256> = input.iter().map(|&x| reduce(x)).collect();
        let expected = permutation(&params, &reduced);
        if out.len() != 32 * t {
            bail!(
                "{what}, input {i}: {} bytes returned, expected {}",
                out.len(),
                32 * t
            );
        }
        for (k, (got, want)) in from_words(&out).iter().zip(&expected).enumerate() {
            if got != want {
                bail!("{what}, input {i}: word {k} is {got:#x}, the reference {want:#x}");
            }
        }
        gas.push(g);
    }
    Ok(gas)
}

const HASH_SIGNATURES: [&str; 3] = [
    "hash_1(uint256)",
    "hash_2(uint256,uint256)",
    "hash_3(uint256,uint256,uint256)",
];

/// hash_1 / hash_2 / hash_3 on the first 1, 2, 3 words of every input
/// against the reference sponge; returns the gas of the calls per arity.
fn check_hash(chain: &mut Chain, to: Address, what: &str) -> Result<[Vec<u64>; 3]> {
    let params = generate_params(4);
    let mut gas: [Vec<u64>; 3] = Default::default();
    for (i, input) in inputs(4).iter().enumerate() {
        for (n, signature) in HASH_SIGNATURES.iter().enumerate() {
            let args = &input[..n + 1];
            let mut data = keccak256(signature)[..4].to_vec();
            data.extend(words(args));
            let (out, g) = chain.call(to, data, &[])?;
            let want = hash_sponge(&params, args);
            if out.len() != 32 || U256::from_be_slice(&out) != want {
                bail!(
                    "{what}, input {i}: {signature} returned 0x{}, the reference sponge {want:#x}",
                    hex::encode(&out)
                );
            }
            gas[n].push(g);
        }
    }
    Ok(gas)
}

fn verify_width(sources: &Arc<Sources>, fork: &Fork, width: &Width) -> Result<Report> {
    let t = width.t;
    let mut chain = Chain::new(fork);
    let label = format!("t={t} on {}", fork.name);
    let calls = inputs(t).len();
    match &width.target {
        Target::Entry { path, gas } => {
            let code = compile(sources, path, fork)?;
            let to = chain.deploy(code.initcode)?;
            let measured = check_permutation(&mut chain, to, &[], t, &label)?;
            Ok(Report {
                t,
                fork: fork.name,
                calls,
                bytes: vec![code.runtime.len()],
                gas: Gas {
                    measured: same_gas(&measured, &label)?,
                    model: *gas,
                },
                warm: None,
                hashes: None,
                permutation: None,
            })
        }
        Target::Parts { paths, gas } => {
            let codes = paths
                .iter()
                .map(|path| compile(sources, path, fork))
                .collect::<Result<Vec<_>>>()?;
            // last to first, each initcode but the last with the next address
            let mut addresses: Vec<Address> = Vec::new();
            for code in codes.iter().rev() {
                let mut initcode = code.initcode.clone();
                if let Some(next) = addresses.last() {
                    initcode.extend([0u8; 12]);
                    initcode.extend(next.as_slice());
                }
                addresses.push(chain.deploy(initcode)?);
            }
            addresses.reverse();
            let cold = check_permutation(&mut chain, addresses[0], &[], t, &label)?;
            let warm = check_permutation(&mut chain, addresses[0], &addresses[1..], t, &label)?;
            let model: u64 = gas.iter().sum();
            let hops = (paths.len() - 1) as u64;
            Ok(Report {
                t,
                fork: fork.name,
                calls: 2 * calls,
                bytes: codes.iter().map(|c| c.runtime.len()).collect(),
                gas: Gas {
                    measured: same_gas(&cold, &label)?,
                    model,
                },
                warm: Some(Gas {
                    measured: same_gas(&warm, &label)?,
                    model: model - hops * (fork.cold_account - fork.warm_account),
                }),
                hashes: None,
                permutation: None,
            })
        }
        Target::Hash {
            path,
            gas,
            entry,
            entry_gas,
            ..
        } => {
            let code = compile(sources, path, fork)?;
            let to = chain.deploy(code.initcode)?;
            let measured = check_hash(&mut chain, to, &label)?;
            let perm = compile(sources, entry, fork)?;
            let perm_to = chain.deploy(perm.initcode)?;
            let perm_gas = check_permutation(&mut chain, perm_to, &[], t, &label)?;
            let mut hashes = [Gas {
                measured: 0,
                model: 0,
            }; 3];
            for (n, g) in measured.iter().enumerate() {
                hashes[n] = Gas {
                    measured: same_gas(g, &format!("{label} hash_{}", n + 1))?,
                    model: gas[n],
                };
            }
            Ok(Report {
                t,
                fork: fork.name,
                calls: 3 * calls + perm_gas.len(),
                bytes: vec![code.runtime.len()],
                gas: hashes[1],
                warm: None,
                hashes: Some(hashes),
                permutation: Some(Gas {
                    measured: same_gas(&perm_gas, &label)?,
                    model: *entry_gas,
                }),
            })
        }
    }
}

/// Compiles, deploys and checks every width (in parallel), printing a line
/// per width in order; fails at the first output that differs from the
/// reference.
pub fn verify(root: &Path, fork: &Fork, widths: &[Width]) -> Result<Vec<Report>> {
    let mut files = HashMap::new();
    for width in widths {
        for (path, text) in width.files() {
            files.insert(path.to_string(), text.to_string());
        }
        if let Target::Hash { entry, source, .. } = &width.target {
            files.insert(entry.clone(), source.clone());
        }
    }
    let sources = Arc::new(Sources {
        root: root.to_path_buf(),
        files,
    });
    let reports: Vec<Result<Report>> = widths
        .par_iter()
        .map(|width| verify_width(&sources, fork, width))
        .collect();
    let mut done = Vec::new();
    for report in reports {
        let report = report?;
        println!("{report}");
        done.push(report);
    }
    Ok(done)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::PRIME;
    use crate::huff::fork::fork;

    #[test]
    fn normalizes_include_paths() {
        assert_eq!(
            normalize(Path::new("./src/bn254/huff/t2/../Utils.huff")),
            "src/bn254/huff/Utils.huff"
        );
    }

    #[test]
    fn random_inputs_exceed_the_prime() {
        assert!(inputs(2).iter().flatten().any(|&x| x >= PRIME));
    }

    /// the checked-in t = 2 (DUPN / SWAPN) runs on Amsterdam only
    #[test]
    fn eip8024_needs_amsterdam() {
        let amsterdam = fork("amsterdam").unwrap();
        let sources = Arc::new(Sources {
            root: Path::new(env!("CARGO_MANIFEST_DIR")).join(".."),
            files: HashMap::new(),
        });
        let code = compile(&sources, "src/bn254/huff/t2/Poseidon2.huff", &amsterdam).unwrap();
        let input = words(&[U256::ZERO, U256::from(1)]);
        for (name, runs) in [("amsterdam", true), ("osaka", false)] {
            let mut chain = Chain::new(&fork(name).unwrap());
            let to = chain.deploy(code.initcode.clone()).unwrap();
            let call = chain.call(to, input.clone(), &[]);
            assert_eq!(call.is_ok(), runs, "{name}: {call:?}");
        }
    }
}
