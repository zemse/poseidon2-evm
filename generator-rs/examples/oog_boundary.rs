// Runs every proven artifact case (formal-verification/Poseidon2/Proofs/**)
// on revm's interpreter at gas G-1, G and G+1 (G the case's `gas` from the
// Lean proof) and checks what `Theorems.Total` claims: below G an
// out-of-gas halt, from G on the interface outcome: a return or revert with
// exactly g - G left, or the exceptional halt it names (a JUMP to no jump
// destination, a stack underflow).
//
// usage: cargo run --release --example oog_boundary -- <formal-verification/Poseidon2>
// PERTURB=1 adds 1 to every G, a control that must report mismatches.

use std::fs;
use std::path::{Path, PathBuf};

use poseidon2_gen::reference::{hash_sponge, permutation};
use poseidon2_gen::round_constants::generate_params;
use revm::bytecode::Bytecode;
use revm::interpreter::host::DummyHost;
use revm::interpreter::interpreter::{EthInterpreter, ExtBytecode};
use revm::interpreter::{
    CallInput, InputsImpl, InstructionResult, Interpreter, InterpreterAction, SharedMemory,
    instruction_table, instructions::gas_table_spec,
};
use revm::primitives::hardfork::SpecId;
use revm::primitives::{Bytes, hex};
use ruint::aliases::U256;

const P: U256 =
    ruint::uint!(0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001_U256);
const HASH_V2_SHORT: U256 =
    ruint::uint!(0x0fcc8f62b28d181b60d780425f6a28111c2de73ab52e084c8c15975a470682d5_U256);

#[derive(Debug, Clone, Copy, PartialEq)]
enum Kind {
    HuffPerm,
    HuffHash,
    /// the Osaka t = 4 hash entry, with its jump destinations j1, j3, jr
    HuffHashXor(usize, usize, usize),
    YulHash,
    YulPerm,
    HashV2,
}

struct Artifact {
    kind: Kind,
    t: usize,
    code: Vec<u8>,
    gas: Vec<u64>,
    case_names: Vec<String>,
}

fn parse_artifact(root: &Path, rel: &str) -> Option<Artifact> {
    // a large artifact's proof is Proofs/Generated/<rel>, its cases in the parts beside it
    let art = rel.strip_prefix("Generated/").unwrap_or(rel);
    let src = fs::read_to_string(root.join("Bytecode").join(art)).ok()?;
    let mut proof = fs::read_to_string(root.join("Proofs").join(rel)).ok()?;
    let parts = root.join("Proofs").join(rel.trim_end_matches(".lean"));
    for i in 0.. {
        let Ok(part) = fs::read_to_string(parts.join(format!("Part{i}.lean"))) else {
            break;
        };
        proof.push_str(&part);
    }
    let field = |k: &str| -> String {
        let i = src.find(&format!("  {k} := ")).unwrap() + k.len() + 6;
        src[i..].lines().next().unwrap().trim().to_string()
    };
    let kind = match field("kind").as_str() {
        ".huffPerm" => Kind::HuffPerm,
        ".huffHash" => Kind::HuffHash,
        k if k.starts_with("(.huffHashXor ") => {
            let n: Vec<usize> = k
                .trim_start_matches("(.huffHashXor ")
                .trim_end_matches(')')
                .split(' ')
                .map(|x| usize::from_str_radix(x.trim_start_matches("0x"), 16).unwrap())
                .collect();
            Kind::HuffHashXor(n[0], n[1], n[2])
        }
        ".yulHash" => Kind::YulHash,
        ".yulPerm" => Kind::YulPerm,
        ".hashV2" => Kind::HashV2,
        k => panic!("kind {k}"),
    };
    let t: usize = field("t").parse().unwrap();
    let size: usize = field("size").parse().unwrap();
    let w0 = src.find("words := [").unwrap() + 10;
    let w1 = w0 + src[w0..].find(']').unwrap();
    let mut code = Vec::new();
    for w in src[w0..w1].split(',') {
        let w = w.trim().trim_start_matches("0x");
        if w.is_empty() {
            continue;
        }
        let padded = format!("{w:0>64}");
        code.extend(hex::decode(padded).unwrap());
    }
    code.truncate(size);
    let g0 = proof.find("def gas : List Nat := [").unwrap() + 23;
    let g1 = g0 + proof[g0..].find(']').unwrap();
    let gas = proof[g0..g1]
        .split(',')
        .map(|s| s.trim().parse().unwrap())
        .collect();
    let case_names = proof
        .lines()
        .filter_map(|l| l.strip_prefix("/-! ### Case "))
        .map(|l| {
            l.split_once(": ")
                .unwrap()
                .1
                .trim_end_matches(" -/")
                .to_string()
        })
        .collect();
    Some(Artifact {
        kind,
        t,
        code,
        gas,
        case_names,
    })
}

fn word(cd: &[u8], off: usize) -> U256 {
    let mut b = [0u8; 32];
    for (i, x) in b.iter_mut().enumerate() {
        *x = cd.get(off + i).copied().unwrap_or(0);
    }
    U256::from_be_bytes(b)
}

fn words(cd: &[u8], off: usize, n: usize) -> Vec<U256> {
    (0..n).map(|i| word(cd, off + 32 * i) % P).collect()
}

fn enc(ws: &[U256]) -> Vec<u8> {
    ws.iter().flat_map(|w| w.to_be_bytes::<32>()).collect()
}

fn yul_capacity(cds: usize) -> U256 {
    let s = U256::from(cds).wrapping_sub(U256::from(4));
    (s >> 5) << 64
}

/// What the interface says a call does (Spec/Interface.lean).
enum Want {
    /// returns (success) or reverts with this output
    Ret(bool, Vec<u8>),
    /// halts with this exception, the frame keeping none of its gas
    Halt(InstructionResult),
}

/// The interface outcome (Spec/Interface.lean).
fn expected(a: &Artifact, cd: &[u8], v: u64) -> Want {
    let perm_head = |cd: &[u8]| {
        let mut ws = words(cd, 4, 3);
        ws.push(yul_capacity(cd.len()) % P);
        permutation(&generate_params(4), &ws)[0]
    };
    match a.kind {
        Kind::HuffPerm => Want::Ret(
            true,
            enc(&permutation(&generate_params(a.t), &words(cd, 0, a.t))),
        ),
        Kind::HuffHash | Kind::HuffHashXor(..) => {
            let hash = |n| {
                Want::Ret(
                    true,
                    enc(&[hash_sponge(&generate_params(4), &words(cd, 4, n))]),
                )
            };
            match (cd.len(), a.kind) {
                (0x24, _) => hash(1),
                (0x44, _) => hash(2),
                (0x64, _) => hash(3),
                (n, Kind::HuffHashXor(j1, j3, jr)) => {
                    if n == j1 ^ 0x21 {
                        hash(1)
                    } else if n == j3 ^ 0x21 {
                        hash(3)
                    } else if n == jr ^ 0x21 {
                        Want::Halt(InstructionResult::StackUnderflow)
                    } else {
                        Want::Halt(InstructionResult::InvalidJump)
                    }
                }
                _ => Want::Halt(InstructionResult::InvalidJump),
            }
        }
        Kind::YulHash => {
            if v != 0 {
                Want::Ret(false, vec![])
            } else {
                Want::Ret(true, enc(&[perm_head(cd)]))
            }
        }
        Kind::HashV2 => {
            if cd.len() < 4 {
                Want::Ret(true, enc(&[HASH_V2_SHORT]))
            } else {
                Want::Ret(true, enc(&[perm_head(cd)]))
            }
        }
        Kind::YulPerm => {
            let sel = selector(a.t);
            if cd.len() < 4
                || word(cd, 0) >> 224 != U256::from(sel)
                || v != 0
                || cd.len() - 4 < 32 * a.t
            {
                Want::Ret(false, vec![])
            } else {
                Want::Ret(
                    true,
                    enc(&permutation(&generate_params(a.t), &words(cd, 4, a.t))),
                )
            }
        }
    }
}

fn selector(t: usize) -> u32 {
    match t {
        2 => 0x81be1a25,
        3 => 0xa7982175,
        8 => 0x6e85443c,
        12 => 0x496f3b22,
        _ => 0,
    }
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 11
    }
    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.next() as u8).collect()
    }
}

fn with_sel(sel: u32, rest: Vec<u8>) -> Vec<u8> {
    let mut v = sel.to_be_bytes().to_vec();
    v.extend(rest);
    v
}

/// Representative (calldata, call value) for case j of the artifact's kind
/// (Checker/Check.lean `*Cases`).
fn calls(a: &Artifact, j: usize, rng: &mut Rng) -> Vec<(Vec<u8>, u64)> {
    let t = a.t;
    let big = u64::MAX;
    let ffs = vec![0xff; 32 * t];
    match a.kind {
        Kind::HuffPerm => vec![
            (rng.bytes(32 * t), 0),
            (ffs.clone(), 5),
            (vec![], 0),
            (rng.bytes(32 * t + 17), 0),
            (rng.bytes(7), 0),
        ],
        Kind::HuffHash => {
            // the sizes of case j: below 0x24, 0x24, between, 0x44, between, 0x64, above
            let sizes: &[usize] = match j {
                0 => &[0, 4, 0x23],
                1 => &[0x24],
                2 => &[0x25, 0x43],
                3 => &[0x44],
                4 => &[0x45, 0x63],
                5 => &[0x64],
                _ => &[0x65, 300],
            };
            sizes
                .iter()
                .flat_map(|&n| [(rng.bytes(n), 0), (vec![0xff; n], 7)])
                .collect()
        }
        Kind::HuffHashXor(j1, j3, jr) => {
            // the jump targets of case j (Check.lean `huffHashXorCases`), the size their xor
            // with 0x21
            let targets: Vec<usize> = match j {
                0 => vec![0, 4],
                1 => vec![0x05],
                2 => vec![0x06, 0x44],
                3 => vec![0x45],
                4 => vec![0x46, 0x64],
                5 => vec![0x65],
                6 => vec![0x66, jr - 1],
                7 => vec![jr],
                8 => vec![jr + 1, j3 - 1],
                9 => vec![j3],
                10 => vec![j3 + 1, j1 - 1],
                11 => vec![j1],
                _ => vec![j1 + 1, 40000],
            };
            targets
                .iter()
                .flat_map(|&x| {
                    let n = x ^ 0x21;
                    [(rng.bytes(n), 0), (vec![0xff; n], 7)]
                })
                .collect()
        }
        Kind::YulHash | Kind::HashV2 => {
            let off = if a.kind == Kind::YulHash { 1 } else { 0 };
            if a.kind == Kind::YulHash && j == 0 {
                vec![(vec![], 1), (rng.bytes(100), big)]
            } else if j - off < 4 {
                let n = j - off;
                vec![(rng.bytes(n), 0), (vec![0xff; n], 0)]
            } else {
                let v = if a.kind == Kind::HashV2 { 7 } else { 0 };
                vec![
                    (rng.bytes(4), v),
                    (rng.bytes(0x64), 0),
                    (vec![0xff; 0x64], 0),
                    (rng.bytes(0x45), 0),
                    (rng.bytes(500), v),
                ]
            }
        }
        Kind::YulPerm => {
            let sel = selector(t);
            let args = |rng: &mut Rng| rng.bytes(32 * t);
            match a.case_names[j].split(" (").next().unwrap() {
                "size < 4, no value" => vec![(vec![], 0), (rng.bytes(3), 0)],
                "size < 4, value" => vec![(vec![], 1), (rng.bytes(2), big)],
                "selector below, no value" => {
                    vec![(with_sel(sel - 1, args(rng)), 0), (with_sel(0, vec![]), 0)]
                }
                "selector below, value" => vec![(with_sel(sel - 1, args(rng)), 3)],
                "selector above, no value" => vec![
                    (with_sel(sel + 1, args(rng)), 0),
                    (with_sel(u32::MAX, vec![]), 0),
                ],
                "selector above, value" => vec![(with_sel(sel + 1, args(rng)), 1)],
                "call value" => vec![(with_sel(sel, args(rng)), 1), (with_sel(sel, vec![]), big)],
                "short arguments" => vec![
                    (with_sel(sel, vec![]), 0),
                    (with_sel(sel, rng.bytes(32 * t - 1)), 0),
                ],
                "call" => vec![
                    (with_sel(sel, args(rng)), 0),
                    (with_sel(sel, ffs.clone()), 0),
                    (with_sel(sel, rng.bytes(32 * t + 40)), 0),
                ],
                n => panic!("case {n}"),
            }
        }
    }
}

enum Res {
    Ok {
        success: bool,
        left: u64,
        out: Vec<u8>,
    },
    Halt(InstructionResult),
}

fn run(code: &[u8], spec: SpecId, cd: &[u8], v: u64, gas: u64) -> Res {
    let input = InputsImpl {
        input: CallInput::Bytes(Bytes::copy_from_slice(cd)),
        call_value: revm::primitives::U256::from(v),
        ..Default::default()
    };
    let mut interp = Interpreter::<EthInterpreter>::new(
        SharedMemory::new(),
        ExtBytecode::new(Bytecode::new_raw(Bytes::copy_from_slice(code))),
        input,
        false,
        spec,
        gas,
    );
    let table = instruction_table::<EthInterpreter, DummyHost>();
    let mut host = DummyHost::new(spec);
    let InterpreterAction::Return(res) = interp.run_plain(&table, &gas_table_spec(spec), &mut host)
    else {
        panic!("new frame");
    };
    match res.result {
        InstructionResult::Stop | InstructionResult::Return | InstructionResult::Revert => {
            Res::Ok {
                success: res.result != InstructionResult::Revert,
                left: res.gas.remaining(),
                out: res.output.to_vec(),
            }
        }
        r => Res::Halt(r),
    }
}

fn find(dir: &Path, base: &Path, out: &mut Vec<String>) {
    for e in fs::read_dir(dir).unwrap() {
        let p: PathBuf = e.unwrap().path();
        if p.is_dir() {
            find(&p, base, out);
        } else if p.extension().is_some_and(|x| x == "lean") {
            out.push(p.strip_prefix(base).unwrap().to_string_lossy().into_owned());
        }
    }
}

fn main() {
    let root = PathBuf::from(
        std::env::args()
            .nth(1)
            .expect("formal-verification/Poseidon2"),
    );
    let mut rels = Vec::new();
    find(&root.join("Proofs"), &root.join("Proofs"), &mut rels);
    rels.sort();
    let mut rng = Rng(0x5eed);
    let (mut runs, mut bad, mut renamed) = (0usize, 0usize, 0usize);
    for rel in rels {
        let Some(a) = parse_artifact(&root, &rel) else {
            continue;
        };
        let specs: &[SpecId] = if rel
            .trim_start_matches("Generated/")
            .starts_with("Huff/Amsterdam")
        {
            &[SpecId::AMSTERDAM]
        } else {
            &[SpecId::CANCUN, SpecId::OSAKA, SpecId::AMSTERDAM]
        };
        for &spec in specs {
            for (j, &g0) in a.gas.iter().enumerate() {
                let g = g0 + std::env::var("PERTURB").map_or(0, |s| s.parse::<u64>().unwrap());
                let mut notes = Vec::new();
                for (cd, v) in calls(&a, j, &mut rng) {
                    let want = expected(&a, &cd, v);
                    for gas in [0, g.saturating_sub(1), g, g + 1, g + 1000] {
                        runs += 1;
                        let r = run(&a.code, spec, &cd, v, gas);
                        let ok = match (&r, gas < g) {
                            (Res::Halt(InstructionResult::OutOfGas), true) => true,
                            (Res::Halt(_), true) => false,
                            (Res::Ok { .. }, true) => false,
                            (Res::Ok { success, left, out }, false) => match &want {
                                Want::Ret(ok, o) => success == ok && *left == gas - g && out == o,
                                Want::Halt(_) => false,
                            },
                            (Res::Halt(h), false) => match &want {
                                Want::Halt(w) if w == h => true,
                                // revm charges an ADD's 3 gas before it checks the stack,
                                // execution-specs and EVMLean check the stack first: with
                                // less than 3 left the same halt is named differently
                                Want::Halt(InstructionResult::StackUnderflow)
                                    if *h == InstructionResult::OutOfGas && gas - g < 3 =>
                                {
                                    renamed += 1;
                                    true
                                }
                                _ => false,
                            },
                        };
                        let desc = match &r {
                            Res::Ok { success, left, out } => format!(
                                "{} left {left} out {}B",
                                if *success { "ret" } else { "revert" },
                                out.len()
                            ),
                            Res::Halt(h) => format!("halt {h:?}"),
                        };
                        if !ok {
                            bad += 1;
                            println!(
                                "MISMATCH {rel} {spec:?} case {j} ({}) G={g} gas={gas} cds={} v={v}: {desc}",
                                a.case_names[j],
                                cd.len()
                            );
                        }
                        if gas == g || gas + 1 == g {
                            notes.push(desc);
                        }
                    }
                }
                notes.dedup();
                println!(
                    "{rel:32} {:9} case {j} {:38} G={g:6}  [G-1, G]: {}",
                    format!("{spec:?}"),
                    a.case_names[j],
                    notes.join(" | ")
                );
            }
        }
    }
    println!("{runs} runs, {bad} mismatches, {renamed} halts named differently");
    if bad > 0 {
        std::process::exit(1);
    }
}
