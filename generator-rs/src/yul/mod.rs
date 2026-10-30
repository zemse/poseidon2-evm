// Generates the Poseidon2 BN254 Yul libraries for a state width t
// (yul/generate.ts). t = 4 keeps the hash_1 / hash_2 / hash_3 /
// poseidon2_core library in src/bn254/yul/LibPoseidon2Yul.sol, other widths
// get an in-place permute(uint256[t] memory) library in src/bn254/yul/t<t>/
// and a Foundry test.

pub mod program;
pub mod render;
pub mod schedule;

use std::fs;
use std::path::Path;

use rayon::prelude::*;

use crate::error::Result;
use crate::huff::render::Vector;
use crate::reference::permutation;
use crate::round_constants::generate_params;
use crate::vectors::test_inputs;
use render::{
    library_name, render_array_library, render_forge_test, render_hash_library, render_wrapper,
};
use schedule::{Layout, Mode, build_hash_entry, build_permutation};

/// Per-width placement, tuned for the solc 0.8.30 setting with the least
/// runtime gas first (via-IR at 1,000,000 runs up to t = 8, the legacy
/// pipeline at 1,000,000 runs for t = 12):
/// locals up to the DUP16 / SWAP16 reach and every diag constant a PUSH32
/// literal (3 gas a read), with no regard to the 24,576 byte code size of a
/// contract using the library (t = 12 is about 39,400 bytes at 1,000,000
/// runs); a memory table, the scratch space or locals would cost 2 to 9 gas
/// a read.
fn layout_for(t: usize) -> Layout {
    if t <= 4 {
        return Layout {
            stack_elements: t,
            diag_in_memory: 0,
            diag_fixed: 0,
            diag_lets: if t == 4 { 4 } else { 0 },
            diag_scratch: 0,
            m4_temps: if t == 4 { 2 } else { 4 },
            internal_let: true,
            prime_first: t >= 3,
            internal_reduce_outputs: t == 2,
            periodic_internal: t == 3,
            raw_inputs: if t == 4 { 4 } else { 0 },
            fold_constants: false,
            nested_x5: t != 3,
            external_lets: t == 3,
            fold_first: false,
            table_absolute: false,
            m4_add_double: t == 4,
            tree_sum: false,
            rounds_function: false,
        };
    }
    if t == 8 {
        return Layout {
            stack_elements: 8,
            diag_in_memory: 0,
            diag_fixed: 0,
            diag_lets: 0,
            diag_scratch: 0,
            m4_temps: 2,
            internal_let: false,
            prime_first: false,
            internal_reduce_outputs: false,
            periodic_internal: false,
            raw_inputs: 0,
            fold_constants: false,
            nested_x5: false,
            external_lets: false,
            fold_first: false,
            table_absolute: false,
            m4_add_double: true,
            tree_sum: false,
            rounds_function: true,
        };
    }
    if t == 12 {
        return Layout {
            stack_elements: 12,
            diag_in_memory: 0,
            diag_fixed: 0,
            diag_lets: 0,
            diag_scratch: 0,
            m4_temps: 2,
            internal_let: false,
            prime_first: false,
            internal_reduce_outputs: false,
            periodic_internal: false,
            raw_inputs: 0,
            fold_constants: true,
            nested_x5: false,
            external_lets: false,
            fold_first: false,
            table_absolute: false,
            m4_add_double: true,
            tree_sum: true,
            rounds_function: false,
        };
    }
    Layout {
        stack_elements: 11,
        diag_in_memory: t,
        diag_fixed: 0,
        diag_lets: 0,
        diag_scratch: 0,
        m4_temps: 2,
        internal_let: false,
        prime_first: false,
        internal_reduce_outputs: false,
        periodic_internal: false,
        raw_inputs: 0,
        fold_constants: false,
        nested_x5: false,
        external_lets: false,
        fold_first: false,
        table_absolute: false,
        m4_add_double: false,
        tree_sum: false,
        rounds_function: false,
    }
}

/// The solc 0.8.30 settings that give a contract using the library its least
/// runtime gas and the gas there (the permute test wrapper, or a consumer of
/// hash_1 / hash_2 / hash_3 for t = 4), for the library's natspec. Measured
/// with the legacy pipeline (optimizer off, 200 and 1,000,000 runs) and
/// via-IR (200 and 1,000,000 runs); via-IR exceeds 40 GB for t = 12.
fn settings_note(t: usize) -> &'static str {
    match t {
        2 => {
            "Lowest runtime gas with solc 0.8.30 via-IR, optimizer on, runs = 1,000,000: 7,560 gas per permute of the test wrapper (legacy pipeline, runs = 1,000,000: 8,851)"
        }
        3 => {
            "Lowest runtime gas with solc 0.8.30 via-IR, optimizer on, runs = 1,000,000: 9,505 gas per permute of the test wrapper (legacy pipeline, runs = 1,000,000: 10,740)"
        }
        4 => {
            "Lowest runtime gas with solc 0.8.30 via-IR, optimizer on, runs = 1,000,000: 13,855 / 13,913 / 13,979 gas per hash_1 / hash_2 / hash_3 call of a consumer, which is then about 32,400 bytes, over the 24,576 byte limit before EIP-7954; legacy pipeline, runs = 1,000,000: 15,193 / 15,279 / 15,365 gas"
        }
        8 => {
            "Lowest runtime gas with solc 0.8.30 via-IR, optimizer on, runs = 1,000,000: 29,321 gas per permute of the test wrapper, which is then about 61,600 bytes, over the 24,576 byte limit before EIP-7954; legacy pipeline, runs = 1,000,000: 31,229 gas (about 27,500 bytes)"
        }
        12 => {
            "Lowest runtime gas with solc 0.8.30 legacy pipeline, optimizer on, runs = 1,000,000: 43,682 gas per permute of the test wrapper, which is then about 39,400 bytes, over the 24,576 byte limit before EIP-7954 (via-IR does not compile it)"
        }
        _ => "Not measured: this width is not shipped",
    }
}

/// The files of one width and its log lines.
struct Output {
    files: Vec<(String, String)>,
    log: Vec<String>,
}

fn generate(t: usize) -> Result<Output> {
    let params = generate_params(t);
    let inputs = test_inputs(t);
    let layout = layout_for(t);

    if t == 4 {
        let core = build_permutation(&params, &inputs, layout, Mode::Hash, 3)?;
        let rest = build_permutation(&params, &inputs, layout, Mode::HashRest, 3)?;
        let entries = (1..=3)
            .map(|n| build_hash_entry(&params, &inputs, n, 3))
            .collect::<Result<Vec<_>>>()?;
        let path = "src/bn254/yul/LibPoseidon2Yul.sol".to_string();
        let log = format!(
            "t=4 Rf={} Rp={}: wrote {path}",
            params.rounds_f, params.rounds_p
        );
        return Ok(Output {
            files: vec![(
                path,
                render_hash_library(&core, &rest, &entries, settings_note(t)),
            )],
            log: vec![log],
        });
    }

    let result = build_permutation(&params, &inputs, layout, Mode::Array, 3)?;
    let dir = format!("src/bn254/yul/t{t}");
    let lib = format!("{dir}/{}.sol", library_name(t));
    let vectors: Vec<Vector> = inputs
        .iter()
        .map(|input| Vector {
            input: input.clone(),
            output: permutation(&params, input),
        })
        .collect();
    let test = format!("test/Poseidon2YulT{t}.t.sol");
    let wrapper = format!("test/wrappers/Poseidon2YulT{t}.sol");
    let mut log = vec![format!(
        "t={t} Rf={} Rp={}: {} locals, {} diag constants as locals, {} in the scratch space, {} in memory, wrote {lib}, {wrapper}, {test}",
        params.rounds_f,
        params.rounds_p,
        layout.stack_elements,
        layout.diag_lets,
        layout.diag_scratch,
        layout.diag_in_memory
    )];
    if t > 12 {
        log.push(format!(
            "  t={t} exceeds the 24,576 byte code size limit; run its test with FOUNDRY_CODE_SIZE_LIMIT=100000"
        ));
    }
    Ok(Output {
        files: vec![
            (
                lib,
                render_array_library(&params, &layout, &result, settings_note(t)),
            ),
            (wrapper, render_wrapper(t)),
            (
                test,
                render_forge_test(&params, &vectors, t <= 12, layout.table_absolute),
            ),
        ],
        log,
    })
}

/// Builds every width (in parallel, next to `check`) and writes its files
/// under `root` in the order of `widths` once `check` passed; stops at the
/// first width that fails.
pub fn run(root: &Path, widths: &[usize], check: impl FnOnce() -> Result<()> + Send) -> Result<()> {
    let (checked, built): (Result<()>, Vec<Result<Output>>) =
        rayon::join(check, || widths.par_iter().map(|&t| generate(t)).collect());
    checked?;
    for output in built {
        let output = output?;
        for (path, text) in output.files {
            let path = root.join(path);
            if let Some(dir) = path.parent() {
                fs::create_dir_all(dir)?;
            }
            fs::write(path, text)?;
        }
        for line in output.log {
            println!("{line}");
        }
    }
    Ok(())
}
