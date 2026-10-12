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
use render::{library_name, render_array_library, render_forge_test, render_hash_library};
use schedule::{Layout, Mode, build_permutation};

/// Per-width placement, tuned against solc 0.8.30 (legacy pipeline, no
/// via-IR, optimizer off, 200 and 1,000,000 runs): locals up to the DUP16 /
/// SWAP16 reach, diag constants as locals where the reach allows, then in
/// the scratch space, a few as PUSH32 and the rest in a memory table, as the
/// 24,576 byte code size of a contract using the library requires.
fn layout_for(t: usize) -> Layout {
    if t <= 4 {
        return Layout {
            stack_elements: t,
            diag_in_memory: 0,
            diag_lets: if t == 4 { 4 } else { 0 },
            diag_scratch: 0,
            m4_temps: 4,
            internal_let: true,
            prime_first: t >= 3,
            internal_reduce_outputs: t == 2,
            periodic_internal: t == 3,
        };
    }
    if t == 8 {
        return Layout {
            stack_elements: 8,
            diag_in_memory: 0,
            diag_lets: 4,
            diag_scratch: 2,
            m4_temps: 4,
            internal_let: false,
            prime_first: false,
            internal_reduce_outputs: false,
            periodic_internal: false,
        };
    }
    if t == 12 {
        return Layout {
            stack_elements: 12,
            diag_in_memory: 9,
            diag_lets: 0,
            diag_scratch: 2,
            m4_temps: 2,
            internal_let: false,
            prime_first: false,
            internal_reduce_outputs: false,
            periodic_internal: false,
        };
    }
    Layout {
        stack_elements: 11,
        diag_in_memory: t,
        diag_lets: 0,
        diag_scratch: 0,
        m4_temps: 2,
        internal_let: false,
        prime_first: false,
        internal_reduce_outputs: false,
        periodic_internal: false,
    }
}

/// The files of one width and its log lines.
struct Output {
    files: Vec<(String, String)>,
    mkdir: Option<String>,
    log: Vec<String>,
}

fn generate(t: usize) -> Result<Output> {
    let params = generate_params(t);
    let inputs = test_inputs(t);
    let layout = layout_for(t);

    if t == 4 {
        let result = build_permutation(&params, &inputs, layout, Mode::Hash, 3)?;
        let path = "src/bn254/yul/LibPoseidon2Yul.sol".to_string();
        let log = format!(
            "t=4 Rf={} Rp={}: wrote {path}",
            params.rounds_f, params.rounds_p
        );
        return Ok(Output {
            files: vec![(path, render_hash_library(&result))],
            mkdir: None,
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
    let mut log = vec![format!(
        "t={t} Rf={} Rp={}: {} locals, {} diag constants as locals, {} in the scratch space, {} in memory, wrote {lib}, {test}",
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
            (lib, render_array_library(&params, &layout, &result)),
            (test, render_forge_test(&params, &vectors, t <= 12)),
        ],
        mkdir: Some(dir),
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
        if let Some(dir) = output.mkdir {
            fs::create_dir_all(root.join(dir))?;
        }
        for (path, text) in output.files {
            fs::write(root.join(path), text)?;
        }
        for line in output.log {
            println!("{line}");
        }
    }
    Ok(())
}
