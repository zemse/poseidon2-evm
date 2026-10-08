// Generates the Poseidon2 BN254 Huff permutation for a state width t
// (huff/generate.ts). Every width gets src/bn254/huff/t<t>/Permutation.huff,
// and every width but t = 4 on the default fork (whose hash entry
// t4/Poseidon2.huff is hand-written) an entry contract and a Foundry test; a
// fork other than the default gets src/bn254/huff/<fork>/t<t>/ and
// test/<fork>/. A permutation over the fork's code size is split into parts
// (split.rs), Part0.huff being the contract to call.
//
// The widths are built in parallel; their files are written and their lines
// logged in order once each is done, as the TS does one width at a time.

pub mod emitter;
pub mod fork;
pub mod render;
pub mod schedule;
pub mod split;

use std::fs;
use std::path::Path;

use rayon::prelude::*;

use crate::error::Result;
use crate::reference::permutation;
use crate::round_constants::generate_params;
use crate::vectors::test_inputs;
use fork::{DEFAULT_HARDFORK, Fork};
use render::{
    Vector, entry_bytes, huff_dir, memory_gas, render_deploy_parts, render_eip8024, render_entry,
    render_forge_test, render_part, render_permutation, render_zero, test_dir,
};
use schedule::{BuildOptions, BuildResult, Range, build_best, describe_options, step_count};
use split::split_permutation;

/// entry contract (calldata loads, stores, return) plus Utils.huff constants
const ENTRY_OVERHEAD: usize = 12 * 12 + 64;

fn describe(result: &BuildResult, opts: &BuildOptions) -> String {
    let shadow = if result.stores + result.loads > 0 {
        format!(", {} shadowed, {} loads", result.stores, result.loads)
    } else {
        String::new()
    };
    format!(
        "{} gas, {} bytes, depth {}, dup {}, {} swaps, {} pops{shadow}, options: {}",
        result.gas,
        result.bytes,
        result.max_depth,
        result.max_dup,
        result.swaps,
        result.pops,
        describe_options(opts)
    )
}

/// A filesystem step of one width, applied in order after the build.
enum Action {
    Log(String),
    MkdirAll(String),
    Write(String, String),
    /// remove the file if it exists
    Remove(String),
    /// remove Part<from>.huff, Part<from + 1>.huff, ... while they exist
    RemoveParts(String, usize),
    ForkFiles,
}

fn generate(t: usize, fork: &Fork) -> Result<Vec<Action>> {
    let params = generate_params(t);
    let inputs = test_inputs(t);
    let legacy = fork.name == DEFAULT_HARDFORK;
    let overhead = if legacy && t == 4 {
        ENTRY_OVERHEAD
    } else {
        entry_bytes(*fork, t, &[], false)
    };
    let dir = format!("{}/t{t}", huff_dir(fork));
    let utils_path = if legacy {
        "../Utils.huff"
    } else {
        "../../Utils.huff"
    };
    let vectors: Vec<Vector> = inputs
        .iter()
        .map(|input| Vector {
            input: input.clone(),
            output: permutation(&params, input),
        })
        .collect();
    let tests = test_dir(fork);
    let test_path = format!("{tests}/Poseidon2T{t}.t.sol");
    let label = format!(
        "t={t} Rf={} Rp={} on {}",
        params.rounds_f, params.rounds_p, fork.name
    );
    let mut actions = Vec::new();

    let range = Range {
        from: 0,
        to: step_count(&params),
    };
    if let Some(best) = build_best(&params, &inputs, fork.code_size - overhead, *fork, range)? {
        let (result, opts) = (&best.result, &best.opts);
        actions.push(Action::Log(format!("{label}: {}", describe(result, opts))));
        if t == 4 && legacy {
            // t4/Poseidon2.huff is the hand-written hash_1 / hash_2 / hash_3
            // entry
            let path = format!("{dir}/Permutation.huff");
            actions.push(Action::ForkFiles);
            actions.push(Action::Write(
                path.clone(),
                render_permutation(&params, result, opts, utils_path, fork),
            ));
            actions.push(Action::Log(format!("  wrote {path}")));
            return Ok(actions);
        }
        actions.push(Action::MkdirAll(dir.clone()));
        actions.push(Action::ForkFiles);
        actions.push(Action::Remove(format!("{dir}/DeployParts.sol")));
        actions.push(Action::Write(
            format!("{dir}/Permutation.huff"),
            render_permutation(&params, result, opts, utils_path, fork),
        ));
        actions.push(Action::Write(
            format!("{dir}/Poseidon2.huff"),
            render_entry(&params, fork, result),
        ));
        actions.push(Action::MkdirAll(tests.clone()));
        actions.push(Action::Write(
            test_path.clone(),
            render_forge_test(&params, &vectors, fork, 1),
        ));
        let bytes =
            result.bytes + entry_bytes(*fork, t, &result.input_slots, result.state_in_memory);
        actions.push(Action::Log(format!(
            "  wrote {dir}/Permutation.huff, {dir}/Poseidon2.huff, {test_path} ({bytes} runtime bytes)"
        )));
        return Ok(actions);
    }

    // over the code size: split at step boundaries
    let parts = split_permutation(&params, &inputs, *fork)?;
    actions.push(Action::Log(format!(
        "{label}: {} parts (code size {})",
        parts.len(),
        fork.code_size
    )));
    actions.push(Action::MkdirAll(dir.clone()));
    actions.push(Action::ForkFiles);
    let mut total = 0;
    for (i, part) in parts.iter().enumerate() {
        let (result, opts, o) = (&part.best.result, &part.best.opts, &part.overhead);
        let Range { from, to } = result.range;
        let bytes = result.bytes + o.bytes;
        let memory = memory_gas(result.memory.max(32 * t + 32));
        let gas = o.entry_gas + result.gas + o.tail_gas + memory;
        total += gas;
        actions.push(Action::Log(format!(
            "  part {i}: steps {from}..{}, {bytes} bytes, {gas} gas (entry {}, tail {}, memory {memory}): {}",
            to as i64 - 1,
            o.entry_gas,
            o.tail_gas,
            describe(result, opts)
        )));
        actions.push(Action::Write(
            format!("{dir}/Part{i}.huff"),
            render_part(&params, result, opts, utils_path, fork, i, parts.len()),
        ));
    }
    actions.push(Action::Write(
        format!("{dir}/DeployParts.sol"),
        render_deploy_parts(),
    ));
    // parts of an earlier, longer split
    actions.push(Action::RemoveParts(dir.clone(), parts.len()));
    actions.push(Action::MkdirAll(tests));
    actions.push(Action::Write(
        test_path.clone(),
        render_forge_test(&params, &vectors, fork, parts.len()),
    ));
    actions.push(Action::Log(format!(
        "  {total} gas per call with {} cold hops ({} each; warm {}), wrote {dir}/Part0..{}.huff, {test_path}",
        parts.len() - 1,
        fork.cold_account,
        fork.warm_account,
        parts.len() - 1
    )));
    Ok(actions)
}

/// the opcode macros a fork needs next to its width directories
fn write_fork_files(root: &Path, fork: &Fork) -> Result<()> {
    if fork.reach > 16 {
        fs::write(
            root.join(format!("{}/Eip8024.huff", huff_dir(fork))),
            render_eip8024(fork.reach),
        )?;
    }
    if !fork.push0 {
        fs::write(
            root.join(format!("{}/Zero.huff", huff_dir(fork))),
            render_zero(),
        )?;
    }
    Ok(())
}

fn apply(root: &Path, fork: &Fork, actions: Vec<Action>) -> Result<()> {
    for action in actions {
        match action {
            Action::Log(line) => println!("{line}"),
            Action::MkdirAll(dir) => fs::create_dir_all(root.join(dir))?,
            Action::Write(path, text) => fs::write(root.join(path), text)?,
            Action::Remove(path) => {
                let path = root.join(path);
                if path.exists() {
                    fs::remove_file(path)?;
                }
            }
            Action::RemoveParts(dir, from) => {
                let mut i = from;
                loop {
                    let path = root.join(format!("{dir}/Part{i}.huff"));
                    if !path.exists() {
                        break;
                    }
                    fs::remove_file(path)?;
                    i += 1;
                }
            }
            Action::ForkFiles => write_fork_files(root, fork)?,
        }
    }
    Ok(())
}

/// Builds every width (in parallel, next to `check`) and writes its files
/// under `root` in the order of `widths` once `check` passed; stops at the
/// first width that fails, after the widths before it are written.
pub fn run(
    root: &Path,
    fork: &Fork,
    widths: &[usize],
    check: impl FnOnce() -> Result<()> + Send,
) -> Result<()> {
    let (checked, built): (Result<()>, Vec<Result<Vec<Action>>>) = rayon::join(check, || {
        widths.par_iter().map(|&t| generate(t, fork)).collect()
    });
    checked?;
    for actions in built {
        apply(root, fork, actions?)?;
    }
    Ok(())
}
