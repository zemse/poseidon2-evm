// Generates the Poseidon2 BN254 Huff permutation for a state width t
// (huff/generate.ts). Every width gets src/bn254/huff/t<t>/Permutation.huff,
// and every width but t = 4 on the default fork an entry contract and a
// Foundry test; t = 4 gets the hash_1 / hash_2 / hash_3 entry
// t4/Poseidon2.huff instead (its own round 0 per arity and the rounds after
// it shared, tested by test/Poseidon2.t.sol). A fork other than the default
// gets src/bn254/huff/<fork>/t<t>/ and test/<fork>/ (t = 4 a generated test
// of the hash entry against the reference sponge). A permutation over the
// fork's code size is split into parts (split.rs), Part0.huff being the
// contract to call.
//
// The widths are built in parallel; their files are written and their lines
// logged in order once each is done, as the TS does one width at a time.
// Each width also names the contract to call and the gas the model expects
// for the call, which verify.rs measures.

pub mod emitter;
pub mod fork;
pub mod render;
pub mod schedule;
pub mod split;
pub(crate) mod sum_tree;
pub mod templates;
pub mod verify;

#[cfg(test)]
#[path = "entry_tests.rs"]
mod entry_tests;

use std::fs;
use std::path::Path;

use rayon::prelude::*;

use crate::error::Result;
use crate::field::U256;
use crate::reference::permutation;
use crate::round_constants::generate_params;
use crate::vectors::test_inputs;
use fork::{DEFAULT_HARDFORK, Fork};
use render::{
    MEMORY_UNKNOWN, Vector, entry_bytes, hash_entry, huff_dir, memory_gas, overhead,
    render_deploy_parts, render_entry, render_entry_plan, render_forge_test, render_hash_entry,
    render_hash_test, render_part, render_permutation, test_dir,
};
use schedule::{
    BuildOptions, BuildResult, Range, build_best, build_hash_prologue, build_hash_rounds,
    describe_options, step_count,
};
use split::{Part, split_permutation};

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
}

/// The contract a width is called through and the gas the model counts for
/// the call: entry, permutation, tail and memory expansion, as forge reports
/// the call.
#[derive(Debug, Clone)]
pub enum Target {
    /// Poseidon2.huff: t words in, t words out
    Entry { path: String, gas: u64 },
    /// Part0.huff .. Part<n-1>.huff, each part's gas with a cold hop to the
    /// next one but without the next one's own gas
    Parts { paths: Vec<String>, gas: Vec<u64> },
    /// hash_1 / hash_2 / hash_3 of t4/Poseidon2.huff with the gas of each,
    /// and an entry around the full permutation (`source`, never written)
    /// for the permutation alone
    Hash {
        path: String,
        gas: [u64; 3],
        entry: String,
        source: String,
        entry_gas: u64,
    },
}

/// One built width: its filesystem steps and its target.
pub struct Width {
    pub t: usize,
    actions: Vec<Action>,
    pub target: Target,
}

impl Width {
    /// the files the width writes, path and text
    pub fn files(&self) -> impl Iterator<Item = (&str, &str)> {
        self.actions.iter().filter_map(|a| match a {
            Action::Write(path, text) => Some((path.as_str(), text.as_str())),
            _ => None,
        })
    }
}

/// gas of a call to an unsplit permutation's entry
fn entry_gas(fork: &Fork, t: usize, result: &BuildResult) -> u64 {
    let o = overhead(
        *fork,
        t,
        &result.input_slots,
        result.state_in_memory,
        false,
        false,
        result.memory,
    );
    o.entry_gas + result.gas + o.tail_gas + memory_gas(result.memory.max(32 * t))
}

/// gas of a call to a part, with a cold hop to the next one
fn part_gas(part: &Part, t: usize) -> u64 {
    let (result, o) = (&part.best.result, &part.overhead);
    o.entry_gas + result.gas + o.tail_gas + memory_gas(result.memory.max(32 * t))
}

/// Whole permutation entry, with one retry when its actual wrapper frees
/// bytes for stored diagonals or shared-body rounds. Core-only budgets
/// (including the folded hash rounds) still use build_best_with directly.
pub fn build_entry(
    params: &crate::round_constants::Params,
    inputs: &[Vec<U256>],
    fork: Fork,
) -> Result<Option<schedule::Best>> {
    let range = Range {
        from: 0,
        to: step_count(params),
    };
    let serial = entry_with_retry(params.t, fork, |budget| {
        build_best(params, inputs, budget, fork, range)
    })?;
    let fused = improve_entry(params.t, fork, serial, |budget, prior| {
        schedule::build_fused_entry(params, inputs, budget, fork, prior.opts)
    });
    let seeded = improve_entry(params.t, fork, fused, |budget, prior| {
        schedule::build_seeded_entry(params, inputs, budget, fork, prior.opts)
    });
    Ok(improve_entry(params.t, fork, seeded, |budget, prior| {
        schedule::build_seeded_slots_entry(params, inputs, budget, fork, prior.opts)
    }))
}

/// The public permutation and the independently selected raw entry body.
/// A terminal body is never rendered as POSEIDON2_PERMUTATION.
pub struct EntryPlan {
    permutation: schedule::Best,
    terminal: Option<BuildResult>,
}

impl EntryPlan {
    pub fn permutation(&self) -> &schedule::Best {
        &self.permutation
    }

    pub fn terminal_result(&self) -> Option<&BuildResult> {
        self.terminal.as_ref()
    }

    pub fn entry_result(&self) -> &BuildResult {
        self.terminal_result().unwrap_or(&self.permutation.result)
    }
}

/// Select a raw entry without changing the public permutation's contract.
pub fn build_entry_plan(
    params: &crate::round_constants::Params,
    inputs: &[Vec<U256>],
    fork: Fork,
) -> Result<Option<EntryPlan>> {
    Ok(build_entry(params, inputs, fork)?.map(|best| plan_entry(params, inputs, fork, best)))
}

fn plan_entry(
    params: &crate::round_constants::Params,
    inputs: &[Vec<U256>],
    fork: Fork,
    permutation: schedule::Best,
) -> EntryPlan {
    let candidate = schedule::build_terminal(params, inputs, fork, &permutation);
    select_terminal(params.t, fork, permutation, candidate)
}

fn select_terminal(
    t: usize,
    fork: Fork,
    permutation: schedule::Best,
    candidate: Result<Option<BuildResult>>,
) -> EntryPlan {
    let terminal = candidate.ok().flatten().filter(|result| {
        entry_fits(t, fork, result)
            && result.max_dup <= fork.reach
            && entry_gas(&fork, t, result) < entry_gas(&fork, t, &permutation.result)
    });
    EntryPlan {
        permutation,
        terminal,
    }
}

fn entry_wrapper(t: usize, fork: Fork, result: &BuildResult) -> usize {
    entry_bytes(
        fork,
        t,
        &result.input_slots,
        result.state_in_memory,
        result.memory,
    )
}

fn entry_fits(t: usize, fork: Fork, result: &BuildResult) -> bool {
    result.max_depth <= 1000
        && result
            .bytes
            .checked_add(entry_wrapper(t, fork, result))
            .is_some_and(|bytes| bytes <= fork.code_size)
}

// Keep the completed serial retry, even when an alternative's wrapper or
// body changes the budget its own retry can use.
fn improve_entry(
    t: usize,
    fork: Fork,
    prior: Option<schedule::Best>,
    mut build: impl FnMut(usize, &schedule::Best) -> Result<Option<schedule::Best>>,
) -> Option<schedule::Best> {
    let prior = prior?;
    let reserved = entry_wrapper(t, fork, &prior.result);
    if let Ok(Some(candidate)) =
        entry_with_retry_from(t, fork, reserved, |budget| build(budget, &prior))
        && entry_gas(&fork, t, &candidate.result) < entry_gas(&fork, t, &prior.result)
    {
        Some(candidate)
    } else {
        Some(prior)
    }
}

fn entry_with_retry(
    t: usize,
    fork: Fork,
    build: impl FnMut(usize) -> Result<Option<schedule::Best>>,
) -> Result<Option<schedule::Best>> {
    entry_with_retry_from(
        t,
        fork,
        entry_bytes(fork, t, &[], false, MEMORY_UNKNOWN),
        build,
    )
}

fn entry_with_retry_from(
    t: usize,
    fork: Fork,
    reserved: usize,
    mut build: impl FnMut(usize) -> Result<Option<schedule::Best>>,
) -> Result<Option<schedule::Best>> {
    let Some(budget) = fork.code_size.checked_sub(reserved) else {
        return Ok(None);
    };
    let wrapper = |best: &schedule::Best| entry_wrapper(t, fork, &best.result);
    let fits = |best: &schedule::Best| entry_fits(t, fork, &best.result);
    let mut best = build(budget)?.filter(fits);
    if let Some(prior) = &best
        && (prior.opts.shared_body || prior.opts.diag_in_memory)
    {
        let actual = wrapper(prior);
        if actual < reserved
            && let Ok(Some(candidate)) = build(fork.code_size - actual)
            && fits(&candidate)
            && entry_gas(&fork, t, &candidate.result) < entry_gas(&fork, t, &prior.result)
        {
            best = Some(candidate);
        }
    }
    Ok(best)
}

fn generate(t: usize, fork: &Fork) -> Result<Width> {
    let params = generate_params(t);
    let inputs = test_inputs(t);
    let legacy = fork.name == DEFAULT_HARDFORK;
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
    let mut best = build_entry(&params, &inputs, *fork)?;
    // a whole permutation that fits only through the sub-chains of a shorter
    // body pays for the size (the chains, the calls, diag constants in
    // memory), which a split may beat
    let mut parts = None;
    if let Some(b) = &best
        && b.opts.consume_group > 0
    {
        let split = split_permutation(&params, &inputs, *fork)?;
        let single = entry_gas(fork, t, &b.result);
        if split.iter().map(|p| part_gas(p, t)).sum::<u64>() < single {
            actions.push(Action::Log(format!(
                "{label}: {}",
                describe(&b.result, &b.opts)
            )));
            actions.push(Action::Log(format!(
                "  {single} gas per call as one contract: the split below costs less"
            )));
            best = None;
        }
        parts = Some(split);
    }
    if let Some(best) = best {
        let (result, opts) = (&best.result, &best.opts);
        actions.push(Action::Log(format!("{label}: {}", describe(result, opts))));
        if t == 4 {
            // t4/Poseidon2.huff is the hash_1 / hash_2 / hash_3 entry: round 0
            // per arity, then the rounds after it shared, returning s0' alone
            actions.push(Action::MkdirAll(dir.clone()));
            actions.push(Action::Write(
                format!("{dir}/Permutation.huff"),
                render_permutation(&params, result, opts, utils_path, fork),
            ));
            let prologues = (1..=3)
                .map(|n| {
                    let words: Vec<Vec<U256>> =
                        inputs.iter().map(|input| input[..n].to_vec()).collect();
                    build_hash_prologue(&params, &words, *fork)
                })
                .collect::<Result<Vec<_>>>()?;
            let budget =
                fork.code_size - hash_entry(*fork, &prologues, (0, 0, MEMORY_UNKNOWN))?.bytes;
            let rounds = build_hash_rounds(&params, &prologues, budget, *fork)?;
            let entry = hash_entry(
                *fork,
                &prologues,
                (rounds.result.gas, rounds.result.bytes, rounds.result.memory),
            )?;
            actions.push(Action::Log(format!(
                "  hash rounds: {}",
                describe(&rounds.result, &rounds.opts)
            )));
            actions.push(Action::Write(
                format!("{dir}/Poseidon2.huff"),
                render_hash_entry(&params, fork, &rounds, &prologues, utils_path)?,
            ));
            // the default fork's test is the hand-written test/Poseidon2.t.sol
            let mut wrote = format!("{dir}/Permutation.huff, {dir}/Poseidon2.huff");
            if !legacy {
                actions.push(Action::MkdirAll(tests.clone()));
                actions.push(Action::Write(
                    test_path.clone(),
                    render_hash_test(&params, &inputs, fork),
                ));
                wrote += &format!(", {test_path}");
            }
            let gas: Vec<String> = entry
                .gas
                .iter()
                .enumerate()
                .map(|(i, g)| format!("hash_{} {g}", i + 1))
                .collect();
            actions.push(Action::Log(format!(
                "  wrote {wrote} ({} gas, {} runtime bytes)",
                gas.join(", "),
                entry.bytes
            )));
            let target = Target::Hash {
                path: format!("{dir}/Poseidon2.huff"),
                gas: entry.gas,
                entry: format!("{dir}/Entry.huff"),
                source: render_entry(&params, fork, result),
                entry_gas: entry_gas(fork, t, result),
            };
            return Ok(Width { t, actions, target });
        }
        actions.push(Action::MkdirAll(dir.clone()));
        // the parts of an earlier split
        actions.push(Action::Remove(format!("{dir}/DeployParts.sol")));
        actions.push(Action::RemoveParts(dir.clone(), 0));
        actions.push(Action::Write(
            format!("{dir}/Permutation.huff"),
            render_permutation(&params, result, opts, utils_path, fork),
        ));
        let plan = plan_entry(&params, &inputs, *fork, best);
        let result = plan.entry_result();
        actions.push(Action::Write(
            format!("{dir}/Poseidon2.huff"),
            render_entry_plan(&params, fork, &plan),
        ));
        actions.push(Action::MkdirAll(tests.clone()));
        actions.push(Action::Write(
            test_path.clone(),
            render_forge_test(&params, &vectors, fork, 1),
        ));
        let bytes = result.bytes
            + entry_bytes(
                *fork,
                t,
                &result.input_slots,
                result.state_in_memory,
                result.memory,
            );
        actions.push(Action::Log(format!(
            "  wrote {dir}/Permutation.huff, {dir}/Poseidon2.huff, {test_path} ({bytes} runtime bytes)"
        )));
        let target = Target::Entry {
            path: format!("{dir}/Poseidon2.huff"),
            gas: entry_gas(fork, t, result),
        };
        return Ok(Width { t, actions, target });
    }

    // over the code size: split at step boundaries
    let parts = match parts {
        Some(parts) => parts,
        None => split_permutation(&params, &inputs, *fork)?,
    };
    actions.push(Action::Log(format!(
        "{label}: {} parts (code size {})",
        parts.len(),
        fork.code_size
    )));
    actions.push(Action::MkdirAll(dir.clone()));
    let mut total = 0;
    let mut gases = Vec::new();
    for (i, part) in parts.iter().enumerate() {
        let (result, opts, o) = (&part.best.result, &part.best.opts, &part.overhead);
        let Range { from, to } = result.range;
        let bytes = result.bytes + o.bytes;
        let memory = memory_gas(result.memory.max(32 * t));
        let gas = part_gas(part, t);
        total += gas;
        gases.push(gas);
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
    let target = Target::Parts {
        paths: (0..parts.len())
            .map(|i| format!("{dir}/Part{i}.huff"))
            .collect(),
        gas: gases,
    };
    Ok(Width { t, actions, target })
}

/// Logs the lines of a width and applies its filesystem steps.
fn apply(root: &Path, actions: &[Action]) -> Result<()> {
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
                let mut i = *from;
                loop {
                    let path = root.join(format!("{dir}/Part{i}.huff"));
                    if !path.exists() {
                        break;
                    }
                    fs::remove_file(path)?;
                    i += 1;
                }
            }
        }
    }
    Ok(())
}

/// Builds every width (in parallel, next to `check`) and, with `write`, logs
/// its lines and writes its files under `root` in the order of `widths` once
/// `check` passed; stops at the first width that fails, after the widths
/// before it are written. Returns the widths for verify.rs.
pub fn run(
    root: &Path,
    fork: &Fork,
    widths: &[usize],
    write: bool,
    check: impl FnOnce() -> Result<()> + Send,
) -> Result<Vec<Width>> {
    let (checked, built): (Result<()>, Vec<Result<Width>>) = rayon::join(check, || {
        widths.par_iter().map(|&t| generate(t, fork)).collect()
    });
    checked?;
    let mut done = Vec::new();
    for width in built {
        let width = width?;
        if write {
            apply(root, &width.actions)?;
        }
        done.push(width);
    }
    Ok(done)
}
