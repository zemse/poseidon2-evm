// Finite joint byte-allocation probe around the selected whole-entry schedule.
// GRID_WIDTH=16 GRID_FORK=osaka cargo test --release --locked --offline --lib joint_entry_budget_grid -- --ignored --nocapture
// No production option selection changes; every reported winner is compiled.
use super::*;
use crate::huff::fork::fork;
use crate::huff::render::{entry_bytes, render_entry, render_permutation};
use crate::huff::schedule::{
    Best, BuildOptions, BuildResult, Range, build_permutation, describe_options, group_candidates,
    steady_rounds, step_count,
};
use crate::round_constants::Params;

fn runtime_bytes(params: &Params, fork: Fork, result: &BuildResult) -> usize {
    result.bytes
        + entry_bytes(
            fork,
            params.t,
            &result.input_slots,
            result.state_in_memory,
            result.memory,
        )
}

fn compiled(params: &Params, fork: Fork, best: &Best) -> u64 {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let files = HashMap::from([
        (
            "grid/Permutation.huff".to_string(),
            render_permutation(
                params,
                &best.result,
                &best.opts,
                "../src/bn254/huff/Utils.huff",
                &fork,
            ),
        ),
        (
            "grid/Poseidon2.huff".to_string(),
            render_entry(params, &fork, &best.result),
        ),
    ]);
    let sources = Arc::new(Sources { root, files });
    let bytecode = compile(&sources, "grid/Poseidon2.huff", &fork).unwrap();
    assert_eq!(
        bytecode.runtime.len(),
        runtime_bytes(params, fork, &best.result)
    );
    let mut chain = Chain::new(&fork);
    let to = chain.deploy(bytecode.initcode).unwrap();
    let calls = check_permutation(&mut chain, to, &[], params.t, "entry grid").unwrap();
    assert_eq!(calls.len(), 24);
    let gas = same_gas(&calls, "entry grid").unwrap();
    assert_eq!(gas, super::super::entry_gas(&fork, params.t, &best.result));
    gas
}

#[test]
#[ignore = "finite wide schedule experiment"]
fn joint_entry_budget_grid() {
    let t: usize = std::env::var("GRID_WIDTH")
        .unwrap_or_else(|_| "16".into())
        .parse()
        .unwrap();
    assert!([16, 20, 24, 28].contains(&t));
    let name = std::env::var("GRID_FORK").unwrap_or_else(|_| "osaka".into());
    let fork = fork(&name).unwrap();
    let params = generate_params(t);
    let inputs = test_inputs(t);
    let range = Range {
        from: 0,
        to: step_count(&params),
    };
    let baseline = super::super::build_entry(&params, &inputs, fork)
        .unwrap()
        .unwrap();
    let baseline_gas = compiled(&params, fork, &baseline);
    println!(
        "GRID_BASELINE {name} t{t} gas {baseline_gas} bytes {} opts {}",
        runtime_bytes(&params, fork, &baseline.result),
        describe_options(&baseline.opts)
    );
    assert!(baseline.opts.shared_body);
    let (_, steady) = steady_rounds(&params, range);
    let mut groups = vec![0];
    groups.extend(group_candidates(
        &params,
        &fork,
        baseline.opts.consume_slots,
    ));
    if !groups.contains(&baseline.opts.consume_group) {
        groups.push(baseline.opts.consume_group);
    }
    let diagonals: Vec<_> = if baseline.opts.diag_in_memory {
        (0..=t).collect()
    } else {
        vec![baseline.opts.diag_push32]
    };
    let total = groups.len() * diagonals.len() * (steady + 1);
    println!(
        "GRID_SPACE {total} candidates groups {groups:?}, diagonals {diagonals:?}, inline 0..={steady}"
    );
    let mut best = baseline.clone();
    let mut best_gas = baseline_gas;
    let (mut attempted, mut built, mut fitting) = (0usize, 0usize, 0usize);
    for group in groups {
        for &diag in &diagonals {
            for inline in 0..=steady {
                attempted += 1;
                let opts = BuildOptions {
                    consume_group: group,
                    diag_push32: diag,
                    body_inline: inline,
                    ..baseline.opts
                };
                let Ok(result) = build_permutation(&params, &inputs, &opts, fork, range, false)
                else {
                    continue;
                };
                built += 1;
                if result.max_depth > 1000 || runtime_bytes(&params, fork, &result) > fork.code_size
                {
                    continue;
                }
                fitting += 1;
                let gas = super::super::entry_gas(&fork, t, &result);
                if gas < best_gas {
                    let text =
                        build_permutation(&params, &inputs, &opts, fork, range, true).unwrap();
                    assert_eq!(
                        (text.gas, text.bytes, text.memory),
                        (result.gas, result.bytes, result.memory)
                    );
                    let candidate = Best { result: text, opts };
                    assert_eq!(compiled(&params, fork, &candidate), gas);
                    println!(
                        "GRID_WIN {name} t{t} gas {gas} bytes {} group {group} diag {diag} inline {inline} after {attempted}/{total}",
                        runtime_bytes(&params, fork, &candidate.result)
                    );
                    best = candidate;
                    best_gas = gas;
                }
            }
            println!(
                "GRID_PROGRESS {attempted}/{total} built {built} fitting {fitting} best {best_gas} group {group} diag {diag}"
            );
        }
    }
    assert_eq!(attempted, total);
    assert!(fitting > 0);
    assert!(best_gas <= baseline_gas);
    println!(
        "GRID_DONE {name} t{t} baseline {baseline_gas} best {best_gas} saving {} attempts {attempted} built {built} fitting {fitting} bytes {} opts {}",
        baseline_gas - best_gas,
        runtime_bytes(&params, fork, &best.result),
        describe_options(&best.opts)
    );
}
