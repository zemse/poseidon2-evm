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

#[test]
fn fused_accumulation_inventory() {
    use crate::field::{PRIME, UINT256_MAX, u256};
    use crate::huff::sum_tree;
    let leaf = (PRIME - u256(1)) * u256(2);
    for n in 6..=14 {
        let bounds = vec![leaf; n];
        let pre = sum_tree::plan_peak(&bounds, UINT256_MAX).unwrap();
        let late = sum_tree::plan_late(&bounds, UINT256_MAX, true).unwrap();
        let mut bound = leaf;
        let mut serial = 0;
        for _ in 1..n {
            if let Some(next) = bound.checked_add(leaf) {
                bound = next;
                serial += 3;
            } else {
                bound = PRIME - u256(1);
                serial += 14;
            }
        }
        let leaf_copies = 3 * n as u64;
        assert!(pre.gas <= late.gas);
        assert!(late.gas - leaf_copies <= serial);
        let bounded = sum_tree::plan_peak(&bounds, bound).unwrap();
        assert!(bounded.bound <= bound);
        assert!(bounded.gas - leaf_copies <= serial);
        println!(
            "FUSED_BOUNDED_INVENTORY n {n} gas {} cap {bound:#x}",
            bounded.gas - leaf_copies
        );
        println!(
            "FUSED_INVENTORY n {n} serial {serial} pre {} late {} pre_peak {} late_peak {}",
            pre.gas - leaf_copies,
            late.gas - leaf_copies,
            pre.peak,
            late.peak
        );
    }
}

#[test]
fn streaming_fused_replays_fixed_legacy_bodies() {
    use crate::huff::schedule::{DEFAULT_OPTIONS, FusedTree};
    for name in ["paris", "shanghai", "cancun", "prague", "osaka"] {
        let fork = fork(name).unwrap();
        for t in [24, 28] {
            let params = generate_params(t);
            let inputs = test_inputs(t);
            let range = Range {
                from: 0,
                to: step_count(&params),
            };
            let opts = BuildOptions {
                external_d: true,
                prime_under_external: false,
                internal_consume: true,
                prime_stack: true,
                shadow: true,
                shared_body: true,
                consume_group: if t == 24 { 6 } else { 3 },
                consume_slots: if t == 24 { 14 } else { 13 },
                external_template: true,
                prime_in_memory: t == 24,
                external_stream: true,
                compact_inputs: true,
                tree_sums: true,
                tree_peak: true,
                tree_adaptive_prime: t == 24,
                ..DEFAULT_OPTIONS
            };
            let result = build_permutation(&params, &inputs, &opts, fork, range, true).unwrap();
            let baseline = Best { opts, result };
            let before = compiled(&params, fork, &baseline);
            assert_eq!(
                before,
                match (name, t) {
                    ("paris", 24) => 76017,
                    ("paris", 28) => 92100,
                    (_, 24) => 75843,
                    (_, 28) => 91920,
                    _ => unreachable!(),
                }
            );
            let (fused_tree, saving) = if t == 24 {
                (FusedTree::PreplacedBounded, 495)
            } else {
                (FusedTree::Preplaced, 1140)
            };
            let opts = BuildOptions { fused_tree, ..opts };
            let result = build_permutation(&params, &inputs, &opts, fork, range, true).unwrap();
            let model = build_permutation(&params, &inputs, &opts, fork, range, false).unwrap();
            assert_eq!(
                (result.gas, result.bytes, result.memory),
                (model.gas, model.bytes, model.memory)
            );
            assert_eq!(result.loads, baseline.result.loads);
            assert_eq!(result.stores, baseline.result.stores);
            assert_eq!(result.max_depth, baseline.result.max_depth);
            assert!(result.max_depth <= 1000);
            assert!(runtime_bytes(&params, fork, &result) <= fork.code_size);
            let candidate = Best { opts, result };
            assert_eq!(compiled(&params, fork, &candidate), before - saving);
        }
    }
}

#[test]
fn seeded_fused_replays_fixed_legacy_bodies() {
    use crate::huff::schedule::{DEFAULT_OPTIONS, FusedTree};
    for name in ["paris", "shanghai", "cancun", "prague", "osaka"] {
        let fork = fork(name).unwrap();
        for t in [24, 28] {
            let params = generate_params(t);
            let inputs = test_inputs(t);
            let range = Range {
                from: 0,
                to: step_count(&params),
            };
            let opts = BuildOptions {
                external_d: true,
                prime_under_external: false,
                internal_consume: true,
                prime_stack: true,
                shadow: true,
                shared_body: true,
                consume_group: if t == 24 { 6 } else { 3 },
                consume_slots: if t == 24 { 14 } else { 13 },
                external_template: true,
                prime_in_memory: t == 24,
                external_stream: true,
                compact_inputs: true,
                tree_sums: true,
                tree_peak: true,
                tree_adaptive_prime: t == 24,
                fused_tree: if t == 24 {
                    FusedTree::PreplacedBounded
                } else {
                    FusedTree::Preplaced
                },
                ..DEFAULT_OPTIONS
            };
            let result = build_permutation(&params, &inputs, &opts, fork, range, true).unwrap();
            let baseline = Best { opts, result };
            let before = compiled(&params, fork, &baseline);
            assert_eq!(
                before,
                match (name, t) {
                    ("paris", 24) => 75522,
                    ("paris", 28) => 90960,
                    (_, 24) => 75348,
                    (_, 28) => 90780,
                    _ => unreachable!(),
                }
            );
            let opts = BuildOptions {
                fused_tree: FusedTree::PreplacedSeeded,
                ..opts
            };
            let result = build_permutation(&params, &inputs, &opts, fork, range, true).unwrap();
            let model = build_permutation(&params, &inputs, &opts, fork, range, false).unwrap();
            assert_eq!(
                (result.gas, result.bytes, result.memory),
                (model.gas, model.bytes, model.memory)
            );
            assert_eq!(result.loads, baseline.result.loads);
            assert_eq!(result.stores, baseline.result.stores);
            assert_eq!(result.max_depth, baseline.result.max_depth);
            assert!(result.max_depth <= 1000);
            assert!(runtime_bytes(&params, fork, &result) <= fork.code_size);
            assert_eq!(
                runtime_bytes(&params, fork, &result),
                match (name, t) {
                    ("paris", 24) => 23771,
                    ("paris", 28) => 24424,
                    (_, 24) => 23720,
                    (_, 28) => 24391,
                    _ => unreachable!(),
                }
            );
            let candidate = Best { opts, result };
            assert_eq!(
                compiled(&params, fork, &candidate),
                before - if t == 24 { 280 } else { 8 }
            );
        }
    }
}

#[test]
#[ignore = "forced streaming fused-sum experiment"]
fn streaming_fused_candidates() {
    use crate::huff::schedule::FusedTree;
    let t: usize = std::env::var("GRID_WIDTH")
        .unwrap_or_else(|_| "28".into())
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
        "FUSED_BASELINE {name} t{t} gas {baseline_gas} bytes {} opts {}",
        runtime_bytes(&params, fork, &baseline.result),
        describe_options(&baseline.opts)
    );
    let body_inline = std::env::var("FUSED_INLINE")
        .map(|v| v.parse::<usize>().unwrap())
        .unwrap_or(baseline.opts.body_inline);
    assert!(body_inline <= steady_rounds(&params, range).1);
    println!("FUSED_INLINE {body_inline}");
    let cap = std::env::var("FUSED_CAP").unwrap_or_else(|_| "word".into());
    let modes = match cap.as_str() {
        "word" => vec![FusedTree::Preplaced, FusedTree::Late],
        "serial" => vec![FusedTree::PreplacedBounded, FusedTree::LateBounded],
        "seeded" => vec![FusedTree::PreplacedSeeded],
        _ => panic!("FUSED_CAP must be word, serial or seeded"),
    };
    println!("FUSED_CAP {cap}");
    for fused_tree in modes {
        let opts = BuildOptions {
            fused_tree,
            body_inline,
            ..baseline.opts
        };
        let result = match build_permutation(&params, &inputs, &opts, fork, range, true) {
            Ok(result) => result,
            Err(err) => {
                println!("FUSED_FAILURE {name} t{t} {fused_tree:?}: {err}");
                continue;
            }
        };
        let gas = super::super::entry_gas(&fork, t, &result);
        let bytes = runtime_bytes(&params, fork, &result);
        if bytes > fork.code_size || result.max_depth > 1000 {
            println!(
                "FUSED_OVERSIZE {name} t{t} {fused_tree:?}: model gas {gas}, bytes {bytes}, depth {}",
                result.max_depth
            );
            continue;
        }
        let candidate = Best { opts, result };
        assert_eq!(compiled(&params, fork, &candidate), gas);
        println!(
            "FUSED_COMPILED {name} t{t} {fused_tree:?} gas {gas} saving {} bytes {bytes} depth {} loads {} stores {}",
            baseline_gas as i64 - gas as i64,
            candidate.result.max_depth,
            candidate.result.loads,
            candidate.result.stores
        );
    }
    println!("FUSED_DONE {name} t{t}");
}
