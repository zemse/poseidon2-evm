use super::*;
use crate::field;
use crate::huff::fork::fork;
use crate::huff::sum_tree;
use crate::round_constants::generate_params;
use crate::vectors::test_inputs;

#[test]
fn streamed_fused_trees_preserve_outputs_slots_and_caller_tail() {
    let params = generate_params(16);
    let mut bounds = vec![UINT256_MAX; params.t];
    bounds[0] = p1();
    let inputs = vec![
        vec![U256::ZERO; params.t],
        vec![p1(); params.t],
        bounds.clone(),
        bounds.iter().map(|&v| v / u256(2)).collect(),
    ];
    let boundary = Boundary {
        bounds: Some(bounds),
        ..Boundary::default()
    };
    for name in [
        "paris",
        "shanghai",
        "cancun",
        "prague",
        "osaka",
        "amsterdam",
    ] {
        for mem in FUSE_MIN..=14 {
            for late in [false, true] {
                for bounded in [false, true] {
                    for deep_prime in [false, true] {
                        let opts = BuildOptions {
                            prime_in_memory: deep_prime,
                            ..DEFAULT_OPTIONS
                        };
                        let mut b = Builder::new(
                            &params,
                            &inputs,
                            opts,
                            fork(name).unwrap(),
                            Range {
                                from: 0,
                                to: step_count(&params),
                            },
                            HashSet::new(),
                            false,
                            true,
                            &boundary,
                        )
                        .unwrap();
                        let old = b.state.clone();
                        let sum = old[0];
                        if deep_prime {
                            let slot = b.e.slot_base - 32;
                            b.e.mstore_const(PRIME, slot).unwrap();
                            b.e.prime_slot = Some(slot);
                        }
                        let mut tail = vec![sum];
                        if deep_prime {
                            tail.extend(vec![old[15]; 15]);
                        }
                        tail.push(b.p());
                        b.e.set_stack(&tail);
                        let slots: Vec<_> = old[1..=mem]
                            .iter()
                            .enumerate()
                            .map(|(i, &s)| {
                                b.e.last_load.insert(Key::In(i + 1), 1);
                                b.e.declare(s)
                            })
                            .collect();
                        let leaf_bound = p1() * u256(2);
                        let cap = if bounded {
                            (1..mem)
                                .fold(leaf_bound, |a, _| a.checked_add(leaf_bound).unwrap_or(p1()))
                        } else {
                            UINT256_MAX
                        };
                        let leaf_bounds = vec![leaf_bound; mem];
                        let plan = if late {
                            sum_tree::plan_late(&leaf_bounds, cap, true)
                        } else {
                            sum_tree::plan_peak(&leaf_bounds, cap)
                        }
                        .unwrap();
                        let mut out = vec![0; params.t];
                        let stores = b.e.stores;
                        let acc = b.emit_fused_tree(&plan, &old, sum, &mut out).unwrap();
                        assert_eq!(b.e.bound(acc), plan.bound);
                        assert!(b.e.bound(acc) <= cap);
                        assert_eq!(b.e.stores - stores, mem);
                        assert_eq!(&b.e.from_top()[1..], tail);
                        assert!(b.e.max_dup <= b.e.max_reach);
                        for (i, &slot) in (1..=mem).zip(&slots) {
                            assert_eq!(b.e.slot_of(out[i]), Some(slot));
                            assert_eq!(b.e.slot_of(old[i]), None);
                            assert_eq!(b.e.bound(out[i]), leaf_bound);
                            b.e.dup(out[i]).unwrap();
                            b.e.pop().unwrap();
                        }
                        for (k, input) in inputs.iter().enumerate() {
                            let mut expected = U256::ZERO;
                            for i in 1..=mem {
                                let output =
                                    field::mul(input[i], params.internal_diag_minus_one[i])
                                        + input[0];
                                assert_eq!(b.e.value(out[i]).vals[k], output);
                                expected = field::add(expected, output);
                            }
                            assert_eq!(field::reduce(b.e.value(acc).vals[k]), expected);
                        }
                        b.e.spill_at(acc, None).unwrap();
                        assert_eq!(b.e.from_top(), tail);
                    }
                }
            }
        }
    }
}

#[test]
fn seeded_fused_trees_preserve_bounds_slots_and_caller_tail() {
    let params = generate_params(16);
    let leaf_bound = p1() * u256(2);
    let inputs = vec![
        vec![U256::ZERO; params.t],
        vec![p1(); params.t],
        vec![leaf_bound; params.t],
        (0..params.t)
            .map(|i| leaf_bound / u256(i as u64 + 1))
            .collect(),
    ];
    let boundary = Boundary {
        bounds: Some(vec![leaf_bound; params.t]),
        ..Boundary::default()
    };
    for name in [
        "paris",
        "shanghai",
        "cancun",
        "prague",
        "osaka",
        "amsterdam",
    ] {
        let fork = fork(name).unwrap();
        for mem in FUSE_MIN..=14 {
            for peak in [false, true] {
                for supply in 0..3 {
                    let opts = BuildOptions {
                        tree_peak: peak,
                        prime_in_memory: supply == 2,
                        fused_tree: FusedTree::PreplacedSeeded,
                        ..DEFAULT_OPTIONS
                    };
                    let mut b = Builder::new(
                        &params,
                        &inputs,
                        opts,
                        fork,
                        Range {
                            from: 0,
                            to: step_count(&params),
                        },
                        HashSet::new(),
                        false,
                        true,
                        &boundary,
                    )
                    .unwrap();
                    let values = b.state[1..=mem].to_vec();
                    if supply == 2 {
                        let slot = b.e.slot_base - 32;
                        b.e.mstore_const(PRIME, slot).unwrap();
                        b.e.prime_slot = Some(slot);
                    }
                    let mut tail = vec![b.state[15]];
                    if supply > 0 {
                        tail.extend(vec![b.state[15]; fork.reach]);
                    }
                    tail.push(b.p());
                    b.e.set_stack(&tail);
                    let slots: Vec<_> = values
                        .iter()
                        .enumerate()
                        .map(|(i, &v)| {
                            b.e.last_load.insert(Key::In(i + 1), 3);
                            b.e.declare(v)
                        })
                        .collect();
                    let bounds = vec![leaf_bound; mem];
                    let plan = if peak {
                        sum_tree::plan_peak(&bounds, UINT256_MAX)
                    } else {
                        sum_tree::plan(&bounds, UINT256_MAX)
                    }
                    .unwrap();
                    let stores = b.e.stores;
                    let acc = b.seed_fused_tree(&values).unwrap();
                    assert_eq!(b.e.bound(acc), plan.bound);
                    assert_eq!(b.e.stores, stores);
                    assert_eq!(&b.e.from_top()[1..], tail);
                    assert!(b.e.max_dup <= fork.reach);
                    for (&v, &slot) in values.iter().zip(&slots) {
                        assert_eq!(b.e.slot_of(v), Some(slot));
                        assert_eq!(b.e.bound(v), leaf_bound);
                        b.e.dup(v).unwrap();
                        b.e.pop().unwrap();
                    }
                    for (k, input) in inputs.iter().enumerate() {
                        let expected = input[1..=mem].iter().copied().fold(U256::ZERO, field::add);
                        assert_eq!(field::reduce(b.e.value(acc).vals[k]), expected);
                    }
                    b.e.spill(acc).unwrap();
                    assert_eq!(b.e.from_top(), tail);
                    for (&v, &slot) in values.iter().zip(&slots) {
                        assert_eq!(b.e.slot_of(v), Some(slot));
                        assert_ne!(b.e.slot_of(acc), Some(slot));
                        b.e.dup(v).unwrap();
                        b.e.pop().unwrap();
                        assert_eq!(b.e.slot_of(v), None);
                    }
                    assert_eq!(b.e.from_top(), tail);
                }
            }
        }
    }
}

#[test]
fn fused_alternatives_require_a_fusable_memory_region() {
    let opts = BuildOptions {
        internal_consume: true,
        prime_stack: true,
        consume_slots: 14,
        ..DEFAULT_OPTIONS
    };
    assert_eq!(DEFAULT_OPTIONS.fused_tree, FusedTree::Serial);
    for name in ["paris", "osaka", "amsterdam"] {
        let reach = fork(name).unwrap().reach;
        for t in [2, 3, 4, 8, 12, 16, 20] {
            assert!(fused_candidates(t, reach, opts).is_empty());
        }
        for t in [24, 28] {
            let modes = fused_candidates(t, reach, opts);
            assert_eq!(modes.len(), 4);
            for mode in modes {
                assert_ne!(mode.fused_tree, FusedTree::Serial);
                assert_eq!(
                    BuildOptions {
                        fused_tree: FusedTree::Serial,
                        ..mode
                    },
                    opts
                );
            }
            if reach > 16 {
                assert!(
                    fused_candidates(
                        t,
                        reach,
                        BuildOptions {
                            consume_slots: 0,
                            ..opts
                        }
                    )
                    .is_empty()
                );
            }
        }
    }
    for off in [
        BuildOptions {
            internal_consume: false,
            ..opts
        },
        BuildOptions {
            prime_stack: false,
            ..opts
        },
    ] {
        assert!(fused_candidates(28, 16, off).is_empty());
    }
}

#[test]
fn fused_modes_do_not_change_below_threshold_bodies() {
    for name in ["paris", "osaka"] {
        let fork = fork(name).unwrap();
        for t in [16, 20] {
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
                body_inline: if t == 16 { 2 } else { 1 },
                consume_group: if t == 16 { 0 } else { 7 },
                consume_slots: 14,
                external_template: true,
                external_stream: true,
                tree_sums: true,
                tree_adaptive_prime: true,
                ..DEFAULT_OPTIONS
            };
            let serial = build_permutation(&params, &inputs, &opts, fork, range, true).unwrap();
            for fused_tree in [
                FusedTree::Preplaced,
                FusedTree::PreplacedBounded,
                FusedTree::Late,
                FusedTree::LateBounded,
                FusedTree::PreplacedSeeded,
            ] {
                let candidate = build_permutation(
                    &params,
                    &inputs,
                    &BuildOptions { fused_tree, ..opts },
                    fork,
                    range,
                    true,
                )
                .unwrap();
                assert_eq!(candidate.lines, serial.lines);
                assert_eq!(
                    (candidate.gas, candidate.bytes, candidate.memory),
                    (serial.gas, serial.bytes, serial.memory)
                );
            }
        }
    }
}

#[test]
fn streamed_fused_leaf_rejects_an_unsafe_output_bound() {
    let params = generate_params(8);
    let boundary = Boundary {
        bounds: Some(vec![UINT256_MAX; params.t]),
        ..Boundary::default()
    };
    let mut b = Builder::new(
        &params,
        &[vec![U256::ZERO; params.t]],
        DEFAULT_OPTIONS,
        fork("osaka").unwrap(),
        Range {
            from: 0,
            to: step_count(&params),
        },
        HashSet::new(),
        false,
        false,
        &boundary,
    )
    .unwrap();
    let old = b.state.clone();
    let plan = sum_tree::plan_peak(&[p1() * u256(2)], UINT256_MAX).unwrap();
    assert!(
        b.emit_fused_tree(&plan, &old, old[0], &mut vec![0; params.t])
            .is_err()
    );
}
