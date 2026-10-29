use super::*;
use crate::field;
use crate::huff::fork::fork;
use crate::huff::sum_tree;
use crate::round_constants::generate_params;

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
