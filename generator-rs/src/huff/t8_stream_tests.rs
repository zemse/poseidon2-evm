use super::*;
use crate::field;
use crate::huff::fork::fork;
use crate::round_constants::generate_params_uncached;
use crate::value::Value;

#[test]
fn t8_kept_lane_fit_matches_replay() {
    let params = generate_params_uncached(8);
    let inputs = vec![vec![U256::ZERO; 8], vec![p1(); 8]];
    let program = "lane=z0 dup15";
    let mut mismatches = 0;
    for name in ["paris", "osaka", "amsterdam"] {
        for kept in [false, true] {
            let fork = fork(name).unwrap();
            let mut b = Builder::new(
                &params,
                &inputs,
                DEFAULT_OPTIONS,
                fork,
                Range {
                    from: 0,
                    to: step_count(&params),
                },
                HashSet::new(),
                false,
                true,
                &Boundary::default(),
            )
            .unwrap();
            let tail: Vec<Id> = (0..14)
                .map(|i| {
                    b.e.alloc(
                        Value::new(
                            format!("caller{i}"),
                            UINT256_MAX,
                            vec![UINT256_MAX - u256(i); inputs.len()],
                            None,
                        )
                        .unwrap(),
                    )
                })
                .collect();
            let mut stack = vec![b.state[0], b.p()];
            stack.extend_from_slice(&tail);
            b.e.set_stack(&stack);
            let state = b.state.clone();
            let sums = [b.p(); 4];
            let predicted = b.stream_block_fits(program, 0, &state, &sums, kept);
            let mut out = vec![0; 8];
            let result = b.stream_block(program, 0, &state, &sums, Some(0), kept, &mut out);
            let replayed = result.is_ok();
            assert_eq!(replayed, kept, "{name} kept={kept}: {result:?}");
            if kept {
                assert_eq!(b.e.top(0).unwrap(), tail[13]);
                assert_eq!(b.e.top(1).unwrap(), out[0]);
                assert_eq!(&b.e.from_top()[2..], tail);
                assert_eq!(b.e.bound(out[0]), p1());
                assert_eq!((b.e.memory, b.e.loads, b.e.stores, b.e.pops), (0, 0, 0, 0));
                for (i, input) in inputs.iter().enumerate() {
                    let y = field::add(input[0], params.round_constants[0][0]);
                    let y2 = field::mul(y, y);
                    let expected = field::mul(field::mul(y2, y2), y);
                    assert_eq!(b.e.value(out[0]).vals[i], expected);
                }
            } else {
                assert!(result.unwrap_err().to_string().contains("stack underflow"));
            }
            println!(
                "t8 kept-lane fit {name} kept={kept}: predicted={predicted}, replayed={replayed}"
            );
            mismatches += usize::from(predicted != replayed);
        }
    }
    assert_eq!(mismatches, 0, "kept-lane fit must agree with replay");
}

fn builder<'a>(
    params: &'a Params,
    inputs: &[Vec<U256>],
    fork: Fork,
    bounds: Vec<U256>,
) -> Builder<'a> {
    Builder::new(
        params,
        inputs,
        DEFAULT_OPTIONS,
        fork,
        Range {
            from: 0,
            to: step_count(params),
        },
        HashSet::new(),
        false,
        true,
        &Boundary {
            bounds: Some(bounds),
            ..Boundary::default()
        },
    )
    .unwrap()
}

fn sentinels(b: &mut Builder<'_>, count: usize) -> Vec<Id> {
    (0..count)
        .map(|i| {
            b.e.alloc(
                Value::new(
                    format!("caller{i}"),
                    UINT256_MAX,
                    vec![UINT256_MAX - U256::from(i); b.vectors],
                    None,
                )
                .unwrap(),
            )
        })
        .collect()
}

#[test]
fn t8_stream_fit_reach_and_underflow() {
    let params = generate_params_uncached(8);
    let inputs = vec![vec![U256::ZERO; 8]];
    for name in ["paris", "osaka", "amsterdam"] {
        let fork = fork(name).unwrap();
        for kept in [false, true] {
            for (suffix, tail_len, accepted) in [
                (format!("dup{}", fork.reach), fork.reach, true),
                (format!("dup{}", fork.reach + 1), fork.reach + 1, false),
                (format!("swap{}", fork.reach), fork.reach, kept),
                (format!("swap{}", fork.reach + 1), fork.reach + 2, false),
                ("dup2".into(), 0, false),
                ("swap1".into(), 0, false),
                ("pop".into(), 0, kept),
                ("pop pop".into(), 0, false),
            ] {
                let mut b = builder(&params, &inputs, fork, vec![p1(); 8]);
                let tail = sentinels(&mut b, tail_len);
                let mut stack = vec![b.state[0], b.p()];
                stack.extend_from_slice(&tail);
                b.e.set_stack(&stack);
                let state = b.state.clone();
                let sums = [b.p(); 4];
                let program = format!("lane=z0 {suffix}");
                let predicted = b.stream_block_fits(&program, 0, &state, &sums, kept);
                let mut out = vec![0; 8];
                let result = b.stream_block(&program, 0, &state, &sums, Some(0), kept, &mut out);
                assert_eq!(predicted, accepted, "{name} kept={kept} {program}");
                assert_eq!(
                    predicted,
                    result.is_ok(),
                    "{name} kept={kept} {program}: {result:?}"
                );
                if accepted {
                    assert!(b.e.max_dup <= fork.reach);
                }
            }
            for stack_len in 0..2 {
                let mut b = builder(&params, &inputs, fork, vec![p1(); 8]);
                let stack = [b.state[0], b.p()];
                b.e.set_stack(&stack[..stack_len]);
                let state = b.state.clone();
                let sums = [b.p(); 4];
                assert!(!b.stream_block_fits("lane=z0", 0, &state, &sums, kept));
                assert!(
                    b.stream_block("lane=z0", 0, &state, &sums, Some(0), kept, &mut [0; 8])
                        .is_err()
                );
            }
        }
    }
}

#[test]
fn t8_stream_programs_fit_and_replay() {
    let params = generate_params_uncached(8);
    let mut inputs = crate::vectors::test_inputs(8);
    inputs.push(vec![p1(); 8]);
    let expected: Vec<Vec<U256>> = inputs
        .iter()
        .map(|input| permutation_steps(&params, input, 0, 1))
        .collect();
    for name in ["paris", "osaka", "amsterdam"] {
        let fork = fork(name).unwrap();
        for block in 0..2 {
            for on_stack in [false, true] {
                for kept in [false, true] {
                    for &program in stream_blocks(kept, on_stack) {
                        let mut b = builder(&params, &inputs, fork, vec![p1(); 8]);
                        let state = b.state.clone();
                        if !on_stack {
                            for &id in &state[4 * block..4 * block + 4] {
                                b.e.dup(id).unwrap();
                                b.e.spill(id).unwrap();
                            }
                        }
                        let sums: [Id; 4] = std::array::from_fn(|i| {
                            b.e.alloc(
                                Value::new(
                                    format!("S{i}"),
                                    p1(),
                                    inputs
                                        .iter()
                                        .map(|input| field::add(input[i], input[i + 4]))
                                        .collect(),
                                    None,
                                )
                                .unwrap(),
                            )
                        });
                        let tail = sentinels(&mut b, 3);
                        let mut stack = sums.to_vec();
                        stack.push(b.p());
                        if on_stack {
                            stack.extend_from_slice(&state[4 * block..4 * block + 4]);
                        }
                        stack.extend_from_slice(&tail);
                        b.e.set_stack(&stack);
                        let predicted = b.stream_block_fits(program, block, &state, &sums, kept);
                        let mut out = vec![0; 8];
                        let result =
                            b.stream_block(program, block, &state, &sums, Some(0), kept, &mut out);
                        assert_eq!(
                            predicted,
                            result.is_ok(),
                            "{name} block={block} kept={kept} on_stack={on_stack}: {result:?}"
                        );
                        assert!(
                            predicted,
                            "{name} block={block} kept={kept} on_stack={on_stack}"
                        );
                        let top = b.e.from_top();
                        assert_eq!(&top[if kept { 4 } else { 0 }..], stack);
                        for (i, &id) in out[4 * block..4 * block + 4].iter().enumerate() {
                            assert_eq!(b.e.find(id) > 0, kept);
                            assert!(b.e.reachable(id));
                            assert_eq!(b.e.bound(id), p1());
                            let lane = 4 * block + i;
                            for (k, expected) in expected.iter().enumerate() {
                                let y = field::add(expected[lane], params.round_constants[0][lane]);
                                let y2 = field::mul(y, y);
                                assert_eq!(
                                    b.e.value(id).vals[k],
                                    field::mul(field::mul(y2, y2), y)
                                );
                            }
                        }
                        assert!(b.e.max_dup <= fork.reach);
                    }
                }
            }
        }
    }
}

const TAKE_SUM_PREFIX: &str = "u3 u2 dup2 add=t1 P P u1 P dup2 dup1 add=d1 dup6 addmod=t2";
const TAKE_SUM_SUFFIX: &str = "add=t0 dup5 P dup3 q=q0 dup12 add=o1 swap6 add=d3 addmod=t3 P P P dup7 lane=z1 swap5 q=q1 dup3 add=o3 P dup2 lane=z3 swap11 add=o2 lane=z2 swap4 add=o0 lane=z0";

#[test]
fn t8_kept_last_sum_lifetime() {
    let params = generate_params_uncached(8);
    let mut inputs = crate::vectors::test_inputs(8);
    inputs.push(vec![p1(); 8]);
    let expected: Vec<Vec<U256>> = inputs
        .iter()
        .map(|input| permutation_steps(&params, input, 0, 1))
        .collect();
    let half = params.rounds_f / 2;
    let partial_end = half + params.rounds_p;
    for round in (0..half).chain(partial_end + 1..params.rounds_f + params.rounds_p) {
        for take_sum in [false, true] {
            let fork = fork("amsterdam").unwrap();
            let mut b = builder(&params, &inputs, fork, vec![p1(); 8]);
            let state = b.state.clone();
            let sums: [Id; 4] = std::array::from_fn(|i| {
                b.e.alloc(
                    Value::new(
                        format!("S{i}"),
                        p1(),
                        inputs
                            .iter()
                            .map(|input| field::add(input[i], input[i + 4]))
                            .collect(),
                        None,
                    )
                    .unwrap(),
                )
            });
            let previous = sentinels(&mut b, 4);
            let tail = sentinels(&mut b, 3);
            let mut stack = previous.clone();
            stack.extend_from_slice(&sums);
            stack.push(b.p());
            stack.extend_from_slice(&state[..4]);
            stack.extend_from_slice(&tail);
            b.e.set_stack(&stack);
            let before = b.e.gas;
            let mut out = vec![0; 8];
            if take_sum {
                assert_eq!(
                    last_stream_block8(),
                    format!("{TAKE_SUM_PREFIX} take0 {TAKE_SUM_SUFFIX}")
                );
                assert!(b.stream_block_fits(last_stream_block8(), 0, &state, &sums, true));
                b.stream_block(
                    last_stream_block8(),
                    0,
                    &state,
                    &sums,
                    Some(round),
                    true,
                    &mut out,
                )
                .unwrap();
            } else {
                b.stream_block(
                    stream_blocks(true, true)[0],
                    0,
                    &state,
                    &sums,
                    Some(round),
                    true,
                    &mut out,
                )
                .unwrap();
            }
            let mut layout = out[..3].to_vec();
            if take_sum {
                layout.extend_from_slice(&previous);
                layout.push(out[3]);
                layout.extend_from_slice(&stack[5..]);
            } else {
                layout.push(out[3]);
                layout.extend_from_slice(&stack);
            }
            assert_eq!(b.e.from_top(), layout);
            assert_eq!(b.e.gas - before, if take_sum { 344 } else { 347 });
            assert_eq!((b.e.memory, b.e.loads, b.e.stores, b.e.pops), (0, 0, 0, 0));
            for (lane, &id) in out[..4].iter().enumerate() {
                assert_eq!(b.e.bound(id), p1());
                for (i, expected) in expected.iter().enumerate() {
                    let y = field::add(expected[lane], params.round_constants[round][lane]);
                    let y2 = field::mul(y, y);
                    assert_eq!(b.e.value(id).vals[i], field::mul(field::mul(y2, y2), y));
                }
            }
            assert!(b.e.max_dup <= fork.reach);
            println!(
                "T8_TAKE_SUM round={round} take_sum={take_sum} gas={} reach={}",
                b.e.gas - before,
                b.e.max_dup
            );
        }
    }
}

#[test]
fn t8_take_sum_reach_and_bounds() {
    let params = generate_params_uncached(8);
    let inputs = vec![vec![U256::ZERO; 8]];
    for name in ["paris", "osaka", "amsterdam"] {
        let fork = fork(name).unwrap();
        for (sum_depth, input_depth, accepted) in [
            (0, 2, false),
            (1, 2, false),
            (2, fork.reach, true),
            (2, fork.reach + 1, false),
            (fork.reach + 1, 2, true),
            (fork.reach + 2, 2, false),
        ] {
            let mut b = builder(&params, &inputs, fork, vec![p1(); 8]);
            let state = b.state.clone();
            let sum =
                b.e.alloc(Value::new("S0".into(), p1(), vec![U256::ZERO], None).unwrap());
            let mut stack = sentinels(&mut b, fork.reach + 2);
            stack[input_depth - 1] = state[0];
            if sum_depth > 0 {
                stack[sum_depth - 1] = sum;
            }
            b.e.set_stack(&stack);
            let sums = [sum; 4];
            assert_eq!(
                b.stream_block_fits("take0", 0, &state, &sums, true),
                accepted
            );
            let result = b.stream_block("take0", 0, &state, &sums, Some(0), true, &mut [0; 8]);
            assert_eq!(
                result.is_ok(),
                accepted,
                "{name} sum={sum_depth} input={input_depth}: {result:?}"
            );
            if accepted {
                let id = b.e.top(0).unwrap();
                stack.swap(0, sum_depth - 1);
                stack[0] = id;
                assert_eq!(b.e.from_top(), stack);
                assert_eq!(b.e.bound(id), p1() + p1());
                assert_eq!(b.e.value(id).vals, [U256::ZERO]);
            }
        }
        for excess in [false, true] {
            let mut bounds = vec![p1(); 8];
            bounds[0] = UINT256_MAX - p1() + u256(u64::from(excess));
            let mut b = builder(&params, &inputs, fork, bounds);
            let state = b.state.clone();
            let sum =
                b.e.alloc(Value::new("S0".into(), p1(), vec![U256::ZERO], None).unwrap());
            let tail = sentinels(&mut b, 2);
            b.e.set_stack(&[tail[0], sum, state[0], tail[1]]);
            let sums = [sum; 4];
            assert!(b.stream_block_fits("take0", 0, &state, &sums, true));
            let result = b.stream_block("take0", 0, &state, &sums, Some(0), true, &mut [0; 8]);
            assert_eq!(
                result.is_ok(),
                !excess,
                "{name} excess={excess}: {result:?}"
            );
            if !excess {
                assert_eq!(b.e.bound(b.e.top(0).unwrap()), UINT256_MAX);
                assert_eq!(&b.e.from_top()[1..], [tail[0], state[0], tail[1]]);
            }
        }
    }
}

#[test]
fn t8_last_sum_stream_paths() {
    let params = generate_params_uncached(8);
    let mut inputs = crate::vectors::test_inputs(8);
    inputs.push(vec![p1(); 8]);
    for (tree_sums, shadow, shared_body, prime_in_memory, loaded) in [
        (true, false, false, false, false),
        (false, false, false, false, false),
        (true, true, true, true, false),
        (false, true, false, true, true),
    ] {
        let fork = fork("amsterdam").unwrap();
        let opts = BuildOptions {
            external_d: true,
            external_stream: true,
            internal_consume: true,
            prime_stack: true,
            tree_sums,
            shadow,
            shared_body,
            prime_in_memory,
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
            &Boundary::default(),
        )
        .unwrap();
        let tail = sentinels(&mut b, 3);
        let mut stack = b.e.from_top();
        if loaded {
            for &id in &b.state[..4] {
                b.e.dup(id).unwrap();
                b.e.spill(id).unwrap();
            }
            stack.drain(..4);
        }
        stack.extend_from_slice(&tail);
        b.e.set_stack(&stack);
        let out = b.build().unwrap();
        let final_stack = b.e.from_top();
        assert_eq!(&final_stack[final_stack.len() - tail.len()..], tail);
        for (i, input) in inputs.iter().enumerate() {
            let expected = permutation_steps(&params, input, 0, step_count(&params));
            for (&id, expected) in out.iter().zip(expected) {
                assert_eq!(b.e.value(id).vals[i], expected);
                assert_eq!(b.e.bound(id), p1());
            }
        }
        assert!(b.e.max_dup <= fork.reach);
        assert!(b.e.max_depth <= 1000);
        assert_eq!(b.step_bytes.len(), step_count(&params));
        assert!(b.step_bytes.windows(2).all(|pair| pair[0] <= pair[1]));
        println!(
            "T8_STREAM_PATH tree={tree_sums} shadow={shadow} shared={shared_body} prime_memory={prime_in_memory} loaded={loaded} gas={}",
            b.e.gas
        );
    }
}

#[test]
fn t8_stream_lane_inclusive_bounds_and_prime_guard() {
    let params = generate_params_uncached(8);
    let limit = UINT256_MAX - params.round_constants[0][0];
    for name in ["paris", "osaka", "amsterdam"] {
        let fork = fork(name).unwrap();
        for kept in [false, true] {
            for excess in [false, true] {
                let bound = limit + u256(u64::from(excess));
                let mut inputs = vec![vec![U256::ZERO; 8]; 2];
                inputs[1][0] = if excess { U256::ZERO } else { limit };
                let mut bounds = vec![p1(); 8];
                bounds[0] = bound;
                let mut b = builder(&params, &inputs, fork, bounds);
                let state = b.state.clone();
                let tail = sentinels(&mut b, 3);
                let mut stack = vec![state[0], b.p()];
                stack.extend_from_slice(&tail);
                b.e.set_stack(&stack);
                let sums = [b.p(); 4];
                // Shape eligibility does not bypass checked arithmetic replay.
                assert!(b.stream_block_fits("lane=z0", 0, &state, &sums, kept));
                let mut out = [0; 8];
                let result = b.stream_block("lane=z0", 0, &state, &sums, Some(0), kept, &mut out);
                assert_eq!(result.is_ok(), !excess, "{name} kept={kept}: {result:?}");
                if excess {
                    assert!(result.unwrap_err().to_string().contains("overflows"));
                    assert_eq!(b.e.from_top(), stack);
                } else {
                    assert_eq!(&b.e.from_top()[usize::from(kept)..], tail);
                    assert_eq!(b.e.bound(out[0]), p1());
                    for (i, input) in inputs.iter().enumerate() {
                        let y = field::add(input[0], params.round_constants[0][0]);
                        let y2 = field::mul(y, y);
                        assert_eq!(b.e.value(out[0]).vals[i], field::mul(field::mul(y2, y2), y));
                    }
                }
            }
            for wrong_prime in [false, true] {
                let inputs = vec![vec![U256::ZERO; 8]];
                let mut b = builder(&params, &inputs, fork, vec![p1(); 8]);
                let p = if wrong_prime {
                    b.e.alloc(
                        Value::new("not_prime".to_string(), PRIME, vec![PRIME], None).unwrap(),
                    )
                } else {
                    b.p()
                };
                let state = b.state.clone();
                let stack = [state[0], p];
                b.e.set_stack(&stack);
                let sums = [b.p(); 4];
                assert!(b.stream_block_fits("lane=z0", 0, &state, &sums, kept));
                let r = if wrong_prime { Some(0) } else { None };
                let err = b
                    .stream_block("lane=z0", 0, &state, &sums, r, kept, &mut [0; 8])
                    .unwrap_err();
                assert!(err.to_string().contains(if wrong_prime {
                    "PRIME copy"
                } else {
                    "without a next round"
                }));
                assert_eq!(b.e.from_top(), stack);
            }
        }
    }
}
