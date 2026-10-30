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
        (true, false, false, true, false),
        (true, false, true, false, false),
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

fn take_stream_input(b: &mut Builder<'_>, input: Id, sum: Id) -> Result<Id> {
    let state = b.state.clone();
    assert_eq!(state[4], input);
    let depth = b.e.find(input);
    let mut stack = b.e.from_top();
    let expected_fit = if depth >= 2 && depth - 1 <= b.e.max_reach {
        stack.swap(0, depth - 1);
        stack
            .iter()
            .position(|&v| v == sum)
            .is_some_and(|i| i < b.e.max_reach)
    } else {
        false
    };
    assert_eq!(
        b.stream_block_fits("takex0", 1, &state, &[sum; 4], true),
        expected_fit
    );
    b.stream_block("takex0", 1, &state, &[sum; 4], Some(0), true, &mut [0; 8])?;
    b.e.top(0)
}

#[test]
fn t8_input_last_use_selection_and_fallback() {
    let params = generate_params_uncached(8);
    let inputs = crate::vectors::test_inputs(8);
    for name in ["amsterdam", "osaka", "paris"] {
        for moved in [false, true] {
            let mut b = builder(&params, &inputs, fork(name).unwrap(), vec![p1(); 8]);
            b.opts.external_d = true;
            b.opts.external_stream = true;
            b.opts.tree_sums = true;
            let old = b.state.clone();
            let tail = sentinels(&mut b, 3);
            let mut stack = b.e.from_top();
            if moved {
                stack.swap(4, 5);
            }
            stack.extend_from_slice(&tail);
            b.e.set_stack(&stack);
            let before = b.e.gas;
            b.stream_linear(Some(0)).unwrap();
            let eligible = name == "amsterdam" && !moved;
            assert_eq!(b.e.gas - before, if eligible { 759 } else { 762 });
            assert_eq!(b.e.find(old[4]) == 0, eligible);
            let top = b.e.from_top();
            assert_eq!(&top[top.len() - tail.len()..], tail);
            for (i, input) in inputs.iter().enumerate() {
                let linear = permutation_steps(&params, input, 0, 1);
                for (lane, &id) in b.state.iter().enumerate() {
                    let y = field::add(linear[lane], params.round_constants[0][lane]);
                    let y2 = field::mul(y, y);
                    assert_eq!(b.e.value(id).vals[i], field::mul(field::mul(y2, y2), y));
                }
            }
        }
    }
}

fn input_last_use_pair(b: &mut Builder<'_>, round: usize, consume: bool) {
    let before = b.e.gas;
    let state = b.state.clone();
    let values: Vec<Vec<U256>> = (0..b.vectors)
        .map(|i| state.iter().map(|&v| b.e.value(v).vals[i]).collect())
        .collect();
    b.layers += 1;
    b.e.push_prime().unwrap();
    let mut sums = [0; 4];
    for i in (0..4).rev() {
        sums[i] = b
            .chain_sum_in_place(&[state[i], state[i + 4]], &format!("S{i}"), p1())
            .unwrap();
    }
    assert_eq!(b.e.gas - before, 71);
    let floor = b.e.from_top();
    let depth = b.e.find(state[4]);
    assert!(matches!(depth, 9 | 10));
    let mut out = [0; 8];
    let first = b.e.gas;
    if consume {
        let suffix = TAKE_SUM_SUFFIX
            .replace("dup12", &format!("dup{}", depth + 7))
            .replace("swap11", &format!("swap{}", depth + 6));
        let program = super::super::templates::first_stream_block8(depth).unwrap();
        assert_eq!(program, format!("{TAKE_SUM_PREFIX} takex0 {suffix}"));
        assert!(b.stream_block_fits(program, 1, &state, &sums, true));
        b.stream_block(program, 1, &state, &sums, Some(round), true, &mut out)
            .unwrap();
    } else {
        b.stream_block(
            stream_blocks(true, true)[0],
            1,
            &state,
            &sums,
            Some(round),
            true,
            &mut out,
        )
        .unwrap();
    }
    assert_eq!(b.e.gas - first, if consume { 344 } else { 347 });
    let mut first_layout = out[4..if consume { 7 } else { 8 }].to_vec();
    let mut first_floor = floor.clone();
    if consume {
        first_floor[depth - 1] = out[7];
        assert_eq!(b.e.find(state[4]), 0);
    }
    first_layout.extend_from_slice(&first_floor);
    assert_eq!(b.e.from_top(), first_layout);
    let sum_depth = if consume { 4 } else { 5 };
    assert_eq!(b.e.find(sums[0]), sum_depth);
    let last = b.e.gas;
    let program = if consume {
        let expected = last_stream_block8()
            .replace("dup12", "dup11")
            .replace("swap11", "swap10");
        let program = super::super::templates::last_stream_block8_after_input();
        assert_eq!(program, expected);
        program.to_string()
    } else {
        last_stream_block8().to_string()
    };
    assert!(b.stream_block_fits(&program, 0, &state, &sums, true));
    b.stream_block(&program, 0, &state, &sums, Some(round), true, &mut out)
        .unwrap();
    assert_eq!(b.e.gas - last, 344);
    let mut layout = out[..3].to_vec();
    first_layout[sum_depth - 1] = out[3];
    layout.extend_from_slice(&first_layout);
    assert_eq!(b.e.from_top(), layout);
    assert_eq!(b.e.find(sums[0]), 0);
    assert_eq!(b.e.gas - before, if consume { 759 } else { 762 });
    for (i, input) in values.iter().enumerate() {
        let linear = permutation_steps(b.params, input, 0, 1);
        for (lane, &v) in out.iter().enumerate() {
            let y = field::add(linear[lane], b.params.round_constants[round][lane]);
            let y2 = field::mul(y, y);
            assert_eq!(b.e.value(v).vals[i], field::mul(field::mul(y2, y2), y));
            assert_eq!(b.e.bound(v), p1());
        }
    }
    assert_eq!((b.e.memory, b.e.loads, b.e.stores, b.e.pops), (0, 0, 0, 0));
    b.state = out.to_vec();
    b.sboxed = true;
}

#[test]
fn t8_input_last_use_paired_lifetimes() {
    let params = generate_params_uncached(8);
    let mut inputs = crate::vectors::test_inputs(8);
    inputs.push(vec![p1(); 8]);
    let half = params.rounds_f / 2;
    let partial_end = half + params.rounds_p;
    for round in (0..half).chain(partial_end + 1..params.rounds_f + params.rounds_p) {
        for shape in 0..4 {
            for consume in [false, true] {
                let mut b = builder(&params, &inputs, fork("amsterdam").unwrap(), vec![p1(); 8]);
                let s = b.state.clone();
                let dead = sentinels(&mut b, 7);
                let tail = sentinels(&mut b, 3);
                let mut stack = match shape {
                    0 => [s.clone(), vec![b.p()]].concat(),
                    1 | 2 => {
                        let mut stack = vec![s[0], s[1], s[2], s[4], s[5], s[6], s[3]];
                        stack.extend_from_slice(&dead[..3]);
                        stack.push(b.p());
                        stack.extend_from_slice(&dead[3..if shape == 1 { 7 } else { 6 }]);
                        stack.push(s[7]);
                        stack
                    }
                    _ => [s.iter().rev().copied().collect(), vec![b.p()]].concat(),
                };
                stack.extend_from_slice(&tail);
                b.e.set_stack(&stack);
                b.e.max_depth = stack.len();
                input_last_use_pair(&mut b, round, consume);
                let top = b.e.from_top();
                assert_eq!(&top[top.len() - tail.len()..], tail);
                assert_eq!(b.e.max_depth, stack.len() + if consume { 20 } else { 21 });
                if consume {
                    assert_eq!(b.e.max_dup, [17, 21, 20, 22][shape]);
                }
            }
        }
    }
}

#[test]
fn t8_input_last_use_recurrence_and_adapters() {
    let params = generate_params_uncached(8);
    let mut inputs = crate::vectors::test_inputs(8);
    inputs.push(vec![p1(); 8]);
    for final_layer in [false, true] {
        let mut b = builder(&params, &inputs, fork("amsterdam").unwrap(), vec![p1(); 8]);
        b.opts.external_d = true;
        b.opts.external_stream = true;
        b.opts.external_template = true;
        b.opts.internal_consume = true;
        b.opts.prime_stack = true;
        b.opts.tree_sums = true;
        let tail = sentinels(&mut b, 3);
        let mut stack = b.e.from_top();
        stack.extend_from_slice(&tail);
        b.e.set_stack(&stack);
        input_last_use_pair(&mut b, 0, true);
        assert_eq!(b.e.find(b.state[7]), 16);
        input_last_use_pair(&mut b, 1, true);
        assert_eq!(b.e.find(b.state[7]), 15);
        let input: Vec<Vec<U256>> = (0..b.vectors)
            .map(|i| b.state.iter().map(|&v| b.e.value(v).vals[i]).collect())
            .collect();
        let before = b.e.gas;
        b.external_matrix(final_layer, !final_layer, false).unwrap();
        assert_eq!(b.e.gas - before, if final_layer { 436 } else { 378 });
        for (i, input) in input.iter().enumerate() {
            let expected = permutation_steps(&params, input, 0, 1);
            for (&id, expected) in b.state.iter().zip(expected) {
                assert_eq!(field::reduce(b.e.value(id).vals[i]), expected);
            }
        }
        let mut prefix = b.state.clone();
        if final_layer {
            assert_eq!(b.e.max_dup, 25);
            assert!(b.state.iter().all(|&s| b.e.bound(s) == p1()));
        } else {
            prefix.insert(1, b.p());
        }
        assert_eq!(&b.e.from_top()[..prefix.len()], prefix);
        if !final_layer {
            let before = b.e.gas;
            let x5 = b.round_start(4, None).unwrap();
            assert_eq!(b.e.gas - before, 45);
            assert_eq!(b.e.top(0).unwrap(), x5);
            assert_eq!(b.e.find_prime(), 9);
            let mut ready = vec![x5];
            ready.extend_from_slice(&b.state[1..]);
            ready.push(b.p());
            assert_eq!(&b.e.from_top()[..9], ready);
        }
        let top = b.e.from_top();
        assert_eq!(&top[top.len() - tail.len()..], tail);
    }
}

#[test]
fn t8_input_last_use_reach_and_bounds() {
    let params = generate_params_uncached(8);
    let inputs = vec![vec![U256::ZERO; 8]];
    for name in ["paris", "osaka", "amsterdam"] {
        let fork = fork(name).unwrap();
        for (input_depth, sum_depth, accepted) in [
            (0, 2, false),
            (1, 2, false),
            (2, 0, false),
            (2, fork.reach, true),
            (2, fork.reach + 1, false),
            (fork.reach + 1, 2, true),
            (fork.reach + 2, 2, false),
        ] {
            let mut b = builder(&params, &inputs, fork, vec![p1(); 8]);
            let input = b.state[4];
            let sum =
                b.e.alloc(Value::new("S0".into(), p1(), vec![U256::ZERO], None).unwrap());
            let mut stack = sentinels(&mut b, fork.reach + 2);
            if input_depth > 0 {
                stack[input_depth - 1] = input;
            }
            if sum_depth > 0 {
                stack[sum_depth - 1] = sum;
            }
            b.e.set_stack(&stack);
            let result = take_stream_input(&mut b, input, sum);
            assert_eq!(
                result.is_ok(),
                accepted,
                "{name} input={input_depth} sum={sum_depth}: {result:?}"
            );
            if accepted {
                stack.swap(0, input_depth - 1);
                stack[0] = result.unwrap();
                assert_eq!(b.e.from_top(), stack);
                assert_eq!(b.e.find(input), 0);
            }
        }
        for excess in [false, true] {
            let mut bounds = vec![p1(); 8];
            bounds[4] = UINT256_MAX - p1() + u256(u64::from(excess));
            let mut b = builder(&params, &inputs, fork, bounds);
            let input = b.state[4];
            let sum =
                b.e.alloc(Value::new("S0".into(), p1(), vec![U256::ZERO], None).unwrap());
            let tail = sentinels(&mut b, 2);
            b.e.set_stack(&[tail[0], input, sum, tail[1]]);
            let result = take_stream_input(&mut b, input, sum);
            assert_eq!(
                result.is_ok(),
                !excess,
                "{name} excess={excess}: {result:?}"
            );
            if !excess {
                assert_eq!(b.e.bound(result.unwrap()), UINT256_MAX);
                assert_eq!(&b.e.from_top()[1..], [tail[0], sum, tail[1]]);
            }
        }
    }
}

#[test]
fn t8_exit_prime_selection_and_configurations() {
    let params = generate_params_uncached(8);
    let mut inputs = crate::vectors::test_inputs(8);
    inputs.push(vec![p1(); 8]);
    assert_eq!(
        super::super::templates::exit_prime_block8(),
        ordered_blocks(BlockKind::Exit)[0].replacen("u1 u0 ", "u1 P take0 ", 1)
    );
    for case in 0..9 {
        let mut opts = BuildOptions {
            external_d: true,
            external_stream: true,
            external_template: true,
            internal_consume: true,
            prime_stack: true,
            tree_sums: true,
            ..DEFAULT_OPTIONS
        };
        match case {
            1 => opts.internal_consume = false,
            2 => opts.shadow = true,
            3 => opts.prime_in_memory = true,
            4 => opts.shared_body = true,
            5 => opts.consume_slots = 6,
            _ => {}
        }
        let range = Range {
            from: usize::from(case == 7),
            to: if case == 8 {
                params.rounds_f / 2 + 2
            } else {
                step_count(&params)
            },
        };
        let shadow = if case == 6 {
            HashSet::from([Key::In(0)])
        } else {
            HashSet::new()
        };
        let mut b = Builder::new(
            &params,
            &inputs,
            opts,
            fork("amsterdam").unwrap(),
            range,
            shadow,
            false,
            true,
            &Boundary {
                store_inputs: true,
                ..Boundary::default()
            },
        )
        .unwrap();
        if case == 6 {
            b.e.spill(b.state[0]).unwrap();
            assert_eq!(b.e.find(b.state[0]), 0);
            assert!(b.input_slots[0].is_some());
        }
        let tail = sentinels(&mut b, 3);
        let mut stack = b.e.from_top();
        stack.extend_from_slice(&tail);
        b.e.set_stack(&stack);
        let out = b.build().unwrap();
        let parked =
            b.e.lines
                .iter()
                .filter(|line| {
                    let ops = line.split_once("//").map_or(line.as_str(), |(ops, _)| ops);
                    ops.contains(" swap6 ") && ops.contains(" add dup2 add")
                })
                .count();
        assert_eq!(parked, usize::from(case == 0), "configuration {case}");
        if case == 6 {
            assert!(b.e.loads > 0 && b.e.memory > 0);
            assert!(b.e.lines.iter().any(|line| {
                line.split_once("//")
                    .is_some_and(|(ops, _)| ops.split_whitespace().any(|op| op == "mstore"))
            }));
        }
        for (i, input) in inputs.iter().enumerate() {
            let expected = permutation_steps(&params, input, range.from, range.to);
            for (&id, expected) in out.iter().zip(expected) {
                assert_eq!(
                    field::reduce(b.e.value(id).vals[i]),
                    expected,
                    "configuration {case}"
                );
                assert!(b.e.bound(id) <= handover_bound());
            }
        }
        let top = b.e.from_top();
        assert_eq!(&top[top.len() - tail.len()..], tail);
        assert!(b.e.max_dup <= b.e.max_reach);
        assert!(b.e.max_depth <= 1000);
        println!(
            "T8_EXIT_CONFIG case={case} parked={parked} gas={} loads={} stores={}",
            b.e.gas, b.e.loads, b.e.stores
        );
    }
}

#[test]
fn t8_exit_prime_sum_slot_fallback() {
    let params = generate_params_uncached(8);
    let inputs = crate::vectors::test_inputs(8);
    for moved in [false, true] {
        let mut b = builder(&params, &inputs, fork("amsterdam").unwrap(), vec![p1(); 8]);
        b.opts.external_d = true;
        b.opts.external_stream = true;
        b.opts.external_template = true;
        b.opts.internal_consume = true;
        let state = b.state.clone();
        let sums: [Id; 4] = std::array::from_fn(|i| {
            b.e.alloc(
                Value::new(
                    format!("S{i}"),
                    p1(),
                    inputs.iter().map(|v| field::add(v[i], v[i + 4])).collect(),
                    None,
                )
                .unwrap(),
            )
        });
        let previous = sentinels(&mut b, 4);
        let tail = sentinels(&mut b, 3);
        let mut stack = previous.clone();
        stack.extend_from_slice(&sums);
        stack.extend_from_slice(&state);
        stack.push(b.p());
        stack.extend_from_slice(&tail);
        if moved {
            stack.swap(4, 5);
        }
        b.e.set_stack(&stack);
        let out = b.ordered_block(BlockKind::Exit, 0, &state, &sums).unwrap();
        assert_eq!(b.e.find(sums[0]) == 0, !moved);
        if !moved {
            stack[4] = b.p();
        }
        let mut layout = vec![out[0], b.p(), out[1], out[2], out[3]];
        layout.extend_from_slice(&stack);
        assert_eq!(b.e.from_top(), layout);
        for (i, input) in inputs.iter().enumerate() {
            let expected = permutation_steps(&params, input, 0, 1);
            for (j, &id) in out.iter().enumerate() {
                assert_eq!(field::reduce(b.e.value(id).vals[i]), expected[j]);
            }
        }
    }
}

fn exit_prime_layer(b: &mut Builder<'_>, park: bool) -> Id {
    let state = b.state.clone();
    let before = b.e.gas;
    b.layers += 1;
    let mut sums = [0; 4];
    for i in (0..4).rev() {
        sums[i] = b
            .chain_sum(&[state[i], state[i + 4]], &format!("S{i}"), p1())
            .unwrap();
        b.e.end_line();
    }
    assert_eq!(b.e.gas - before, 68);
    let program = ordered_blocks(BlockKind::Block)[0];
    assert!(b.stream_block_fits(program, 1, &state, &sums, true));
    let first = b
        .stream_block(program, 1, &state, &sums, None, true, &mut [])
        .unwrap();
    assert_eq!(b.e.gas - before, 220);
    let mut floor = b.e.from_top();
    assert_eq!(&floor[..4], first);
    assert_eq!(b.e.find(sums[0]), 5);
    assert_eq!(b.e.find_prime(), 19);
    let ordinary = ordered_blocks(BlockKind::Exit)[0];
    let suffix = ordinary.strip_prefix("u1 u0 dup2 add=t0 ").unwrap();
    let prefix = if park {
        "u1 P take0 dup2 add=t0"
    } else {
        "u1 u0 dup2 add=t0"
    };
    let program = format!("{prefix} {suffix}");
    assert!(b.stream_block_fits(&program, 0, &state, &sums, true));
    let start = b.e.gas;
    b.stream_block(prefix, 0, &state, &sums, None, true, &mut [])
        .unwrap();
    assert_eq!(b.e.gas - start, if park { 27 } else { 24 });
    if park {
        floor[4] = b.p();
        assert_eq!(b.e.find(sums[0]), 0);
    }
    assert_eq!(&b.e.from_top()[2..], floor);
    let u0 = b.e.values.iter().rev().find(|v| v.name == "u0").unwrap();
    assert_eq!(u0.bound, p1() + p1());
    let last = b
        .stream_block(suffix, 0, &state, &sums, None, true, &mut [])
        .unwrap();
    b.state = last.into_iter().chain(first).collect();
    let mut expected = vec![last[0], b.p(), last[1], last[2], last[3]];
    expected.extend_from_slice(&floor);
    assert_eq!(b.e.from_top(), expected);
    assert_eq!(b.e.gas - before, if park { 378 } else { 375 });
    sums[0]
}

#[test]
fn t8_exit_prime_lifetime_and_real_internal_entry() {
    let params = generate_params_uncached(8);
    let mut inputs = crate::vectors::test_inputs(8);
    inputs.push(vec![p1(); 8]);
    let round = params.rounds_f / 2;
    for whole_round in [false, true] {
        let mut baseline = None;
        for park in [false, true] {
            let mut b = builder(&params, &inputs, fork("amsterdam").unwrap(), vec![p1(); 8]);
            b.opts.external_d = true;
            b.opts.external_stream = true;
            b.opts.external_template = true;
            b.opts.internal_consume = true;
            b.opts.prime_stack = true;
            b.opts.tree_sums = true;
            let tail = sentinels(&mut b, 3);
            let mut stack = b.e.from_top();
            stack.extend_from_slice(&tail);
            b.e.set_stack(&stack);
            input_last_use_pair(&mut b, 0, true);
            input_last_use_pair(&mut b, 1, true);
            let values: Vec<Vec<U256>> = (0..b.vectors)
                .map(|i| b.state.iter().map(|&v| b.e.value(v).vals[i]).collect())
                .collect();
            let before = b.e.gas;
            let sum = exit_prime_layer(&mut b, park);
            let linear: Vec<Vec<U256>> = values
                .iter()
                .map(|v| permutation_steps(&params, v, 0, 1))
                .collect();
            for (i, expected) in linear.iter().enumerate() {
                for (j, &id) in b.state.iter().enumerate() {
                    assert_eq!(field::reduce(b.e.value(id).vals[i]), expected[j]);
                }
            }
            let state = b.state.clone();
            let line = b.e.lines.len();
            let pops = b.e.pops;
            if whole_round {
                b.internal_round_consume(round, true, None).unwrap();
                assert_eq!(b.e.pops - pops, usize::from(!park));
                let ops: Vec<String> = b.e.lines[line..]
                    .iter()
                    .map(|line| line.split_once("//").unwrap().0.trim().to_string())
                    .collect();
                let mut body = ops.clone();
                let repair = if park { 0 } else { 8 };
                if !park {
                    assert_eq!(body.remove(1), "dupn 23 swap9 pop");
                }
                assert!(!body.iter().any(|line| line.contains("pop")));
                assert_eq!(
                    (if park { 378 } else { 375 }) + 45 + repair,
                    if park { 423 } else { 428 }
                );
                for (i, input) in linear.iter().enumerate() {
                    let expected = permutation_steps(&params, input, round + 1, round + 2);
                    for (&id, expected) in b.state.iter().zip(expected) {
                        assert_eq!(field::reduce(b.e.value(id).vals[i]), expected);
                    }
                }
                let signature: Vec<_> =
                    b.e.from_top()
                        .iter()
                        .map(|&id| {
                            let v = b.e.value(id);
                            (id, v.bound, v.vals.clone())
                        })
                        .collect();
                if let Some((gas, prior_stack, prior_body)) = &baseline {
                    assert_eq!(b.e.gas - before + 5, *gas);
                    assert_eq!(&signature, prior_stack);
                    assert_eq!(&body, prior_body);
                } else {
                    baseline = Some((b.e.gas - before, signature, body));
                }
                println!(
                    "T8_EXIT_PRIME park={park} boundary={} through_round={}",
                    if park { 423 } else { 428 },
                    b.e.gas - before
                );
            } else {
                let before_sbox = b.e.gas;
                let x5 = b.round_start(round, None).unwrap();
                assert_eq!(b.e.gas - before_sbox, 45);
                let top = b.e.from_top();
                assert_eq!(top[0], x5);
                assert_eq!(&top[1..8], &state[1..]);
                assert_eq!(top[8], if park { b.p() } else { sum });
                assert_eq!(b.e.bound(x5), p1());
                assert_eq!(b.e.gas - before, if park { 423 } else { 420 });
            }
            let top = b.e.from_top();
            assert_eq!(&top[top.len() - tail.len()..], tail);
            assert!(b.e.max_dup <= b.e.max_reach);
            assert!(b.e.max_depth <= 1000);
            assert_eq!((b.e.loads, b.e.stores), (0, 0));
        }
    }
}

#[test]
fn t8_prime_early_lands_m0_on_the_stacked_copies() {
    let params = generate_params_uncached(8);
    let mut inputs = crate::vectors::test_inputs(8);
    inputs.push(vec![p1(); 8]);
    let build =
        |fork: Fork, base: BuildOptions, prime_early: bool| -> Result<(Builder<'_>, Vec<Id>)> {
            let opts = BuildOptions {
                external_d: true,
                internal_consume: true,
                prime_stack: true,
                prime_early,
                external_template: true,
                tree_sums: true,
                ..base
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
            )?;
            let out = b.build()?;
            Ok((b, out))
        };
    let amsterdam = fork("amsterdam").unwrap();
    let streamed = BuildOptions {
        external_stream: true,
        ..DEFAULT_OPTIONS
    };
    let (laid, _) = build(amsterdam, streamed, false).unwrap();
    let (early, out) = build(amsterdam, streamed, true).unwrap();
    // the copies of the swapped elements are pushed under the sum's own,
    // and m0 lands on them: the SWAP that put it there goes, every round
    assert_eq!(laid.e.gas - early.e.gas, 3 * params.rounds_p as u64);
    assert_eq!(early.e.max_dup, laid.e.max_dup);
    assert!(early.e.max_depth <= laid.e.max_depth);
    assert!(early.e.max_dup <= amsterdam.reach);
    let round = early
        .e
        .lines
        .iter()
        .position(|l| l.contains("Round 5 (internal)"))
        .unwrap();
    let text = early.e.lines[round + 1..round + 4].join("\n");
    assert!(!text.contains("swap7"), "{text}");
    assert!(text.contains("swap9 0x"), "{text}");
    for (i, input) in inputs.iter().enumerate() {
        let expected = permutation_steps(&params, input, 0, step_count(&params));
        for (&id, expected) in out.iter().zip(expected) {
            assert_eq!(early.e.value(id).vals[i], expected);
            assert_eq!(early.e.bound(id), p1());
        }
    }
    // the sum's DUPs then reach past the copies: not within DUP16 (the
    // options Osaka selects)
    let osaka = fork("osaka").unwrap();
    let stored = BuildOptions {
        diag_in_memory: true,
        diag_push32: 7,
        ..DEFAULT_OPTIONS
    };
    assert!(build(osaka, stored, true).is_err());
    assert!(build(osaka, stored, false).is_ok());
}

#[test]
fn t8_seam_runs_the_next_s_boxes_in_the_last_consuming_round() {
    let params = generate_params_uncached(8);
    let mut inputs = crate::vectors::test_inputs(8);
    inputs.push(vec![p1(); 8]);
    let build = |external_seam: bool| -> (Builder<'_>, Vec<Id>) {
        let opts = BuildOptions {
            external_d: true,
            external_stream: true,
            internal_consume: true,
            prime_stack: true,
            prime_early: true,
            external_seam,
            external_template: true,
            tree_sums: true,
            ..DEFAULT_OPTIONS
        };
        let mut b = Builder::new(
            &params,
            &inputs,
            opts,
            fork("amsterdam").unwrap(),
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
        let out = b.build().unwrap();
        (b, out)
    };
    let (plain, _) = build(false);
    let (seam, out) = build(true);
    // every lane but s0' lands over its second copy: no copy and no DUP of
    // the output for its S-box in the external round
    assert_eq!(plain.e.gas - seam.e.gas, 3 * (params.t as u64 - 1));
    assert!(seam.e.max_depth < plain.e.max_depth);
    let last = params.rounds_f / 2 + params.rounds_p - 1;
    let from = seam
        .e
        .lines
        .iter()
        .position(|l| l.contains(&format!("Round {last} (internal)")))
        .unwrap();
    let to = seam
        .e
        .lines
        .iter()
        .position(|l| l.contains(&format!("Round {} (external)", last + 1)))
        .unwrap();
    let text = seam.e.lines[from..to].join("\n");
    assert_eq!(
        text.matches("mulmod dup1 mulmod mulmod").count(),
        1 + params.t
    );
    assert!(
        !seam.e.lines[to + 1].contains("mulmod"),
        "{}",
        seam.e.lines[to + 1]
    );
    for (i, input) in inputs.iter().enumerate() {
        let expected = permutation_steps(&params, input, 0, step_count(&params));
        for (&id, expected) in out.iter().zip(expected) {
            assert_eq!(seam.e.value(id).vals[i], expected);
            assert_eq!(seam.e.bound(id), p1());
        }
    }
}
