use super::*;
use crate::field;
use crate::huff::fork::fork;
use crate::huff::render::{render_entry, render_entry_plan};
use crate::huff::{entry_wrapper, select_terminal};
use crate::round_constants::generate_params;
use crate::value::Value;

fn tokens(lines: &[String]) -> Vec<&str> {
    lines
        .iter()
        .flat_map(|line| line.split("//").next().unwrap().split_whitespace())
        .collect()
}

#[test]
fn t3_terminal_production_builder_and_selection_guards() {
    let params = generate_params(3);
    let inputs = crate::vectors::test_inputs(3);
    let range = Range {
        from: 0,
        to: step_count(&params),
    };
    assert_eq!(T3_OPTIONS, super::super::t3_terminal_tests::OPTIONS);
    assert!(eligible3(&params, T3_OPTIONS, range, &Boundary::default()));
    assert!(!eligible(&params, T3_OPTIONS, range, &Boundary::default()));
    for boundary in [
        Boundary {
            bounds: Some(vec![p1(); 3]),
            ..Boundary::default()
        },
        Boundary {
            calldata: true,
            ..Boundary::default()
        },
        Boundary {
            live: Some(vec![0]),
            ..Boundary::default()
        },
        Boundary {
            prime_second: true,
            ..Boundary::default()
        },
        Boundary {
            prime_below: Some(0),
            ..Boundary::default()
        },
        Boundary {
            store_inputs: true,
            ..Boundary::default()
        },
    ] {
        assert!(!eligible3(&params, T3_OPTIONS, range, &boundary));
    }
    for change in 0..3 {
        let mut wrong = (*generate_params(3)).clone();
        match change {
            0 => wrong.t = 2,
            1 => wrong.rounds_f = 10,
            _ => wrong.rounds_p = 55,
        }
        assert!(!eligible3(&wrong, T3_OPTIONS, range, &Boundary::default()));
    }
    for name in ["amsterdam", "osaka", "paris"] {
        let fork = fork(name).unwrap();
        let prior = crate::huff::build_entry(&params, &inputs, fork)
            .unwrap()
            .unwrap();
        assert_eq!(prior.opts, T3_OPTIONS);
        let candidate = build(&params, &inputs, fork, &prior).unwrap().unwrap();
        let fixture =
            super::super::t3_terminal_tests::build_fixture(&params, &inputs, fork, true, 0)
                .unwrap()
                .0;
        assert_eq!(tokens(&candidate.lines), tokens(&fixture.lines));
        assert_eq!(
            (
                candidate.gas,
                candidate.bytes,
                candidate.memory,
                candidate.max_depth,
                candidate.max_dup
            ),
            (7581, 6629, 96, 75, 9)
        );
        assert_eq!(candidate.step_bytes, fixture.step_bytes);
        assert_eq!(&candidate.step_bytes[..64], &prior.result.step_bytes[..64]);
        assert_eq!(candidate.step_bytes.len(), 65);
        assert_eq!(candidate.step_bytes.last(), Some(&candidate.bytes));
        assert_eq!(candidate.input_slots, [None; 3]);
        assert!(candidate.state_in_memory);
        let plan = crate::huff::build_entry_plan(&params, &inputs, fork)
            .unwrap()
            .unwrap();
        assert_eq!(plan.permutation().result.lines, prior.result.lines);
        assert_eq!(tokens(&plan.entry_result().lines), tokens(&candidate.lines));
        assert!(render_entry_plan(&params, &fork, &plan).contains("outputs stored at [0, 0x60)"));
        for change in 0..14 {
            let mut bad = prior.clone();
            match change {
                0 => bad.result.memory = 32,
                1 => bad.result.state_in_memory = true,
                2 => bad.result.input_slots[0] = Some(RAW_INPUT),
                3 => bad.result.input_slots[0] = Some(COMPACT_INPUT),
                4 => {
                    bad.result.input_slots.pop();
                }
                5 => bad.result.range.from = 1,
                6 => bad.result.range.to -= 1,
                7 => bad.opts.prime_under_external = true,
                8 => bad.opts.shadow = true,
                9 => bad.opts = OPTIONS,
                10 => bad.result.loads = 1,
                11 => bad.result.stores = 1,
                12 => bad.result.tables.push(Table {
                    name: "bad".into(),
                    words: vec![],
                }),
                _ => bad.result.lines.push("mload".into()),
            }
            assert!(
                build(&params, &inputs, fork, &bad).unwrap().is_none(),
                "{name} change {change}"
            );
        }
        let bytes = candidate.bytes + entry_wrapper(3, fork, &candidate);
        for delta in [0, 1] {
            let mut limited = fork;
            limited.code_size = bytes - delta;
            assert_eq!(
                select_terminal(3, limited, prior.clone(), Ok(Some(candidate.clone())))
                    .terminal_result()
                    .is_some(),
                delta == 0
            );
        }
        let mut edge = candidate.clone();
        edge.max_depth = 1000;
        edge.max_dup = fork.reach;
        assert!(
            select_terminal(3, fork, prior.clone(), Ok(Some(edge)))
                .terminal_result()
                .is_some()
        );
        for change in 0..6 {
            let mut bad = candidate.clone();
            match change {
                0 => bad.bytes = usize::MAX,
                1 => bad.max_depth = 1001,
                2 => bad.max_dup = fork.reach + 1,
                3 => bad.gas += 12,
                4 => bad.gas += 13,
                _ => bad.bytes = fork.code_size,
            }
            let plan = select_terminal(3, fork, prior.clone(), Ok(Some(bad)));
            assert!(plan.terminal_result().is_none());
            assert_eq!(
                render_entry_plan(&params, &fork, &plan),
                render_entry(&params, &fork, &prior.result)
            );
        }
        for missing in [Ok(None), Err(Error("failed terminal build".into()))] {
            let plan = select_terminal(3, fork, prior.clone(), missing);
            assert!(plan.terminal_result().is_none());
            assert_eq!(plan.entry_result().lines, prior.result.lines);
        }
    }
}

fn final_builder<'a>(params: &'a Params, inputs: &[Vec<U256>], fork: Fork) -> Builder<'a> {
    let mut b = Builder::new(
        params,
        inputs,
        T3_OPTIONS,
        fork,
        Range { from: 0, to: 65 },
        HashSet::new(),
        false,
        true,
        &Boundary::default(),
    )
    .unwrap();
    b.terminal = Some(Terminal::T3);
    b.state = (0..3)
        .map(|i| {
            b.e.alloc(
                Value::new(
                    format!("s{i}"),
                    p1() * u256(4),
                    vec![U256::ZERO; inputs.len()],
                    None,
                )
                .unwrap(),
            )
        })
        .collect();
    b.e.set_stack(&[b.state[0], b.e.p, b.state[2], b.state[1]]);
    // The unit fixture supplies a recorded stack-only predecessor.
    b.e.lines.push("dup1 add".into());
    b
}

#[test]
fn t3_terminal_production_final_round_guards() {
    let params = generate_params(3);
    let inputs = vec![vec![U256::ZERO; 3]];
    for name in ["amsterdam", "osaka", "paris"] {
        let fork = fork(name).unwrap();
        let mut b = final_builder(&params, &inputs, fork);
        b.terminal_round3(63).unwrap();
        assert!(b.stored && b.state_in_memory);
        assert_eq!(b.e.memory, 96);
        let expected = permutation_steps(&params, &inputs[0], 64, 65);
        for (&out, want) in b.state.iter().zip(expected) {
            assert_eq!(b.e.value(out).vals[0], want);
            assert!(b.e.bound(out) < PRIME);
        }
        for change in 0..20 {
            let mut b = final_builder(&params, &inputs, fork);
            match change {
                0 => b.terminal = None,
                1 => b.range.from = 1,
                2 => b.range.to = 64,
                3 => b.live = Some(vec![0]),
                4 => b.state_in_memory = true,
                5 => b.stored = true,
                6 => b.lane_constants = Some(vec![U256::ZERO; 3]),
                7 => b.input_slots[0] = Some(RAW_INPUT),
                8 => b.input_slots[0] = Some(COMPACT_INPUT),
                9 => b.e.memory = 32,
                10 => b.e.prime_slot = Some(0),
                11 => b.e.stores = 1,
                12 => b.e.loads = 1,
                13 => b.e.tables.push(Table {
                    name: "bad".into(),
                    words: vec![],
                }),
                14 => b.opts.prime_under_external = true,
                15 => {
                    let dirty = b.e.alloc(
                        Value::new(
                            "unsafe zero".into(),
                            p1() * u256(4) + u256(1),
                            vec![U256::ZERO],
                            None,
                        )
                        .unwrap(),
                    );
                    b.state[0] = dirty;
                    b.e.set_stack(&[dirty, b.e.p, b.state[2], b.state[1]]);
                }
                16 => {
                    let fake =
                        b.e.alloc(Value::new("fake P".into(), PRIME, vec![PRIME], None).unwrap());
                    b.e.set_stack(&[b.state[0], fake, b.state[2], b.state[1]]);
                }
                17 => b.e.set_stack(&[b.state[2], b.e.p, b.state[0], b.state[1]]),
                18 => b.e.lines.push("mload".into()),
                _ => {
                    b.state.pop();
                }
            }
            let before = (
                b.e.from_top(),
                b.e.gas,
                b.e.bytes,
                b.e.memory,
                b.e.lines.clone(),
            );
            assert!(b.terminal_round3(63).is_err(), "{name} change {change}");
            assert_eq!(
                (b.e.from_top(), b.e.gas, b.e.bytes, b.e.memory, b.e.lines),
                before
            );
        }
        for round in [0, 62, 64, usize::MAX] {
            assert!(
                final_builder(&params, &inputs, fork)
                    .terminal_round3(round)
                    .is_err()
            );
        }
    }
}

#[test]
fn t3_terminal_production_suffix_bounds_tails_and_stores() {
    let value = |name: &str, bound, word| Value::new(name.into(), bound, vec![word], None).unwrap();
    for name in ["amsterdam", "osaka", "paris"] {
        let fork = fork(name).unwrap();
        for tail_len in [0, 3, 120] {
            for x in [U256::ZERO, u256(1), p1()] {
                for y in [U256::ZERO, u256(1), p1()] {
                    for z in [U256::ZERO, u256(1), p1()] {
                        let mut e = Emitter::new(1, fork, HashSet::new(), false, true);
                        let ids = [
                            e.alloc(value("y", p1(), y)),
                            e.p,
                            e.alloc(value("z", p1(), z)),
                            e.alloc(value("x", p1(), x)),
                            e.p,
                        ];
                        let mut stack = ids.to_vec();
                        for i in 0..tail_len {
                            let word = u256(100 + i as u64);
                            stack.push(e.alloc(value("caller", word, word)));
                        }
                        e.set_stack(&stack);
                        for memory in [1, 32, 64, 96, 512] {
                            e.memory = memory;
                            assert!(terminal3(&mut e).is_err());
                            assert_eq!((e.from_top(), e.gas, e.bytes), (stack.clone(), 0, 0));
                        }
                        e.memory = 0;
                        e.prime_slot = Some(0);
                        assert!(terminal3(&mut e).is_err());
                        e.prime_slot = None;
                        for i in [0, 2, 3] {
                            let dirty = e.alloc(value("dirty zero", PRIME, U256::ZERO));
                            let mut wrong = stack.clone();
                            wrong[i] = dirty;
                            e.set_stack(&wrong);
                            assert!(terminal3(&mut e).is_err());
                            assert_eq!((e.from_top(), e.gas, e.bytes), (wrong, 0, 0));
                        }
                        e.set_stack(&stack);
                        for offset in [1, 32, usize::MAX] {
                            assert!(e.mstore_next(offset).is_err());
                            assert_eq!(
                                (e.from_top(), e.gas, e.bytes, e.memory),
                                (stack.clone(), 0, 0, 0)
                            );
                        }
                        let outputs = terminal3(&mut e).unwrap();
                        let sum = field::add(field::add(x, y), z);
                        for (&out, word) in outputs.iter().zip([x, y, z]) {
                            assert_eq!(e.value(out).vals[0], field::add(sum, word));
                            assert_eq!(e.bound(out), p1());
                        }
                        assert_eq!(e.from_top(), &stack[5..]);
                        assert_eq!(
                            (e.gas, e.bytes, e.memory, e.max_depth, e.max_dup),
                            (66, 18, 96, tail_len + 8, 6)
                        );
                        assert_eq!(
                            tokens(&e.lines),
                            super::super::t3_terminal_tests::SUFFIX
                                .split_whitespace()
                                .collect::<Vec<_>>()
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn t3_terminal_production_split_keeps_canonical_boundaries() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let mut fork = fork("osaka").unwrap();
    fork.code_size = 1500;
    let width = crate::huff::generate(3, &fork).unwrap();
    assert!(matches!(&width.target, crate::huff::Target::Parts { paths, .. } if paths.len() > 1));
    for (_, source) in width.files().filter(|(path, _)| path.ends_with(".huff")) {
        assert!(!source.contains("Private terminal body"));
    }
    let reports = crate::huff::verify::verify(&root, &fork, &[width]).unwrap();
    assert_eq!(reports[0].gas.diff(), 0);
    assert_eq!(reports[0].warm.unwrap().diff(), 0);
}
