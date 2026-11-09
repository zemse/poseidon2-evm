use super::*;
use crate::field;
use crate::huff::fork::fork;
use crate::value::{Value, apply_op};

pub(crate) const OPTIONS: BuildOptions = BuildOptions {
    prime_under_external: false,
    external_template: true,
    internal_template: true,
    external_seam: true,
    ..DEFAULT_OPTIONS
};

pub(crate) const SUFFIX: &str = "dup2 dup2 dup5 add dup6 add dup1 swap6 addmod msize mstore dup4 addmod msize mstore addmod msize mstore";

fn replay(e: &mut Emitter, text: &str) -> Result<()> {
    for token in text.split_whitespace() {
        if let Some(n) = token.strip_prefix("dup") {
            let n = n.parse::<usize>().unwrap();
            assert!(n <= 7);
            e.dup(e.top(n - 1)?)?;
        } else if let Some(n) = token.strip_prefix("swap") {
            e.swap(n.parse().unwrap())?;
        } else if token == "P" {
            e.push(PRIME, None)?;
        } else {
            let op = match token {
                "add" => Op::Add,
                "addmod" => Op::Addmod,
                _ => bail!("unknown terminal move {token}"),
            };
            let operands = (0..op.arity())
                .map(|i| e.top(i).map(inplace))
                .collect::<Result<Vec<_>>>()?;
            e.compute(op, &operands, token)?;
        }
    }
    e.end_line();
    Ok(())
}

// [y,P,z,x,P,U] -> memory [o0,o1,o2], stack [U].
fn terminal(e: &mut Emitter) -> Result<Vec<Id>> {
    if e.memory != 0 || e.prime_slot.is_some() {
        bail!("terminal entry needs untouched memory");
    }
    let y = e.top(0)?;
    let z = e.top(2)?;
    let x = e.top(3)?;
    if e.top(1)? != e.p || e.top(4)? != e.p {
        bail!("terminal entry needs PRIME in slots two and five");
    }
    if [x, y, z].iter().any(|&id| e.bound(id) >= PRIME) {
        bail!("terminal entry needs clean S-box outputs");
    }
    let tail = e.from_top()[5..].to_vec();
    replay(e, "dup2 dup2 dup5 add dup6 add")?;
    assert_eq!(e.bound(e.top(0)?), p1() * u256(3));
    replay(e, "dup1 swap6 addmod")?;
    let o0 = e.top(0)?;
    assert_eq!(e.mstore_next(0)?, o0);
    e.end_line();
    replay(e, "dup4 addmod")?;
    let o1 = e.top(0)?;
    assert_eq!(e.mstore_next(32)?, o1);
    e.end_line();
    replay(e, "addmod")?;
    let o2 = e.top(0)?;
    assert_eq!(e.mstore_next(64)?, o2);
    e.end_line();
    assert_eq!(e.from_top(), tail);
    assert_eq!(e.memory, 96);
    for &out in &[o0, o1, o2] {
        assert_eq!(e.bound(out), p1());
    }
    Ok(vec![o0, o1, o2])
}

// A checked whole-entry fixture, not a production schedule or split mode.
pub(crate) fn build_fixture(
    params: &Params,
    inputs: &[Vec<U256>],
    fork: Fork,
    memory_output: bool,
    tail_len: usize,
) -> Result<(BuildResult, usize)> {
    assert_eq!((params.t, params.rounds_f, params.rounds_p), (3, 8, 56));
    let range = Range {
        from: 0,
        to: step_count(params),
    };
    let boundary = Boundary::default();
    let mut b = Builder::new(
        params,
        inputs,
        OPTIONS,
        fork,
        range,
        HashSet::new(),
        false,
        true,
        &boundary,
    )?;
    let mut stack = b.e.from_top();
    let mut tail = Vec::new();
    for i in 0..tail_len {
        let word = u256(100 + i as u64);
        tail.push(b.e.alloc(Value::new(
            format!("caller{i}"),
            word,
            vec![word; inputs.len()],
            Some(word),
        )?));
    }
    stack.extend_from_slice(&tail);
    b.e.set_stack(&stack);
    b.e.next_round();
    b.e.comment("Initial linear layer");
    b.external_template(TemplateKind::Entry, None)?;
    b.e.comment("");
    b.step_bytes.push(b.e.bytes);
    let mut round = 0;
    while round < 64 {
        b.e.next_round();
        if (4..60).contains(&round) {
            b.e.comment(&format!("Round {round} (internal)"));
            if b.internal_external3(round)? {
                assert_eq!(round, 59);
                round += 1;
            } else {
                assert_ne!(round, 59);
                b.internal_round(round, true)?;
            }
        } else if round == 0 {
            // rounds 0 to 2 as one program
            b.e.comment(&format!("Round {round} (external)"));
            assert_eq!(b.external_chain(TemplateKind::Round, round)?, 3);
            b.e.comment("");
            b.step_bytes.push(b.e.bytes);
            round += 3;
            continue;
        } else if round == 61 && memory_output {
            // rounds 61 to 63: the S-boxes of each start among the linear
            // layer of the one before
            b.e.comment(&format!("Round {round} (external)"));
            assert_eq!(b.external_chain(TemplateKind::Final, round)?, 3);
            let p = b.p();
            assert_eq!(b.e.from_top()[1], p);
            assert_eq!(b.e.from_top()[4], p);
            assert!(t2_entry::stack_only(&b.e.lines, fork));
            b.state = terminal(&mut b.e)?;
            b.state_in_memory = true;
            b.stored = true;
            b.e.comment("");
            b.step_bytes.push(b.e.bytes);
            break;
        } else {
            b.e.comment(&format!("Round {round} (external)"));
            if round == 63 && memory_output {
                assert_eq!((b.e.memory, b.e.stores, b.e.loads), (0, 0, 0));
                assert!(b.e.tables.is_empty());
                assert_eq!(b.input_slots, vec![None; 3]);
                assert!(b.e.prime_slot.is_none());
                let state = b.state.clone();
                assert!(
                    b.e.from_top()
                        .starts_with(&[state[0], b.p(), state[2], state[1]])
                );
                for &id in &state {
                    assert_eq!(b.e.bound(id), p1() * u256(4));
                }
                let x = b.template_lane(&state, 0, round, true)?;
                b.e.end_line();
                b.e.push_prime()?;
                b.e.push_prime()?;
                b.e.swap(3)?;
                let z = b.template_lane(&state, 2, round, true)?;
                b.e.end_line();
                b.e.push_prime()?;
                b.e.push_prime()?;
                b.e.dup(state[1])?;
                let y = b.template_lane(&state, 1, round, true)?;
                b.e.end_line();
                let p = b.p();
                assert!(b.e.from_top().starts_with(&[y, p, z, x, p, state[1]]));
                assert!(t2_entry::stack_only(&b.e.lines, fork));
                b.state = terminal(&mut b.e)?;
                b.state_in_memory = true;
                b.stored = true;
            } else {
                let kind = match round {
                    3 => TemplateKind::Exit,
                    63 => TemplateKind::Final,
                    _ => TemplateKind::Round,
                };
                b.external_template(kind, Some(round))?;
            }
        }
        b.e.comment("");
        b.step_bytes.push(b.e.bytes);
        round += 1;
    }
    b.e.end_line();
    let stack = b.e.from_top();
    assert_eq!(&stack[stack.len() - tail_len..], &tail);
    assert_eq!(b.e.memory, if memory_output { 96 } else { 0 });
    assert_eq!(b.state_in_memory, memory_output);
    assert_eq!(b.stored, memory_output);
    assert_eq!(b.step_bytes.last(), Some(&b.e.bytes));
    let outputs = b.state.clone();
    let expected = expected_outputs(params, inputs, range);
    Ok((
        finish_checked(b, &outputs, &expected, &boundary)?,
        stack.len(),
    ))
}

#[test]
fn t3_terminal_bounds_tails_and_store_guards() {
    let l = p1();
    assert!(l.checked_mul(u256(5)).is_some());
    assert!(l.checked_mul(u256(6)).is_none());
    let val = |name: &str, bound, word, constant| {
        Value::new(name.into(), bound, vec![word], constant).unwrap()
    };
    let params = crate::round_constants::generate_params(3);
    let threshold = UINT256_MAX / u256(3);
    for (bound, fits) in [(threshold, true), (threshold + u256(1), false)] {
        let x = val("zero sample", bound, U256::ZERO, None);
        let pair = apply_op(Op::Add, &[&x, &x], "pair".into(), 1).unwrap();
        let result = apply_op(Op::Add, &[&pair, &x], "sum".into(), 1);
        assert_eq!(result.is_ok(), fits);
        if fits {
            let result = result.unwrap();
            assert_eq!(result.bound, UINT256_MAX);
            assert_eq!(result.vals, [U256::ZERO]);
        }
    }
    for &c in &params.round_constants[63] {
        let right = val("c", c, U256::ZERO, None);
        for (bound, fits) in [(UINT256_MAX - c, true), (UINT256_MAX - c + u256(1), false)] {
            let left = val("zero sample", bound, U256::ZERO, None);
            let result = apply_op(Op::Add, &[&left, &right], "sum".into(), 1);
            assert_eq!(result.is_ok(), fits);
            if fits {
                assert_eq!(result.unwrap().bound, UINT256_MAX);
            }
        }
    }
    for name in ["amsterdam", "osaka", "paris"] {
        let fork = fork(name).unwrap();
        for text in [
            "mload",
            "msize mstore",
            "codecopy",
            "calldatacopy",
            "jump",
            "stop",
        ] {
            assert!(!t2_entry::stack_only(&[format!("dup1 add {text}")], fork));
        }
        for bad in [
            val("fake P", PRIME, PRIME, None),
            val("wrong P", l, l, Some(l)),
            val("displaced P", l, U256::ZERO, None),
        ] {
            let mut e = Emitter::new(1, fork, HashSet::new(), false, true);
            let x = e.alloc(val("x", l, U256::ZERO, None));
            let bad = e.alloc(bad);
            e.set_stack(&[x, x, bad]);
            assert!(replay(&mut e, "addmod").is_err());
        }
        for tail_len in [0, 3, 120] {
            for x in [U256::ZERO, u256(1), l] {
                for y in [U256::ZERO, u256(1), l] {
                    for z in [U256::ZERO, u256(1), l] {
                        let mut e = Emitter::new(1, fork, HashSet::new(), false, true);
                        let ids = [
                            e.alloc(val("y", l, y, None)),
                            e.p,
                            e.alloc(val("z", l, z, None)),
                            e.alloc(val("x", l, x, None)),
                            e.p,
                        ];
                        let mut stack = ids.to_vec();
                        for i in 0..tail_len {
                            let word = u256(100 + i as u64);
                            stack.push(e.alloc(val("caller", word, word, Some(word))));
                        }
                        e.set_stack(&stack);
                        for memory in [1, 32, 64, 96, 512] {
                            e.memory = memory;
                            assert!(terminal(&mut e).is_err());
                            assert_eq!((e.gas, e.bytes), (0, 0));
                            assert_eq!(e.from_top(), stack);
                        }
                        e.memory = 1;
                        assert!(e.mstore_next(1).is_err());
                        e.memory = 0;
                        assert!(e.mstore_next(32).is_err());
                        e.prime_slot = Some(0);
                        assert!(terminal(&mut e).is_err());
                        e.prime_slot = None;
                        for slot in [0, 2, 3] {
                            let dirty = e.alloc(val("dirty zero", PRIME, U256::ZERO, None));
                            let mut wrong = stack.clone();
                            wrong[slot] = dirty;
                            e.set_stack(&wrong);
                            assert!(terminal(&mut e).is_err());
                            assert_eq!((e.gas, e.bytes), (0, 0));
                            assert_eq!(e.from_top(), wrong);
                        }
                        e.set_stack(&stack);
                        let outputs = terminal(&mut e).unwrap();
                        let sum = field::add(field::add(x, y), z);
                        for (&id, word) in outputs.iter().zip([x, y, z]) {
                            assert_eq!(e.value(id).vals[0], field::add(sum, word));
                        }
                        assert_eq!((e.gas, e.bytes, e.memory), (66, 18, 96));
                        assert_eq!((e.max_depth, e.max_dup), (tail_len + 8, 6));
                        let before = (e.from_top(), e.gas, e.bytes, e.memory);
                        assert!(e.mstore_next(0).is_err());
                        assert!(e.mstore_next(97).is_err());
                        assert_eq!((e.from_top(), e.gas, e.bytes, e.memory), before);
                    }
                }
            }
            for memory in [false, true] {
                let (result, _) =
                    build_fixture(&params, &[vec![l; 3]], fork, memory, tail_len).unwrap();
                assert_eq!(result.max_depth, 72 + tail_len);
                assert_eq!(result.max_dup, 9);
            }
        }
    }
}
