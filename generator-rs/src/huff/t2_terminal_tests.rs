use super::*;
use crate::field;
use crate::huff::fork::fork;
use crate::value::{Value, apply_op};

pub(crate) const OPTIONS: BuildOptions = BuildOptions {
    prime_under_external: false,
    internal_reduce_outputs: true,
    external_template: true,
    internal_mul3: true,
    ..DEFAULT_OPTIONS
};

fn replay(e: &mut Emitter, text: &str) -> Result<()> {
    for token in text.split_whitespace() {
        if let Some(n) = token.strip_prefix("dup") {
            let n = n.parse::<usize>().unwrap();
            assert!(n <= 6);
            e.dup(e.top(n - 1)?)?;
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

// [y,P,x,P,T] -> memory [z0,z1], stack [x,P,T].
fn terminal(e: &mut Emitter) -> Result<Vec<Id>> {
    if e.memory != 0 || e.prime_slot.is_some() {
        bail!("terminal entry needs untouched memory");
    }
    let y = e.top(0)?;
    let x = e.top(2)?;
    if e.top(1)? != e.p || e.top(3)? != e.p {
        bail!("terminal entry needs PRIME in slots two and four");
    }
    if e.bound(x) >= PRIME || e.bound(y) >= PRIME {
        bail!("terminal entry needs clean S-box outputs");
    }
    let tail = e.from_top()[4..].to_vec();
    replay(e, "dup1 dup4 add dup3 dup2 dup6 addmod")?;
    let z0 = e.top(0)?;
    assert_eq!(e.mstore_next(0)?, z0);
    e.end_line();
    replay(e, "addmod")?;
    let z1 = e.top(0)?;
    assert_eq!(e.mstore_next(32)?, z1);
    e.end_line();
    let mut want = vec![x, e.p];
    want.extend(tail);
    assert_eq!(e.from_top(), want);
    assert_eq!(e.memory, 64);
    for &out in &[z0, z1] {
        assert_eq!(e.bound(out), p1());
    }
    Ok(vec![z0, z1])
}

// A checked whole-entry fixture, not a production schedule or split mode.
pub(crate) fn build_fixture(
    params: &Params,
    inputs: &[Vec<U256>],
    fork: Fork,
    memory_output: bool,
    tail_len: usize,
) -> Result<(BuildResult, usize)> {
    assert_eq!((params.t, params.rounds_f, params.rounds_p), (2, 8, 56));
    let range = Range {
        from: 0,
        to: step_count(params),
    };
    let mut b = Builder::new(
        params,
        inputs,
        OPTIONS,
        fork,
        range,
        HashSet::new(),
        false,
        true,
        &Boundary::default(),
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
    for round in 0..64 {
        b.e.next_round();
        if (4..60).contains(&round) {
            b.e.comment(&format!("Round {round} (internal)"));
            b.internal_round(round, true)?;
        } else {
            b.e.comment(&format!("Round {round} (external)"));
            if round == 63 && memory_output {
                assert_eq!((b.e.memory, b.e.stores, b.e.loads), (0, 0, 0));
                assert!(b.e.tables.is_empty());
                assert_eq!(b.input_slots, vec![None; 2]);
                let inputs = b.state.clone();
                b.template_lane(&inputs, 0, round, true)?;
                b.e.end_line();
                for _ in 0..3 {
                    b.e.push_prime()?;
                }
                b.e.swap(4)?;
                b.template_lane(&inputs, 1, round, true)?;
                b.e.end_line();
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
    }
    b.e.end_line();
    for (k, input) in inputs.iter().enumerate() {
        let expected = permutation_steps(params, input, 0, step_count(params));
        for (i, &out) in b.state.iter().enumerate() {
            assert_eq!(b.e.bound(out), p1());
            assert_eq!(b.e.value(out).vals[k], expected[i]);
        }
    }
    let stack = b.e.from_top();
    assert_eq!(&stack[stack.len() - tail_len..], &tail);
    assert_eq!(stack[stack.len() - tail_len - 1], b.p());
    if !memory_output {
        assert_eq!(&stack[..2], &b.state);
        assert_eq!(stack[2], b.p());
    }
    assert_eq!(b.e.memory, if memory_output { 64 } else { 0 });
    assert_eq!(b.state_in_memory, memory_output);
    assert_eq!(b.stored, memory_output);
    assert_eq!(b.step_bytes.last(), Some(&b.e.bytes));
    let e = b.e;
    Ok((
        BuildResult {
            lines: e.lines,
            gas: e.gas,
            bytes: e.bytes,
            max_depth: e.max_depth,
            max_dup: e.max_dup,
            swaps: e.swaps,
            pops: e.pops,
            stores: e.stores,
            loads: e.loads,
            range,
            state_in_memory: b.state_in_memory,
            input_slots: b.input_slots,
            step_bytes: b.step_bytes,
            memory: e.memory,
            tables: e.tables,
        },
        stack.len(),
    ))
}

#[test]
fn t2_terminal_bounds_tails_and_store_guards() {
    let l = p1();
    assert!(l.checked_mul(u256(4)).is_some());
    let val = |name: &str, bound, word, constant| {
        Value::new(name.into(), bound, vec![word], constant).unwrap()
    };
    let p = val("P", PRIME, PRIME, Some(PRIME));
    for right in [l, generate_params_for_test().round_constants[63][0]] {
        let b = val("b", right, U256::ZERO, None);
        for (bound, fits) in [
            (UINT256_MAX - right, true),
            (UINT256_MAX - right + u256(1), false),
        ] {
            let a = val("a", bound, U256::ZERO, None);
            let result = apply_op(Op::Add, &[&a, &b], "sum".into(), 1);
            assert_eq!(result.is_ok(), fits);
            if fits {
                assert_eq!(result.unwrap().bound, UINT256_MAX);
            }
        }
    }
    let x = val("x", l, l, None);
    let fake_p = val("fake P", PRIME, PRIME, None);
    assert!(apply_op(Op::Addmod, &[&x, &x, &fake_p], "sum".into(), 1).is_err());
    assert!(apply_op(Op::Addmod, &[&x, &x, &p], "sum".into(), 1).is_ok());
    for name in ["amsterdam", "osaka", "paris"] {
        for tail_len in [0, 3, 120] {
            for x in [U256::ZERO, u256(1), l] {
                for y in [U256::ZERO, u256(1), l] {
                    let mut e = Emitter::new(1, fork(name).unwrap(), HashSet::new(), false, true);
                    let x_id = e.alloc(val("x", l, x, None));
                    let y_id = e.alloc(val("y", l, y, None));
                    let mut stack = vec![y_id, e.p, x_id, e.p];
                    for i in 0..tail_len {
                        let word = u256(100 + i as u64);
                        stack.push(e.alloc(val("caller", word, word, Some(word))));
                    }
                    e.set_stack(&stack);
                    for memory in [1, 32, 64, 512] {
                        e.memory = memory;
                        assert!(terminal(&mut e).is_err());
                        assert_eq!((e.gas, e.bytes), (0, 0));
                        assert_eq!(e.from_top(), stack);
                    }
                    e.memory = 1;
                    assert!(e.mstore_next(1).is_err());
                    e.memory = 0;
                    for slot in [1, 3] {
                        let mut wrong = stack.clone();
                        wrong[slot] = x_id;
                        e.set_stack(&wrong);
                        assert!(terminal(&mut e).is_err());
                        assert_eq!((e.gas, e.bytes), (0, 0));
                        assert_eq!(e.from_top(), wrong);
                    }
                    let dirty = e.alloc(val("dirty", PRIME, U256::ZERO, None));
                    let mut wrong = stack.clone();
                    wrong[2] = dirty;
                    e.set_stack(&wrong);
                    assert!(terminal(&mut e).is_err());
                    assert_eq!((e.gas, e.bytes), (0, 0));
                    e.set_stack(&stack);
                    e.prime_slot = Some(0);
                    assert!(terminal(&mut e).is_err());
                    e.prime_slot = None;
                    let out = terminal(&mut e).unwrap();
                    assert_eq!(e.value(out[0]).vals[0], field::add(field::add(x, y), x));
                    assert_eq!(e.value(out[1]).vals[0], field::add(field::add(x, y), y));
                    assert_eq!((e.gas, e.bytes, e.memory), (44, 12, 64));
                    assert_eq!(e.max_depth, tail_len + 8);
                    assert_eq!(e.max_dup, 6);
                    let before = (e.from_top(), e.gas, e.bytes, e.memory);
                    assert!(e.mstore_next(0).is_err());
                    assert!(e.mstore_next(65).is_err());
                    assert_eq!((e.from_top(), e.gas, e.bytes, e.memory), before);
                }
            }
        }
        let params = generate_params_for_test();
        for tail in [0, 3, 120] {
            for memory in [false, true] {
                let (result, _) =
                    build_fixture(&params, &[vec![l; 2]], fork(name).unwrap(), memory, tail)
                        .unwrap();
                assert_eq!(result.max_depth, 130 + tail);
                assert!(result.max_dup <= fork(name).unwrap().reach);
            }
        }
    }
}

fn generate_params_for_test() -> std::sync::Arc<Params> {
    crate::round_constants::generate_params(2)
}
