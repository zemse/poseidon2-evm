use super::*;
use crate::field;
use crate::huff::fork::fork;
use crate::round_constants::generate_params_uncached;
use crate::value::Value;

pub(crate) const OPTIONS: BuildOptions = BuildOptions {
    external_template: true,
    internal_template: true,
    ..DEFAULT_OPTIONS
};

// Rounds 59..60: [a,P,c,b,T] -> [s0',P,s1',s2',b,T].
const SEAM: &str = concat!(
    "c59 add dup2 dup1 dup3 dup1 mulmod dup1 mulmod mulmod ",
    "P P dup4 dup6 dup5 add addmod ",
    "P P P dup4 dup9 add k1 add dup2 dup1 dup3 dup1 mulmod dup1 mulmod mulmod ",
    "swap6 dup1 dup5 add k2 add addmod dup2 dup1 dup3 dup1 mulmod dup1 mulmod mulmod ",
    "swap3 add k0 add dup2 dup1 dup3 dup1 mulmod dup1 mulmod mulmod ",
    "P swap1 dup3 dup2 dup6 add add swap4 dup5 add swap3 dup5 add swap4 add",
);

fn replay(e: &mut Emitter, params: &Params) -> Result<()> {
    for token in SEAM.split_whitespace() {
        if let Some(n) = token.strip_prefix("dup") {
            let id = e.top(n.parse::<usize>().unwrap() - 1)?;
            e.dup(id)?;
        } else if let Some(n) = token.strip_prefix("swap") {
            e.swap(n.parse().unwrap())?;
        } else if token == "P" {
            e.push_prime()?;
        } else if matches!(token, "c59" | "k0" | "k1" | "k2") {
            let (round, lane) = match token {
                "c59" => (59, 0),
                "k0" => (60, 0),
                "k1" => (60, 1),
                _ => (60, 2),
            };
            e.push(params.round_constants[round][lane], Some(token))?;
        } else {
            let op = match token {
                "add" => Op::Add,
                "addmod" => Op::Addmod,
                "mulmod" => Op::Mulmod,
                _ => bail!("unknown seam opcode {token}"),
            };
            let operands = (0..op.arity())
                .map(|i| e.top(i).map(inplace))
                .collect::<Result<Vec<_>>>()?;
            e.compute(op, &operands, token)?;
            e.end_line();
        }
    }
    e.end_line();
    Ok(())
}

fn seam(b: &mut Builder<'_>) -> Result<()> {
    assert_eq!(b.e.top(0)?, b.state[0]);
    assert_eq!(b.e.top(1)?, b.p());
    assert_eq!(b.e.top(2)?, b.state[2]);
    assert_eq!(b.e.top(3)?, b.state[1]);
    replay(&mut b.e, b.params)?;
    b.state = vec![b.e.top(0)?, b.e.top(2)?, b.e.top(3)?];
    assert_eq!(b.e.top(1)?, b.p());
    Ok(())
}

fn builder<'a>(
    params: &'a Params,
    inputs: &[Vec<U256>],
    bounds: Vec<U256>,
    fork: Fork,
) -> Result<Builder<'a>> {
    Builder::new(
        params,
        inputs,
        OPTIONS,
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
}

fn internal_layout(b: &mut Builder<'_>, tail: &[Id]) {
    let mut stack = vec![b.state[0], b.p(), b.state[2], b.state[1]];
    stack.extend_from_slice(tail);
    b.e.set_stack(&stack);
}

fn check_values(b: &Builder<'_>, inputs: &[Vec<U256>], from: usize, to: usize) {
    for (k, input) in inputs.iter().enumerate() {
        let expected = permutation_steps(b.params, input, from, to);
        for (i, &id) in b.state.iter().enumerate() {
            assert_eq!(field::reduce(b.e.value(id).vals[k]), expected[i]);
        }
    }
}

// Full-entry fixture only; the interleaved seam has no split at round 59.
pub(crate) fn build_fixture(
    params: &Params,
    inputs: &[Vec<U256>],
    fork: Fork,
) -> Result<BuildResult> {
    assert_eq!(params.t, 3);
    assert_eq!((params.rounds_f, params.rounds_p), (8, 56));
    let mut b = builder(params, inputs, vec![p1(); 3], fork)?;
    b.e.next_round();
    b.external_template(TemplateKind::Entry, None)?;
    for round in 0..4 {
        b.e.next_round();
        let kind = if round == 3 {
            TemplateKind::Exit
        } else {
            TemplateKind::Round
        };
        b.external_template(kind, Some(round))?;
    }
    for round in 4..59 {
        b.e.next_round();
        b.internal_round(round, true)?;
    }
    b.e.next_round();
    b.e.comment("Rounds 59..60 (test-only seam)");
    seam(&mut b)?;
    b.e.next_round();
    for round in 61..64 {
        b.e.next_round();
        let kind = if round == 63 {
            TemplateKind::Final
        } else {
            TemplateKind::Round
        };
        b.external_template(kind, Some(round))?;
    }
    b.e.end_line();
    check_values(&b, inputs, 0, step_count(params));
    for (i, &id) in b.state.iter().enumerate() {
        assert_eq!(b.e.top(i)?, id);
        assert_eq!(b.e.bound(id), p1());
    }
    assert_eq!(b.e.top(3)?, b.p());
    assert_eq!((b.e.memory, b.e.loads, b.e.stores, b.e.pops), (0, 0, 0, 0));
    let e = b.e;
    Ok(BuildResult {
        lines: e.lines,
        gas: e.gas,
        bytes: e.bytes,
        max_depth: e.max_depth,
        max_dup: e.max_dup,
        swaps: e.swaps,
        pops: e.pops,
        stores: e.stores,
        loads: e.loads,
        range: b.range,
        state_in_memory: false,
        input_slots: b.input_slots,
        step_bytes: Vec::new(),
        memory: e.memory,
        tables: e.tables,
    })
}

#[test]
fn t3_external_seam_round_constants() {
    let params = generate_params_uncached(3);
    for (round, lane, expected) in [
        (
            58,
            0,
            "0x03326e643580356bf6d44008ae4c042a21ad4880097a5eb38b71e2311bb88f8f",
        ),
        (
            59,
            0,
            "0x268076b0054fb73f67cee9ea0e51e3ad50f27a6434b5dceb5bdde2299910a4c9",
        ),
        (
            60,
            0,
            "0x1acd63c67fbc9ab1626ed93491bda32e5da18ea9d8e4f10178d04aa6f8747ad0",
        ),
        (
            60,
            1,
            "0x19f8a5d670e8ab66c4e3144be58ef6901bf93375e2323ec3ca8c86cd2a28b5a5",
        ),
        (
            60,
            2,
            "0x1c0dc443519ad7a86efa40d2df10a011068193ea51f6c92ae1cfbb5f7b9b6893",
        ),
        (
            61,
            0,
            "0x14b39e7aa4068dbe50fe7190e421dc19fbeab33cb4f6a2c4180e4c3224987d3d",
        ),
        (
            61,
            1,
            "0x1d449b71bd826ec58f28c63ea6c561b7b820fc519f01f021afb1e35e28b0795e",
        ),
        (
            61,
            2,
            "0x1ea2c9a89baaddbb60fa97fe60fe9d8e89de141689d1252276524dc0a9e987fc",
        ),
    ] {
        assert_eq!(field::hex(params.round_constants[round][lane]), expected);
    }
    let used: Vec<&str> = SEAM
        .split_whitespace()
        .filter(|token| matches!(*token, "c59" | "k0" | "k1" | "k2"))
        .collect();
    assert_eq!(used, ["c59", "k1", "k2", "k0"]);
}

#[test]
fn t3_external_seam_bounds_values_and_caller_tail() {
    let params = generate_params_uncached(3);
    let bounds = vec![p1() * u256(2), p1() * u256(2), p1() * u256(5)];
    let mut inputs: Vec<Vec<U256>> = (0..8)
        .map(|mask| {
            bounds
                .iter()
                .enumerate()
                .map(|(i, &v)| if mask & (1 << i) == 0 { U256::ZERO } else { v })
                .collect()
        })
        .collect();
    inputs.push(bounds.iter().map(|&v| v / u256(2)).collect());
    inputs.push(bounds.iter().map(|&v| v - u256(1)).collect());
    for name in ["paris", "osaka", "amsterdam"] {
        for dead in [0, 20, 160] {
            for backing in [false, true] {
                for candidate in [false, true] {
                    let fork = fork(name).unwrap();
                    let mut b = builder(&params, &inputs, bounds.clone(), fork).unwrap();
                    let mut tail: Vec<Id> = (0..=dead)
                        .map(|i| {
                            b.e.alloc(
                                Value::new(
                                    format!("caller{i}"),
                                    UINT256_MAX,
                                    vec![UINT256_MAX - u256(i as u64); inputs.len()],
                                    None,
                                )
                                .unwrap(),
                            )
                        })
                        .collect();
                    if backing {
                        tail.push(b.p());
                    }
                    internal_layout(&mut b, &tail);
                    b.internal_round(58, true).unwrap();
                    assert_eq!(b.e.gas, 109);
                    if candidate {
                        seam(&mut b).unwrap();
                        assert_eq!(b.e.gas, 404);
                        assert_eq!(b.e.depth(), tail.len() + 6);
                        assert_eq!(b.e.top(0).unwrap(), b.state[0]);
                        assert_eq!(b.e.top(2).unwrap(), b.state[1]);
                        assert_eq!(b.e.top(3).unwrap(), b.state[2]);
                    } else {
                        b.internal_round(59, true).unwrap();
                        b.external_template(TemplateKind::Round, Some(60)).unwrap();
                        assert_eq!(b.e.gas, 407);
                        assert_eq!(b.e.depth(), tail.len() + 7);
                    }
                    check_values(&b, &inputs, 59, 62);
                    assert_eq!(b.e.top(1).unwrap(), b.p());
                    let tail_start = if candidate { 6 } else { 7 };
                    assert_eq!(&b.e.from_top()[tail_start..], tail);
                    for &id in &b.state {
                        assert_eq!(b.e.bound(id), p1() * u256(4));
                    }
                    let gas = b.e.gas;
                    b.external_template(TemplateKind::Round, Some(61)).unwrap();
                    assert_eq!(b.e.gas - gas, 189);
                    assert_eq!(b.e.gas, if candidate { 593 } else { 596 });
                    assert_eq!(b.e.swaps, if candidate { 11 } else { 12 });
                    check_values(&b, &inputs, 59, 63);
                    assert_eq!(b.e.top(0).unwrap(), b.state[1]);
                    assert_eq!(b.e.top(1).unwrap(), b.p());
                    assert_eq!(b.e.top(2).unwrap(), b.state[0]);
                    assert_eq!(b.e.top(3).unwrap(), b.state[2]);
                    assert_eq!(&b.e.from_top()[8..], tail);
                    for &id in &b.state {
                        assert_eq!(b.e.bound(id), p1() * u256(4));
                    }
                    assert_eq!(b.e.max_depth, tail.len() + 14);
                    b.external_template(TemplateKind::Round, Some(62)).unwrap();
                    b.external_template(TemplateKind::Final, Some(63)).unwrap();
                    check_values(&b, &inputs, 59, step_count(&params));
                    assert_eq!(b.e.gas, if candidate { 998 } else { 1001 });
                    for (i, &id) in b.state.iter().enumerate() {
                        assert_eq!(b.e.top(i).unwrap(), id);
                        assert_eq!(b.e.bound(id), p1());
                    }
                    assert_eq!(b.e.top(3).unwrap(), b.p());
                    assert_eq!(&b.e.from_top()[10..], tail);
                    assert!(b.e.max_dup <= fork.reach);
                    assert_eq!((b.e.memory, b.e.loads, b.e.stores, b.e.pops), (0, 0, 0, 0));
                }
            }
        }
    }
}

#[test]
fn t3_external_seam_rejects_unsafe_bounds_modulus_and_reach() {
    let params = generate_params_uncached(3);
    let inputs = vec![vec![U256::ZERO; 3]];
    let ab = UINT256_MAX - params.round_constants[59][0];
    let bb = UINT256_MAX - p1() - params.round_constants[60][1];
    let cb = UINT256_MAX - p1() - params.round_constants[60][2];
    for name in ["paris", "osaka", "amsterdam"] {
        let fork = fork(name).unwrap();
        for (a_bound, b_bound, c_bound, valid) in [
            (p1() * u256(2), bb, cb, true),
            (ab, bb, cb, true),
            (ab + u256(1), bb, cb, false),
            (p1() * u256(2), bb + u256(1), cb, false),
            (p1() * u256(2), bb, cb + u256(1), false),
        ] {
            let bounds = vec![a_bound, b_bound, c_bound];
            let mut cases = inputs.clone();
            if valid {
                cases.push(bounds.clone());
            }
            let mut b = builder(&params, &cases, bounds, fork).unwrap();
            internal_layout(&mut b, &[]);
            let result = seam(&mut b);
            if valid {
                result.unwrap();
                assert_eq!(b.e.gas, 295);
                check_values(&b, &cases, 60, 62);
            } else {
                assert!(result.unwrap_err().to_string().contains("add overflow"));
            }
        }
        let bounds = vec![p1() * u256(2), p1() * u256(3), p1() * u256(2)];
        let mut b = builder(&params, &inputs, bounds.clone(), fork).unwrap();
        let wrong =
            b.e.alloc(Value::new("not_prime".to_string(), PRIME, vec![PRIME], None).unwrap());
        b.e.set_stack(&[b.state[0], wrong, b.state[2], b.state[1]]);
        assert!(
            replay(&mut b.e, &params)
                .unwrap_err()
                .to_string()
                .contains("modulus must be PRIME")
        );
        let mut b = builder(&params, &inputs, bounds.clone(), fork).unwrap();
        internal_layout(&mut b, &[]);
        b.e.max_reach = 8;
        assert!(
            seam(&mut b)
                .unwrap_err()
                .to_string()
                .contains("out of reach (dup9)")
        );
        for i in 0..3 {
            let mut outside = vec![vec![U256::ZERO; 3]];
            outside[0][i] = bounds[i] + u256(1);
            assert!(builder(&params, &outside, bounds.clone(), fork).is_err());
        }
    }
}
