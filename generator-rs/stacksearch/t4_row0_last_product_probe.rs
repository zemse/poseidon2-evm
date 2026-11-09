// Checked replay and compiled calls for the last product of the t4 hash row.
use super::*;
use crate::field::{self, PRIME, UINT256_MAX, u256};
use crate::huff::emitter::{Emitter, Operand};
use crate::huff::fork::fork;
use crate::value::{Op, Value, apply_op};

const SBOX: &str = "c0 add dup2 dup1 dup3 dup1 mulmod dup1 mulmod mulmod";

fn replay(name: &str, candidate: bool, c0: U256, tail_len: usize) -> (u64, Vec<Vec<U256>>) {
    let l = PRIME - u256(1);
    let corners: Vec<_> = [U256::ZERO, l, u256(3) * l]
        .into_iter()
        .flat_map(|r| [U256::ZERO, l, u256(3) * l, u256(4) * l].map(|a| (r, a)))
        .collect();
    let mut e = Emitter::new(
        corners.len(),
        fork(name).unwrap(),
        Default::default(),
        false,
        true,
    );
    let p = e.p;
    let r = e.alloc(
        Value::new(
            "R".into(),
            u256(3) * l,
            corners.iter().map(|v| v.0).collect(),
            None,
        )
        .unwrap(),
    );
    let a = e.alloc(
        Value::new(
            "a".into(),
            u256(4) * l,
            corners.iter().map(|v| v.1).collect(),
            None,
        )
        .unwrap(),
    );
    let mut stock = vec![r, p, a, p];
    for i in 0..3 + tail_len {
        let value = u256(100 + i as u64);
        stock.push(
            e.alloc(
                Value::new(
                    format!("sentinel{i}"),
                    value,
                    vec![value; corners.len()],
                    None,
                )
                .unwrap(),
            ),
        );
    }
    e.set_stack(&stock);
    let ops = if candidate {
        format!("5 dup3 dup5 {SBOX} mul addmod")
    } else {
        format!("dup2 5 dup2 dup6 {SBOX} mulmod add mod")
    };
    for token in ops.split_whitespace() {
        if let Some(n) = token.strip_prefix("dup") {
            let n: usize = n.parse().unwrap();
            let id = e.top(n - 1).unwrap();
            assert!(e.find(id) <= 6, "suffix must not read the caller tail");
            e.dup(id).unwrap();
        } else if token == "5" || token == "c0" {
            e.push(if token == "5" { u256(5) } else { c0 }, None)
                .unwrap();
        } else {
            let op = match token {
                "add" => Op::Add,
                "mul" => Op::Mul,
                "addmod" => Op::Addmod,
                "mulmod" => Op::Mulmod,
                "mod" => Op::Mod,
                _ => panic!("unexpected opcode {token}"),
            };
            let operands: Vec<_> = (0..op.arity())
                .map(|i| Operand::Inplace(e.top(i).unwrap()))
                .collect();
            e.compute(op, &operands, token).unwrap();
        }
    }
    let out = e.top(0).unwrap();
    assert_eq!(&e.from_top()[1..], &stock[2..]);
    assert_eq!(e.bound(out), l);
    assert_eq!(
        (e.stores, e.loads, e.pops, e.swaps, e.memory),
        (0, 0, 0, 0, 0)
    );
    assert_eq!(e.top(2).unwrap(), p);
    for (i, &(r, a)) in corners.iter().enumerate() {
        let y = field::add(a, c0);
        let y2 = field::mul(y, y);
        let x = field::mul(field::mul(y2, y2), y);
        assert_eq!(e.value(out).vals[i], field::add(r, field::mul(u256(5), x)));
    }
    (
        e.gas,
        e.from_top()
            .iter()
            .map(|&v| e.value(v).vals.clone())
            .collect(),
    )
}

#[test]
fn t4_row0_last_product_bounds() {
    let l = PRIME - u256(1);
    let five_l = l.checked_mul(u256(5)).expect("5(P-1) fits uint256");
    println!("P={PRIME:#x}, 5(P-1)={five_l:#x}, MAX={UINT256_MAX:#x}");
    assert!(five_l <= UINT256_MAX);
    assert!(l.checked_mul(u256(6)).is_none());
    let threshold = UINT256_MAX / u256(5);
    let value = |name: &str, bound, actual, constant| {
        Value::new(name.into(), bound, vec![actual], constant).unwrap()
    };
    let five = value("five", u256(5), u256(5), Some(u256(5)));
    let p = value("P", PRIME, PRIME, Some(PRIME));
    for x in [U256::ZERO, u256(1), l, threshold] {
        let x = value("x", threshold, x, None);
        let product = apply_op(Op::Mul, &[&x, &five], "5x".into(), 1).unwrap();
        assert_eq!(product.bound, UINT256_MAX);
    }
    let unsafe_x = value("unsafe x", threshold + u256(1), U256::ZERO, None);
    assert!(
        apply_op(Op::Mul, &[&unsafe_x, &five], "5x".into(), 1)
            .unwrap_err()
            .to_string()
            .contains("mul overflow")
    );
    let product = value("5x", five_l, U256::ZERO, None);
    let acc = value("R", u256(3) * l, U256::ZERO, None);
    assert!(
        apply_op(Op::Add, &[&product, &acc], "sum".into(), 1)
            .unwrap_err()
            .to_string()
            .contains("add overflow")
    );
    assert_eq!(
        apply_op(Op::Addmod, &[&product, &acc, &p], "z".into(), 1)
            .unwrap()
            .bound,
        l
    );
    let fake_p = value("not a PRIME identity", PRIME, PRIME, None);
    assert!(apply_op(Op::Addmod, &[&product, &acc, &fake_p], "z".into(), 1).is_err());
    let wrong_p = value("wrong PRIME", l, l, Some(l));
    assert!(apply_op(Op::Addmod, &[&product, &acc, &wrong_p], "z".into(), 1).is_err());
    for x in [U256::ZERO, u256(1), l] {
        for r in [U256::ZERO, l, u256(3) * l] {
            let x = value("x", l, x, None);
            let r = value("R", u256(3) * l, r, None);
            let product = apply_op(Op::Mul, &[&x, &five], "5x".into(), 1).unwrap();
            assert_eq!(product.bound, five_l);
            let out = apply_op(Op::Addmod, &[&product, &r, &p], "z".into(), 1).unwrap();
            assert_eq!(
                out.vals[0],
                field::add(field::mul(x.vals[0], u256(5)), r.vals[0])
            );
            assert!(out.vals[0] < PRIME);
        }
    }
    let c0 = generate_params(4).round_constants[63][0];
    for name in ["amsterdam", "osaka", "paris"] {
        for constant in [c0, l, U256::ZERO] {
            for tail in [0, 3, 120] {
                let (before, old) = replay(name, false, constant, tail);
                let (after, new) = replay(name, true, constant, tail);
                assert_eq!(old, new);
                let discount = u64::from(constant.is_zero() && name != "paris");
                assert_eq!((before, after), (73 - discount, 67 - discount));
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RowProducts {
    Original,
    Last,
    Both,
}

const ROWS: [RowProducts; 3] = [RowProducts::Original, RowProducts::Last, RowProducts::Both];
// The production row runs lane 0 first on [s0, P] in place: three gas below `Both`.
const IN_PLACE_GAS: u64 = 248;

impl RowProducts {
    fn cost(self) -> (u64, usize) {
        match self {
            Self::Original => (263, 193),
            Self::Last => (257, 191),
            Self::Both => (251, 190),
        }
    }

    fn lines(self, constants: &[U256]) -> [String; 4] {
        let sbox = |i: usize| SBOX.replace("c0", &format!("{:#066x}", constants[i]));
        [
            match self {
                Self::Both => format!("dup2 0x3 dup2 dup8 {} mul", sbox(3)),
                _ => format!("dup2 dup1 0x3 dup2 dup9 {} mulmod", sbox(3)),
            },
            format!("dup2 dup7 {} add", sbox(2)),
            format!("dup2 0x7 dup2 dup8 {} mulmod add", sbox(1)),
            match self {
                Self::Original => format!("dup2 0x5 dup2 dup6 {} mulmod add mod", sbox(0)),
                _ => format!("0x5 dup3 dup5 {} mul addmod", sbox(0)),
            },
        ]
    }
}

#[test]
fn t4_row0_coefficient3_bounds() {
    let l = PRIME - u256(1);
    let value = |bound, actual| Value::new("v".into(), bound, vec![actual], None).unwrap();
    let p = Value::new("P".into(), PRIME, vec![PRIME], Some(PRIME)).unwrap();
    let three = value(u256(3), u256(3));
    let five = value(u256(5), u256(5));
    let seven = value(u256(7), u256(7));
    let five_l = l.checked_mul(u256(5)).expect("5L fits");
    assert!(l.checked_mul(u256(6)).is_none());
    let threshold = UINT256_MAX / u256(3);
    assert_eq!(threshold.checked_mul(u256(3)), Some(UINT256_MAX));
    for bound in [threshold - u256(1), threshold] {
        for actual in [U256::ZERO, u256(1), l, bound] {
            let x = value(bound, actual);
            let product = apply_op(Op::Mul, &[&x, &three], "3x".into(), 1).unwrap();
            assert_eq!(product.bound, bound * u256(3));
        }
    }
    let unsafe_x = value(threshold + u256(1), U256::ZERO);
    assert!(
        apply_op(Op::Mul, &[&unsafe_x, &three], "3x".into(), 1)
            .unwrap_err()
            .to_string()
            .contains("mul overflow")
    );
    let x = value(l, U256::ZERO);
    assert!(apply_op(Op::Mul, &[&x, &seven], "7x".into(), 1).is_err());
    for multiple in [3, 4, 5] {
        let a = value(u256(multiple) * l, U256::ZERO);
        let b = value(UINT256_MAX - a.bound, U256::ZERO);
        assert_eq!(
            apply_op(Op::Add, &[&a, &b], "sum".into(), 1).unwrap().bound,
            UINT256_MAX
        );
        let unsafe_b = value(b.bound + u256(1), U256::ZERO);
        assert!(apply_op(Op::Add, &[&a, &unsafe_b], "sum".into(), 1).is_err());
    }
    for modulus in [
        value(PRIME, PRIME),
        Value::new("wrong P".into(), l, vec![l], Some(l)).unwrap(),
    ] {
        for op in [Op::Addmod, Op::Mulmod] {
            assert!(apply_op(op, &[&x, &x, &modulus], "out".into(), 1).is_err());
        }
        assert!(apply_op(Op::Mod, &[&x, &modulus], "out".into(), 1).is_err());
    }
    for actual in [U256::ZERO, l] {
        let acc = value(
            five_l,
            if actual.is_zero() {
                actual
            } else {
                five_l - u256(6)
            },
        );
        let last = value(
            l,
            if actual.is_zero() {
                actual
            } else {
                l - u256(4)
            },
        );
        assert!(
            apply_op(Op::Add, &[&acc, &last], "unsafe hybrid".into(), 1)
                .unwrap_err()
                .to_string()
                .contains("add overflow")
        );
    }
    assert!((five_l - u256(6)).checked_add(l - u256(4)).is_none());
    let product = value(five_l, U256::ZERO);
    assert!(apply_op(Op::Add, &[&product, &product], "final sum".into(), 1).is_err());
    assert_eq!(
        apply_op(Op::Addmod, &[&product, &product, &p], "out".into(), 1)
            .unwrap()
            .bound,
        l
    );
    for bound in [l * u256(2), l * u256(3)] {
        assert!(Value::new("over bound".into(), bound, vec![bound + u256(1)], None).is_err());
    }
    for x0 in [U256::ZERO, u256(1), l] {
        for x1 in [U256::ZERO, u256(1), l] {
            for x2 in [U256::ZERO, u256(1), l] {
                for x3 in [U256::ZERO, u256(1), l] {
                    let xs = [x0, x1, x2, x3].map(|x| value(l, x));
                    let want = field::add(
                        field::add(field::mul(x0, u256(5)), field::mul(x1, u256(7))),
                        field::add(x2, field::mul(x3, u256(3))),
                    );
                    for row in ROWS {
                        let term3 = if row == RowProducts::Both {
                            apply_op(Op::Mul, &[&xs[3], &three], "3x3".into(), 1)
                        } else {
                            apply_op(Op::Mulmod, &[&xs[3], &three, &p], "3x3".into(), 1)
                        }
                        .unwrap();
                        let prefix = if row == RowProducts::Both { 3 } else { 1 };
                        assert_eq!(term3.bound, l * u256(prefix));
                        let acc = apply_op(Op::Add, &[&term3, &xs[2]], "acc".into(), 1).unwrap();
                        assert_eq!(acc.bound, l * u256(prefix + 1));
                        let term1 =
                            apply_op(Op::Mulmod, &[&xs[1], &seven, &p], "7x1".into(), 1).unwrap();
                        let acc = apply_op(Op::Add, &[&acc, &term1], "acc".into(), 1).unwrap();
                        assert_eq!(acc.bound, l * u256(prefix + 2));
                        let out = if row == RowProducts::Original {
                            let term0 = apply_op(Op::Mulmod, &[&xs[0], &five, &p], "5x0".into(), 1)
                                .unwrap();
                            let acc = apply_op(Op::Add, &[&acc, &term0], "acc".into(), 1).unwrap();
                            assert_eq!(acc.bound, l * u256(4));
                            apply_op(Op::Mod, &[&acc, &p], "out".into(), 1).unwrap()
                        } else {
                            let term0 =
                                apply_op(Op::Mul, &[&xs[0], &five], "5x0".into(), 1).unwrap();
                            assert_eq!(term0.bound, five_l);
                            apply_op(Op::Addmod, &[&term0, &acc, &p], "out".into(), 1).unwrap()
                        };
                        assert_eq!(out.bound, l);
                        assert_eq!(out.vals, vec![want]);
                        assert!(out.vals[0] < PRIME);
                    }
                }
            }
        }
    }
}

#[test]
fn t4_row0_complete_replay() {
    use crate::huff::emitter::{push_bytes, push_gas};
    let l = PRIME - u256(1);
    let bounds = [3, 2, 3, 2].map(|n| l * u256(n));
    let real = generate_params(4).round_constants[63].clone();
    for name in ["amsterdam", "osaka", "paris"] {
        let fork = fork(name).unwrap();
        for constants in [&real[..], &[U256::ZERO; 4][..], &[l; 4][..]] {
            let mut vectors = Vec::new();
            for a in [U256::ZERO, l, bounds[0]] {
                for b in [U256::ZERO, l, bounds[1]] {
                    for c in [U256::ZERO, l, bounds[2]] {
                        for d in [U256::ZERO, l, bounds[3]] {
                            vectors.push([a, b, c, d]);
                        }
                    }
                }
            }
            vectors.push(std::array::from_fn(|i| l - constants[i]));
            for tail_len in [0, 3, 120] {
                let mut outputs = Vec::new();
                for row in ROWS {
                    let mut e = Emitter::new(vectors.len(), fork, Default::default(), false, true);
                    let p = e.p;
                    let state: Vec<_> = bounds
                        .iter()
                        .enumerate()
                        .map(|(i, &bound)| {
                            e.alloc(
                                Value::new(
                                    format!("a{i}"),
                                    bound,
                                    vectors.iter().map(|v| v[i]).collect(),
                                    None,
                                )
                                .unwrap(),
                            )
                        })
                        .collect();
                    let mut stock = vec![state[0], p, state[1], state[2], state[3]];
                    for i in 0..tail_len {
                        let v = if i == 0 { PRIME } else { u256(100 + i as u64) };
                        stock.push(
                            e.alloc(
                                Value::new(format!("caller{i}"), v, vec![v; vectors.len()], None)
                                    .unwrap(),
                            ),
                        );
                    }
                    e.set_stack(&stock);
                    for (line, text) in row.lines(constants).iter().enumerate() {
                        for token in text.split_whitespace() {
                            if let Some(n) = token.strip_prefix("dup") {
                                let n: usize = n.parse().unwrap();
                                assert!(n <= if row == RowProducts::Both { 8 } else { 9 });
                                let id = e.top(n - 1).unwrap();
                                assert!(!stock[5..].contains(&id), "read caller tail");
                                e.dup(id).unwrap();
                            } else if let Some(hex) = token.strip_prefix("0x") {
                                e.push(U256::from_str_radix(hex, 16).unwrap(), None)
                                    .unwrap();
                            } else {
                                let op = match token {
                                    "add" => Op::Add,
                                    "mul" => Op::Mul,
                                    "addmod" => Op::Addmod,
                                    "mulmod" => Op::Mulmod,
                                    "mod" => Op::Mod,
                                    _ => panic!("unexpected opcode {token}"),
                                };
                                if matches!(op, Op::Addmod | Op::Mulmod | Op::Mod) {
                                    assert_eq!(e.top(op.arity() - 1).unwrap(), p);
                                }
                                let operands: Vec<_> = (0..op.arity())
                                    .map(|i| Operand::Inplace(e.top(i).unwrap()))
                                    .collect();
                                let out = e.compute(op, &operands, token).unwrap();
                                if op == Op::Mul {
                                    assert_eq!(
                                        e.bound(out),
                                        l * u256(if line == 0 { 3 } else { 5 })
                                    );
                                }
                                if matches!(op, Op::Mulmod | Op::Addmod | Op::Mod) {
                                    assert_eq!(e.bound(out), l);
                                }
                            }
                        }
                        let expected = if line == 3 {
                            1
                        } else {
                            line as u64 + if row == RowProducts::Both { 3 } else { 1 }
                        };
                        assert_eq!(e.bound(e.top(0).unwrap()), l * u256(expected));
                    }
                    assert_eq!(&e.from_top()[1..], &stock);
                    assert_eq!(e.top(2).unwrap(), p);
                    assert_eq!(e.max_depth, stock.len() + 10);
                    assert!(e.max_depth <= 1024);
                    assert_eq!(
                        (e.stores, e.loads, e.pops, e.swaps, e.memory),
                        (0, 0, 0, 0, 0)
                    );
                    let (gas, bytes) = row.cost();
                    assert_eq!(
                        e.gas,
                        gas - constants
                            .iter()
                            .map(|&c| 3 - push_gas(c, &fork))
                            .sum::<u64>()
                    );
                    assert_eq!(
                        e.bytes,
                        bytes
                            - constants
                                .iter()
                                .map(|&c| 33 - push_bytes(c, &fork))
                                .sum::<usize>()
                    );
                    let out = e.value(e.top(0).unwrap());
                    for (i, a) in vectors.iter().enumerate() {
                        let want = a.iter().zip(constants).zip([5, 7, 1, 3]).fold(
                            U256::ZERO,
                            |sum, ((&a, &c), k)| {
                                let y = field::add(a, c);
                                let y2 = field::mul(y, y);
                                let x = field::mul(field::mul(y2, y2), y);
                                field::add(sum, field::mul(x, u256(k)))
                            },
                        );
                        assert_eq!(out.vals[i], want);
                        assert!(out.vals[i] < PRIME);
                    }
                    assert_eq!(*out.vals.last().unwrap(), PRIME - u256(16));
                    outputs.push(out.vals.clone());
                }
                assert_eq!(outputs[0], outputs[1]);
                assert_eq!(outputs[1], outputs[2]);
            }
        }
    }
}

fn expanded_inputs() -> Vec<Vec<U256>> {
    let mut standard = inputs(4);
    let mut rng = Prng::new(SEED ^ 0x7464_726f_7730);
    while standard.len() < 30 {
        standard.push((0..4).map(|_| rng.next_u256()).collect());
    }
    assert_eq!(standard.len(), 30);
    for x in [
        U256::ZERO,
        u256(1),
        PRIME - u256(1),
        PRIME,
        PRIME + u256(1),
        UINT256_MAX,
    ] {
        standard.push(vec![x; 4]);
    }
    for i in 0..4 {
        let mut single = vec![U256::ZERO; 4];
        single[i] = UINT256_MAX;
        standard.push(single);
        let mut mixed = vec![UINT256_MAX, PRIME, PRIME - u256(1), U256::ZERO];
        mixed.rotate_left(i);
        standard.push(mixed);
    }
    standard
}

#[test]
fn t4_row0_last_product_compiled() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let params = generate_params(4);
    let constants = &params.round_constants[63];
    let vectors = expanded_inputs();
    let mut abi = Vec::new();
    for len in [0, 1, 3, 4, 5, 35, 36, 37, 67, 68, 69, 99, 100, 101, 132] {
        for pattern in 0..3 {
            for selector in [[0; 4], [0xde, 0xad, 0xbe, 0xef]] {
                let mut data: Vec<u8> = (0..len)
                    .map(|i| match pattern {
                        0 => 0,
                        1 => 255,
                        _ => ((i * 37 + len) % 256) as u8,
                    })
                    .collect();
                for (byte, sel) in data.iter_mut().take(4).zip(selector) {
                    *byte = sel;
                }
                abi.push(data);
            }
        }
    }
    for name in ["amsterdam", "osaka", "paris"] {
        let fork = fork(name).unwrap();
        let width = super::super::generate(4, &fork).unwrap();
        let Target::Hash {
            path,
            gas,
            entry,
            source,
            entry_gas,
            ..
        } = &width.target
        else {
            panic!("expected t4 hashes");
        };
        let mut files: HashMap<String, String> = width
            .files()
            .map(|(p, s)| (p.to_string(), s.to_string()))
            .collect();
        files.insert(entry.clone(), source.clone());
        let production = files[path].clone();
        let marker = "// Round 63 (external, s0' only)";
        assert_eq!(production.matches(marker).count(), 1);
        let (prefix, last) = production.split_once(marker).unwrap();
        let (body, suffix) = last.split_once("\n}").unwrap();
        let actual = body
            .lines()
            .flat_map(|line| line.split("//").next().unwrap().split_whitespace())
            .collect::<Vec<_>>()
            .join(" ");
        let lane0 = format!(
            "{} 0x5 mul",
            SBOX.replace("c0", &format!("{:#066x}", constants[0]))
        );
        assert!(
            actual.starts_with(&lane0) && actual.ends_with(" swap2 addmod"),
            "{actual}"
        );
        let production_bytes: usize = actual
            .split_whitespace()
            .map(|token| match token {
                "dupn" | "swapn" => 2,
                "[PRIME]" => 33,
                _ if token.starts_with("0x") => 1 + (token.len() - 1) / 2,
                _ if token.parse::<usize>().is_ok() => 0,
                _ => 1,
            })
            .sum();
        let baseline = Arc::new(Sources {
            root: root.clone(),
            files: files.clone(),
        });
        let generated = compile(&baseline, path, &fork).unwrap();
        let raw_baseline = compile(&baseline, entry, &fork).unwrap();
        let public_path = path.replace("Poseidon2.huff", "Permutation.huff");
        let public_source = &files[&public_path];
        println!(
            "{name} public identity: source {}, raw runtime {}, raw initcode {}",
            keccak256(public_source.as_bytes()),
            keccak256(&raw_baseline.runtime),
            keccak256(&raw_baseline.initcode)
        );
        let mut results = Vec::new();
        for row in ROWS {
            let label = format!("{row:?}");
            let text = format!(
                "{prefix}{marker}\n    {}\n\n}}{suffix}",
                row.lines(constants).join("\n    ")
            );
            let mut trial = files.clone();
            trial.insert(path.clone(), text);
            assert_eq!(&trial[&public_path], public_source);
            let sources = Arc::new(Sources {
                root: root.clone(),
                files: trial,
            });
            let code = compile(&sources, path, &fork).unwrap();
            let bytes = code.runtime.len();
            assert_eq!(
                bytes,
                generated.runtime.len() + row.cost().1 - production_bytes
            );
            assert!(bytes <= fork.code_size);
            assert!(code.initcode.len() <= fork.initcode_size);
            let mut chain = Chain::new(&fork);
            let to = chain.deploy(code.initcode).unwrap();
            let mut costs = [Vec::new(), Vec::new(), Vec::new()];
            let mut outputs = Vec::new();
            for input in &vectors {
                for (n, signature) in HASH_SIGNATURES.iter().enumerate() {
                    let args = &input[..n + 1];
                    let mut data = keccak256(signature)[..4].to_vec();
                    data.extend(words(args));
                    let (out, spent) = chain.call(to, data, &[]).unwrap();
                    assert_eq!(out.len(), 32);
                    let word = U256::from_be_slice(&out);
                    assert!(word < PRIME);
                    assert_eq!(word, hash_sponge(&params, args));
                    costs[n].push(spent);
                    outputs.push(out);
                }
            }
            let measured = costs.map(|v| same_gas(&v, &label).unwrap());
            assert_eq!(measured, gas.map(|g| g + row.cost().0 - IN_PLACE_GAS));
            for data in &abi {
                let n = match data.len().cmp(&68) {
                    std::cmp::Ordering::Less => 1,
                    std::cmp::Ordering::Equal => 2,
                    std::cmp::Ordering::Greater => 3,
                };
                let args: Vec<_> = (0..n)
                    .map(|i| {
                        let word: [u8; 32] =
                            std::array::from_fn(|j| data.get(4 + 32 * i + j).copied().unwrap_or(0));
                        U256::from_be_bytes(word)
                    })
                    .collect();
                let (out, spent) = chain.call(to, data.clone(), &[]).unwrap();
                assert_eq!(out.len(), 32);
                let word = U256::from_be_slice(&out);
                assert!(word < PRIME);
                assert_eq!(word, hash_sponge(&params, &args));
                assert_eq!(spent, measured[n - 1]);
                outputs.push(out);
            }
            let raw = compile(&sources, entry, &fork).unwrap();
            assert_eq!(raw.runtime, raw_baseline.runtime);
            assert_eq!(raw.initcode, raw_baseline.initcode);
            assert!(raw.runtime.len() <= fork.code_size);
            assert!(raw.initcode.len() <= fork.initcode_size);
            let raw_to = chain.deploy(raw.initcode).unwrap();
            for input in &vectors {
                let (out, spent) = chain.call(raw_to, words(input), &[]).unwrap();
                assert_eq!(out.len(), 128);
                let words = from_words(&out);
                assert!(words.iter().all(|&w| w < PRIME));
                let reduced: Vec<_> = input.iter().copied().map(reduce).collect();
                assert_eq!(words, permutation(&params, &reduced));
                assert_eq!(spent, *entry_gas);
            }
            println!(
                "{name} {label}: {} calls per hash arity and raw permutation, {} ABI calls, {bytes} hash runtime bytes, hashes {measured:?}, raw {entry_gas}, model difference 0",
                vectors.len(),
                abi.len()
            );
            results.push((measured, bytes, outputs));
        }
        for pair in results.windows(2) {
            for (before, after) in pair[0].0.iter().zip(&pair[1].0) {
                assert_eq!(before - after, 6);
            }
            assert_eq!(pair[0].2, pair[1].2);
        }
        assert_eq!(results[0].1 - results[1].1, 2);
        assert_eq!(results[1].1 - results[2].1, 1);
        for (before, after) in results[0].0.iter().zip(&results[2].0) {
            assert_eq!(before - after, 12);
        }
    }
}
