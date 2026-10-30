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
    let c0 = params.round_constants[63][0];
    let vectors = expanded_inputs();
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
        let candidate = files[path].clone();
        let marker = "// Round 63 (external, s0' only)";
        assert_eq!(candidate.matches(marker).count(), 1);
        let (prefix, last) = candidate.split_once(marker).unwrap();
        let mut lines: Vec<_> = last.lines().map(str::to_string).collect();
        let i = lines
            .iter()
            .position(|line| line.contains(&format!("{c0:#066x}")))
            .unwrap();
        let expected = format!(
            "0x5 dup3 dup5 {c0:#066x} add dup2 dup1 dup3 dup1 mulmod dup1 mulmod mulmod mul addmod"
        );
        let actual = lines[i]
            .split("//")
            .next()
            .unwrap()
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ");
        assert_eq!(actual, expected);
        assert!(lines[i + 1].trim().is_empty());
        lines[i] = format!(
            "    dup2 0x5 dup2 dup6 {c0:#066x} add dup2 dup1 dup3 dup1 mulmod dup1 mulmod mulmod mulmod add"
        );
        lines.insert(i + 1, "    mod".to_string());
        let original = format!("{prefix}{marker}{}\n", lines.join("\n"));
        let mut results = Vec::new();
        for (label, text, extra) in [("baseline", original, 6), ("candidate", candidate, 0)] {
            let mut trial = files.clone();
            trial.insert(path.clone(), text);
            let sources = Arc::new(Sources {
                root: root.clone(),
                files: trial,
            });
            let code = compile(&sources, path, &fork).unwrap();
            let bytes = code.runtime.len();
            let mut chain = Chain::new(&fork);
            let to = chain.deploy(code.initcode).unwrap();
            let mut costs = [Vec::new(), Vec::new(), Vec::new()];
            for input in &vectors {
                for (n, signature) in HASH_SIGNATURES.iter().enumerate() {
                    let args = &input[..n + 1];
                    let mut data = keccak256(signature)[..4].to_vec();
                    data.extend(words(args));
                    let (out, spent) = chain.call(to, data, &[]).unwrap();
                    assert_eq!(out.len(), 32);
                    assert_eq!(U256::from_be_slice(&out), hash_sponge(&params, args));
                    costs[n].push(spent);
                }
            }
            let measured = costs.map(|v| same_gas(&v, label).unwrap());
            assert_eq!(measured, gas.map(|g| g + extra));
            let raw = compile(&sources, entry, &fork).unwrap();
            let raw_to = chain.deploy(raw.initcode).unwrap();
            for input in &vectors {
                let (out, spent) = chain.call(raw_to, words(input), &[]).unwrap();
                let reduced: Vec<_> = input.iter().copied().map(reduce).collect();
                assert_eq!(from_words(&out), permutation(&params, &reduced));
                assert_eq!(spent, *entry_gas);
            }
            println!(
                "{name} {label}: {} calls per hash arity and raw permutation, {bytes} hash runtime bytes, hashes {measured:?}, raw {entry_gas}, model difference 0",
                vectors.len()
            );
            results.push(measured);
        }
        for (before, after) in results[0].iter().zip(&results[1]) {
            assert_eq!(before - after, 6);
        }
    }
}
