use super::*;
use crate::round_constants::generate_params;
use crate::vectors::{Prng, test_inputs};

#[test]
fn interval_sums_reduce_less_and_check_exact_endpoints() {
    let l = PRIME - u256(1);
    for t in [8, 12] {
        let params = generate_params(t);
        let inputs = vec![vec![U256::ZERO; t]];
        let mut b = Builder::new(
            &params,
            &inputs,
            super::super::layout_for(t),
            Mode::Array,
            0,
        )
        .unwrap();
        for i in 0..t + 2 {
            b.p.let_(&format!("local{i}"), &b.p.constant(U256::ZERO))
                .unwrap();
        }
        for steady in [false, true] {
            let values: Vec<_> = (0..t)
                .rev()
                .map(|i| {
                    let bound = if steady && i > 0 { l * u256(2) } else { l };
                    Value::new(format!("state{i}"), bound, vec![bound], None).unwrap()
                })
                .collect();
            let e = b.planned_sum(&values, l).unwrap().expect("reachable tree");
            let expected = values.iter().fold(U256::ZERO, |a, v| add(a, v.vals[0]));
            assert_eq!(e.vals, [expected]);
            assert_eq!(e.bound, l);
            let reductions = match (t, steady) {
                (8, false) => 1,
                (8, true) | (12, false) => 2,
                (12, true) => 3,
                _ => unreachable!(),
            };
            assert_eq!(e.name.matches("addmod(").count(), reductions);
            let (serial, _) = Builder::steps(&values, l);
            assert!(serial.iter().filter(|s| s.reduce).count() > reductions);
        }
        for i in 0..16 {
            b.p.let_(&format!("extra{i}"), &b.p.constant(U256::ZERO))
                .unwrap();
        }
        let values: Vec<_> = (0..t)
            .rev()
            .map(|i| Value::new(format!("state{i}"), l, vec![l], None).unwrap())
            .collect();
        assert!(b.planned_sum(&values, l).unwrap().is_none());
    }
}

#[test]
fn sum_cap_and_exact_reach_boundaries() {
    let params = generate_params(12);
    let inputs = vec![vec![U256::ZERO; 12]];
    let mut b = Builder::new(
        &params,
        &inputs,
        super::super::layout_for(12),
        Mode::Array,
        0,
    )
    .unwrap();
    for i in 0..14 {
        b.p.let_(&format!("local{i}"), &b.p.constant(U256::ZERO))
            .unwrap();
    }
    let v = Value::new("state0".to_string(), UINT256_MAX, vec![UINT256_MAX], None).unwrap();
    assert!(b.reachable(&v, 2));
    assert!(!b.reachable(&v, 3));
    assert!(b.chain_sum(&[v], "sum", PRIME - u256(1)).is_err());
}

#[test]
fn all_yul_widths_check_full_word_inputs() {
    let mut rng = Prng::new(0x73756d74726565);
    for t in [2, 3, 4, 8, 12] {
        let params = generate_params(t);
        let mut inputs = test_inputs(t);
        for value in [PRIME, PRIME + u256(1), UINT256_MAX, UINT256_MAX - u256(1)] {
            inputs.push(vec![value; t]);
        }
        for _ in 0..64 {
            inputs.push((0..t).map(|_| rng.next_u256()).collect());
        }
        let layout = super::super::layout_for(t);
        let mode = if t == 4 { Mode::Hash } else { Mode::Array };
        let result = build_permutation(&params, &inputs, layout, mode, 0).unwrap();
        assert!(!result.lines.is_empty());
    }
}
