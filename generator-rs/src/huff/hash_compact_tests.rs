use super::*;
use crate::huff::fork::fork;
use crate::huff::render::{hash_entry, hash_entry_compact};
use crate::round_constants::generate_params;

#[test]
fn compact_hash1_layout_and_shared_fallback() {
    let params = generate_params(4);
    for name in ["paris", "osaka", "amsterdam"] {
        let fork = fork(name).unwrap();
        let prologues: Vec<_> = (1..=3)
            .map(|n| {
                let inputs =
                    [U256::ZERO, p1(), PRIME, PRIME + u256(1), UINT256_MAX].map(|v| vec![v; n]);
                build_hash_prologue(&params, &inputs, fork).unwrap()
            })
            .collect();
        let rounds = build_hash_rounds(&params, &prologues, fork.code_size - 1000, fork).unwrap();
        let inputs = [U256::ZERO, p1(), PRIME, PRIME + u256(1), UINT256_MAX].map(|v| vec![v]);
        let (p, r) = build_compact_hash1(&params, &inputs, fork, &rounds.opts).unwrap();
        assert_eq!(p.dead, 2);
        assert_eq!(prologues[0].dead, 3);
        assert_eq!(p.depth + 1, prologues[0].depth);
        assert_eq!(p.outputs, prologues[0].outputs);
        assert_eq!(p.bounds, prologues[0].bounds);
        assert_eq!(
            p.gas + fork.push0.then_some(2).unwrap_or(3),
            prologues[0].gas
        );
        let costs = (rounds.result.gas, rounds.result.bytes, rounds.result.memory);
        let normal = hash_entry(fork, &prologues, costs).unwrap();
        let compact = hash_entry_compact(fork, &prologues, costs, Some((&p, &r))).unwrap();
        if name == "amsterdam" {
            assert_eq!(compact.gas, [11835, 11879, 11919]);
            assert_eq!(compact.bytes, 64255);
            assert_eq!(normal.gas[0] - compact.gas[0], 2);
            assert!(
                compact
                    .lines
                    .iter()
                    .any(|l| l.contains("POSEIDON2_HASH1_ROUNDS()"))
            );
        } else {
            assert_eq!(compact.gas, normal.gas);
            assert_eq!(compact.bytes, normal.bytes);
            assert_eq!(compact.lines, normal.lines);
        }
        assert!(
            build_hash_rounds(&params, &[prologues[0].clone(), p], fork.code_size, fork).is_err()
        );
    }
}
