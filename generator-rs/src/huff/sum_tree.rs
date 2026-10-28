// Interval trees of ADD / ADDMOD, with exact inclusive bounds. The leaf
// order is fixed; PRIME is placed before the operands of each ADDMOD.
// Costs assume three-gas leaf/PRIME copies, ADD at 3 and ADDMOD at 8 on
// every supported fork. Reach, memory loads and code size are not modelled:
// the emitter checks and prices the chosen tree in its actual layout.
// The cache key is the complete ordered bound vector and the output cap.

use std::collections::{BTreeMap, HashMap};
use std::sync::{Arc, Mutex, OnceLock};

use crate::field::{PRIME, U256, u256};

pub(super) enum Node {
    Leaf(usize),
    Pair {
        left: Arc<Plan>,
        right: Arc<Plan>,
        reduce: bool,
    },
}

pub(super) struct Plan {
    pub node: Node,
    pub bound: U256,
    pub gas: u64,
    /// peak of this tree, not minimized across discarded equal-gas bounds
    pub peak: usize,
}

type Cache = HashMap<(Vec<U256>, U256), Option<Arc<Plan>>>;
static CACHE: OnceLock<Mutex<Cache>> = OnceLock::new();

pub(super) fn plan(bounds: &[U256], cap: U256) -> Option<Arc<Plan>> {
    let key = (bounds.to_vec(), cap);
    let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    if let Some(found) = cache.lock().expect("sum tree cache").get(&key) {
        return found.clone();
    }
    let found = build(bounds, cap);
    cache
        .lock()
        .expect("sum tree cache")
        .insert(key, found.clone());
    found
}

fn build(bounds: &[U256], cap: U256) -> Option<Arc<Plan>> {
    let n = bounds.len();
    if n == 0 {
        return None;
    }
    let mut cells: Vec<Vec<Vec<Arc<Plan>>>> = vec![vec![Vec::new(); n + 1]; n];
    for (i, &bound) in bounds.iter().enumerate() {
        cells[i][i + 1].push(Arc::new(Plan {
            node: Node::Leaf(i),
            bound,
            gas: 3,
            peak: 1,
        }));
    }
    for len in 2..=n {
        for start in 0..=n - len {
            let end = start + len;
            let mut choices: BTreeMap<U256, Arc<Plan>> = BTreeMap::new();
            for (mid, row) in cells.iter().enumerate().take(end).skip(start + 1) {
                for left in &cells[start][mid] {
                    for right in &row[end] {
                        for reduce in [false, true] {
                            let bound = if reduce {
                                PRIME - u256(1)
                            } else {
                                let Some(sum) = left.bound.checked_add(right.bound) else {
                                    continue;
                                };
                                sum
                            };
                            let gas = left.gas + right.gas + if reduce { 11 } else { 3 };
                            let extra = usize::from(reduce);
                            let peak = (left.peak + extra).max(right.peak + 1 + extra);
                            if choices
                                .get(&bound)
                                .is_none_or(|old| (gas, peak) < (old.gas, old.peak))
                            {
                                choices.insert(
                                    bound,
                                    Arc::new(Plan {
                                        node: Node::Pair {
                                            left: left.clone(),
                                            right: right.clone(),
                                            reduce,
                                        },
                                        bound,
                                        gas,
                                        peak,
                                    }),
                                );
                            }
                        }
                    }
                }
            }
            let mut cheapest = u64::MAX;
            for (_, choice) in choices {
                if choice.gas < cheapest {
                    cheapest = choice.gas;
                    cells[start][end].push(choice);
                }
            }
        }
    }
    cells[0][n]
        .iter()
        .filter(|p| p.bound <= cap)
        .min_by_key(|p| (p.gas, p.peak, p.bound))
        .cloned()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{self, UINT256_MAX, wide};

    // No dominance pruning: all interval splits and reduction choices.
    fn exhaustive(bounds: &[U256]) -> Vec<(U256, u64)> {
        if bounds.len() == 1 {
            return vec![(bounds[0], 3)];
        }
        let mut out = Vec::new();
        for split in 1..bounds.len() {
            for (a, ga) in exhaustive(&bounds[..split]) {
                for (b, gb) in exhaustive(&bounds[split..]) {
                    let sum = wide(a) + wide(b);
                    if sum <= wide(UINT256_MAX) {
                        out.push((U256::from_limbs_slice(&sum.as_limbs()[..4]), ga + gb + 3));
                    }
                    out.push((PRIME - u256(1), ga + gb + 11));
                }
            }
        }
        out
    }

    fn replay(plan: &Plan, bounds: &[U256], inputs: &[U256], leaves: &mut Vec<usize>) -> U256 {
        match &plan.node {
            Node::Leaf(i) => {
                leaves.push(*i);
                assert_eq!(plan.bound, bounds[*i]);
                assert_eq!((plan.gas, plan.peak), (3, 1));
                inputs[*i]
            }
            Node::Pair {
                left,
                right,
                reduce,
            } => {
                let a = replay(left, bounds, inputs, leaves);
                let b = replay(right, bounds, inputs, leaves);
                let (bound, gas, result) = if *reduce {
                    (PRIME - u256(1), 11, field::add(a, b))
                } else {
                    let bound = wide(left.bound) + wide(right.bound);
                    assert!(bound <= wide(UINT256_MAX));
                    (U256::from_limbs_slice(&bound.as_limbs()[..4]), 3, a + b)
                };
                assert_eq!(plan.bound, bound);
                assert_eq!(plan.gas, left.gas + right.gas + gas);
                let p = usize::from(*reduce);
                assert_eq!(plan.peak, (p + left.peak).max(p + 1 + right.peak));
                assert!(result <= plan.bound);
                result
            }
        }
    }

    #[test]
    fn asymmetric_random_trees_match_exhaustive_cost_and_replay() {
        let edges = [
            U256::ZERO,
            u256(1),
            PRIME - u256(1),
            (PRIME - u256(1)) * u256(2),
            UINT256_MAX,
            UINT256_MAX - u256(1),
        ];
        let mut seed = 0x31c9c2b4a792e751u64;
        let mut random = || {
            let limbs = std::array::from_fn(|_| {
                seed ^= seed << 13;
                seed ^= seed >> 7;
                seed ^= seed << 17;
                seed
            });
            U256::from_limbs(limbs)
        };
        for trial in 0..96 {
            let n = 2 + trial % 5;
            let bounds: Vec<_> = (0..n)
                .map(|i| {
                    if (trial + i) % 3 == 0 {
                        random()
                    } else {
                        edges[(trial + i) % edges.len()]
                    }
                })
                .collect();
            let cap = edges[trial % edges.len()];
            let minimum = exhaustive(&bounds)
                .into_iter()
                .filter(|(bound, _)| *bound <= cap)
                .map(|(_, gas)| gas)
                .min();
            let tree = plan(&bounds, cap);
            assert_eq!(tree.as_ref().map(|p| p.gas), minimum, "trial {trial}");
            if let Some(tree) = tree {
                for mode in 0..4 {
                    let inputs: Vec<_> = bounds
                        .iter()
                        .map(|&b| match mode {
                            0 => U256::ZERO,
                            1 => b,
                            2 => b / u256(2),
                            _ => {
                                if b == UINT256_MAX {
                                    random()
                                } else {
                                    random() % (b + u256(1))
                                }
                            }
                        })
                        .collect();
                    let mut leaves = Vec::new();
                    let got = replay(&tree, &bounds, &inputs, &mut leaves);
                    assert_eq!(leaves, (0..n).collect::<Vec<_>>());
                    assert!(got <= cap);
                    assert_eq!(
                        field::reduce(got),
                        inputs.into_iter().fold(U256::ZERO, field::add)
                    );
                }
            }
        }
    }

    #[test]
    fn cache_separates_order_bounds_and_cap() {
        let a = [PRIME - u256(1), u256(1), (PRIME - u256(1)) * u256(2)];
        let small = plan(&a, PRIME - u256(1)).unwrap();
        let large = plan(&a, UINT256_MAX).unwrap();
        assert!(Arc::ptr_eq(&small, &plan(&a, PRIME - u256(1)).unwrap()));
        assert!(!Arc::ptr_eq(&small, &large));
        assert!(large.gas < small.gas);
        let b = [a[2], a[1], a[0]];
        let reversed = plan(&b, PRIME - u256(1)).unwrap();
        assert!(!Arc::ptr_eq(&small, &reversed));
        let mut leaves = Vec::new();
        replay(&reversed, &b, &b, &mut leaves);
    }

    #[test]
    fn two_lazy_pairs_need_one_reduction() {
        let bound = (PRIME - u256(1)) * u256(2);
        let tree = plan(&[bound; 4], PRIME - u256(1)).unwrap();
        assert_eq!(tree.gas, 4 * 3 + 2 * 3 + 11);
        assert_eq!(tree.bound, PRIME - u256(1));
    }

    #[test]
    fn cap_and_inclusive_word_bounds() {
        assert!(plan(&[], PRIME).is_none());
        assert!(plan(&[UINT256_MAX], PRIME).is_none());
        let tree = plan(&[UINT256_MAX, U256::ZERO], UINT256_MAX).unwrap();
        assert_eq!(tree.gas, 9);
        assert_eq!(tree.bound, UINT256_MAX);
        let tree = plan(&[UINT256_MAX, u256(1)], UINT256_MAX).unwrap();
        assert_eq!(tree.gas, 17);
        assert_eq!(tree.bound, PRIME - u256(1));
    }
}
