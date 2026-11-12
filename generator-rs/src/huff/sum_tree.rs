// Interval trees of ADD / ADDMOD, with exact inclusive bounds. The leaf
// order is fixed. PRIME is preplaced, or supplied after both operands with
// SWAP2. Costs assume three-gas leaf/PRIME copies, ADD/SWAP at 3 and ADDMOD
// at 8 on every supported fork. Base planning ignores reach, loads and size;
// the optional placement pass estimates leaf loads from the current depths.
// The emitter checks and prices the complete schedule in its actual layout.
// The global key includes bounds, cap, frontier and uniform placement policy.

use std::collections::{BTreeMap, HashMap};
use std::sync::{Arc, Mutex, OnceLock};

use crate::field::{PRIME, U256, u256};

pub(crate) enum Node {
    Leaf(usize),
    Pair {
        left: Arc<Plan>,
        right: Arc<Plan>,
        reduce: bool,
        late_prime: bool,
    },
}

pub(crate) struct Plan {
    pub node: Node,
    pub bound: U256,
    pub gas: u64,
    /// working-stack peak under this tree's fixed emission order
    pub peak: usize,
}

type Cache = HashMap<(Vec<U256>, U256, bool, bool), Option<Arc<Plan>>>;
static CACHE: OnceLock<Mutex<Cache>> = OnceLock::new();

pub(crate) fn plan(bounds: &[U256], cap: U256) -> Option<Arc<Plan>> {
    cached_plan(bounds, cap, false, false)
}

pub(crate) fn plan_peak(bounds: &[U256], cap: U256) -> Option<Arc<Plan>> {
    cached_plan(bounds, cap, true, false)
}

pub(crate) fn plan_late(bounds: &[U256], cap: U256, peak_aware: bool) -> Option<Arc<Plan>> {
    cached_plan(bounds, cap, peak_aware, true)
}

fn cached_plan(
    bounds: &[U256],
    cap: U256,
    peak_aware: bool,
    late_prime: bool,
) -> Option<Arc<Plan>> {
    let key = (bounds.to_vec(), cap, peak_aware, late_prime);
    let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    if let Some(found) = cache.lock().expect("sum tree cache").get(&key) {
        return found.clone();
    }
    let found = frontier(bounds, peak_aware, late_prime)
        .into_iter()
        .filter(|p| p.bound <= cap)
        .min_by_key(|p| (p.gas, p.peak, p.bound));
    cache
        .lock()
        .expect("sum tree cache")
        .insert(key, found.clone());
    found
}

fn frontier(bounds: &[U256], peak_aware: bool, late_prime: bool) -> Vec<Arc<Plan>> {
    let n = bounds.len();
    if n == 0 {
        return Vec::new();
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
            let mut pareto: Vec<Arc<Plan>> = Vec::new();
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
                            let late = reduce && late_prime;
                            let gas = left.gas
                                + right.gas
                                + if late {
                                    14
                                } else if reduce {
                                    11
                                } else {
                                    3
                                };
                            let extra = usize::from(reduce && !late);
                            let peak = (left.peak + extra)
                                .max(right.peak + 1 + extra)
                                .max(if late { 3 } else { 0 });
                            let keep = if peak_aware {
                                !pareto.iter().any(|old| {
                                    old.bound <= bound && old.gas <= gas && old.peak <= peak
                                })
                            } else {
                                choices
                                    .get(&bound)
                                    .is_none_or(|old| (gas, peak) < (old.gas, old.peak))
                            };
                            if keep {
                                let candidate = Arc::new(Plan {
                                    node: Node::Pair {
                                        left: left.clone(),
                                        right: right.clone(),
                                        reduce,
                                        late_prime: late,
                                    },
                                    bound,
                                    gas,
                                    peak,
                                });
                                if peak_aware {
                                    pareto.retain(|old| {
                                        !(bound <= old.bound && gas <= old.gas && peak <= old.peak)
                                    });
                                    pareto.push(candidate);
                                } else {
                                    choices.insert(bound, candidate);
                                }
                            }
                        }
                    }
                }
            }
            if peak_aware {
                pareto.sort_by_key(|p| (p.bound, p.gas, p.peak));
                cells[start][end] = pareto;
            } else {
                let mut cheapest = u64::MAX;
                for (_, choice) in choices {
                    if choice.gas < cheapest {
                        cheapest = choice.gas;
                        cells[start][end].push(choice);
                    }
                }
            }
        }
    }
    std::mem::take(&mut cells[0][n])
}

/// Reprice placement on a fixed arithmetic tree. Depths and reach are fixed
/// for this local memo; no layout-dependent result enters the global cache.
/// An out-of-reach leaf adds a three-gas load estimate, not its store cost.
pub(crate) fn place_for_reach(base: &Arc<Plan>, depths: &[usize], reach: usize) -> Arc<Plan> {
    type Placed = (Arc<Plan>, usize);
    fn place(
        base: &Arc<Plan>,
        depths: &[usize],
        reach: usize,
        extra: usize,
        memo: &mut HashMap<(usize, usize), Placed>,
    ) -> Placed {
        // Base nodes remain alive for the entire local traversal.
        let key = (Arc::as_ptr(base) as usize, extra);
        if let Some(found) = memo.get(&key) {
            return found.clone();
        }
        let found = match &base.node {
            Node::Leaf(i) => (
                base.clone(),
                usize::from(depths[*i] > 0 && depths[*i].saturating_add(extra) > reach),
            ),
            Node::Pair {
                left,
                right,
                reduce,
                ..
            } => {
                let mut best: Option<Placed> = None;
                for late in [false, true] {
                    if late && !reduce {
                        continue;
                    }
                    let p = usize::from(*reduce && !late);
                    let (left, nl) = place(left, depths, reach, extra + p, memo);
                    let (right, nr) = place(right, depths, reach, extra + p + 1, memo);
                    let gas = left.gas
                        + right.gas
                        + if late {
                            14
                        } else if *reduce {
                            11
                        } else {
                            3
                        };
                    let peak =
                        (left.peak + p)
                            .max(right.peak + p + 1)
                            .max(if late { 3 } else { 0 });
                    let loads = nl + nr;
                    let score = (gas + 3 * loads as u64, loads, peak, gas);
                    if best.as_ref().is_none_or(|(old, reads)| {
                        score < (old.gas + 3 * *reads as u64, *reads, old.peak, old.gas)
                    }) {
                        best = Some((
                            Arc::new(Plan {
                                node: Node::Pair {
                                    left,
                                    right,
                                    reduce: *reduce,
                                    late_prime: late,
                                },
                                bound: base.bound,
                                gas,
                                peak,
                            }),
                            loads,
                        ));
                    }
                }
                best.expect("preplaced choice")
            }
        };
        memo.insert(key, found.clone());
        found
    }
    place(base, depths, reach, 0, &mut HashMap::new()).0
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
                late_prime,
            } => {
                let a = replay(left, bounds, inputs, leaves);
                let b = replay(right, bounds, inputs, leaves);
                let (bound, gas, result) = if *reduce {
                    (
                        PRIME - u256(1),
                        if *late_prime { 14 } else { 11 },
                        field::add(a, b),
                    )
                } else {
                    assert!(!late_prime);
                    let bound = wide(left.bound) + wide(right.bound);
                    assert!(bound <= wide(UINT256_MAX));
                    (U256::from_limbs_slice(&bound.as_limbs()[..4]), 3, a + b)
                };
                assert_eq!(plan.bound, bound);
                assert_eq!(plan.gas, left.gas + right.gas + gas);
                let p = usize::from(*reduce && !late_prime);
                assert_eq!(
                    plan.peak,
                    (p + left.peak)
                        .max(p + 1 + right.peak)
                        .max(if *late_prime { 3 } else { 0 })
                );
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

    fn exhaustive_peak(bounds: &[U256]) -> Vec<(U256, u64, usize)> {
        if bounds.len() == 1 {
            return vec![(bounds[0], 3, 1)];
        }
        let mut out = Vec::new();
        for split in 1..bounds.len() {
            for (a, ga, pa) in exhaustive_peak(&bounds[..split]) {
                for (b, gb, pb) in exhaustive_peak(&bounds[split..]) {
                    if let Some(sum) = a.checked_add(b) {
                        out.push((sum, ga + gb + 3, pa.max(pb + 1)));
                    }
                    out.push((PRIME - u256(1), ga + gb + 11, (pa + 1).max(pb + 2)));
                }
            }
        }
        out
    }

    fn check_frontier(bounds: &[U256]) {
        let mut all = exhaustive_peak(bounds);
        all.sort_unstable();
        all.dedup();
        let want: Vec<_> = all
            .iter()
            .copied()
            .filter(|p| {
                !all.iter()
                    .any(|q| q != p && q.0 <= p.0 && q.1 <= p.1 && q.2 <= p.2)
            })
            .collect();
        let got: Vec<_> = frontier(bounds, true, false)
            .iter()
            .map(|p| (p.bound, p.gas, p.peak))
            .collect();
        assert_eq!(got, want, "bounds {bounds:?}");
    }

    #[test]
    fn peak_frontier_recovers_equal_gas_witness() {
        let bounds = [5, 1, 4, 2].map(|u| (PRIME - u256(1)) * u256(u));
        let old = plan(&bounds, PRIME - u256(1)).unwrap();
        let new = plan_peak(&bounds, PRIME - u256(1)).unwrap();
        assert_eq!((old.gas, old.peak), (37, 5));
        assert_eq!((new.gas, new.peak), (37, 4));
        assert!(!Arc::ptr_eq(&old, &new));
        assert!(Arc::ptr_eq(
            &new,
            &plan_peak(&bounds, PRIME - u256(1)).unwrap()
        ));
        let mut leaves = Vec::new();
        let got = replay(&new, &bounds, &bounds, &mut leaves);
        assert_eq!(leaves, vec![0, 1, 2, 3]);
        assert_eq!(got, bounds.into_iter().fold(U256::ZERO, field::add));
    }

    #[test]
    fn peak_frontiers_match_exhaustive_parent_compositions() {
        assert!(frontier(&[], true, false).is_empty());
        for n in 1..=5 {
            for code in 0..5usize.pow(n as u32) {
                let mut x = code;
                let bounds: Vec<_> = (0..n)
                    .map(|_| {
                        let bound = (PRIME - u256(1)) * u256((x % 5 + 1) as u64);
                        x /= 5;
                        bound
                    })
                    .collect();
                check_frontier(&bounds);
            }
        }
        for bounds in [
            vec![U256::ZERO; 5],
            vec![UINT256_MAX, u256(1), U256::ZERO],
            vec![u256(1), UINT256_MAX, UINT256_MAX - u256(1), u256(2)],
        ] {
            check_frontier(&bounds);
        }
    }

    #[test]
    fn reach_placement_is_local_to_depths_and_preserves_values() {
        let bound = PRIME - u256(1);
        let base = plan_peak(&[bound, bound], bound).unwrap();
        let near = place_for_reach(&base, &[2, 1], 16);
        let deep = place_for_reach(&base, &[16, 15], 16);
        let amsterdam = place_for_reach(&base, &[16, 15], 235);
        assert_eq!(near.gas, 17);
        assert_eq!(deep.gas, 20);
        assert_eq!(amsterdam.gas, 17);
        for tree in [near, deep, amsterdam] {
            let mut leaves = Vec::new();
            let value = replay(&tree, &[bound, bound], &[bound, bound], &mut leaves);
            assert_eq!(leaves, vec![0, 1]);
            assert_eq!(value, field::add(bound, bound));
        }
    }

    #[test]
    fn reach_placement_matches_exhaustive_choices() {
        fn choices(
            base: &Plan,
            depths: &[usize],
            reach: usize,
            extra: usize,
        ) -> Vec<(u64, usize, usize)> {
            match &base.node {
                Node::Leaf(i) => vec![(
                    3,
                    usize::from(depths[*i] > 0 && depths[*i] + extra > reach),
                    1,
                )],
                Node::Pair {
                    left,
                    right,
                    reduce,
                    ..
                } => {
                    let mut out = Vec::new();
                    for late in [false, true] {
                        if late && !reduce {
                            continue;
                        }
                        let p = usize::from(*reduce && !late);
                        for (lg, lr, lp) in choices(left, depths, reach, extra + p) {
                            for (rg, rr, rp) in choices(right, depths, reach, extra + p + 1) {
                                let gas = lg
                                    + rg
                                    + if late {
                                        14
                                    } else if *reduce {
                                        11
                                    } else {
                                        3
                                    };
                                let peak = (lp + p).max(rp + p + 1).max(if late { 3 } else { 0 });
                                out.push((gas, lr + rr, peak));
                            }
                        }
                    }
                    out
                }
            }
        }
        fn loads(plan: &Plan, depths: &[usize], reach: usize, extra: usize) -> usize {
            match &plan.node {
                Node::Leaf(i) => usize::from(depths[*i] > 0 && depths[*i] + extra > reach),
                Node::Pair {
                    left,
                    right,
                    reduce,
                    late_prime,
                } => {
                    let p = usize::from(*reduce && !late_prime);
                    loads(left, depths, reach, extra + p)
                        + loads(right, depths, reach, extra + p + 1)
                }
            }
        }
        for trial in 0..72 {
            let n = 2 + trial % 5;
            let bounds: Vec<_> = (0..n)
                .map(|i| (PRIME - u256(1)) * u256(1 + ((trial + i) % 5) as u64))
                .collect();
            let depths: Vec<_> = (0..n)
                .map(|i| {
                    if (trial + i) % 7 == 0 {
                        0
                    } else {
                        12 + (trial + n - i) % 7
                    }
                })
                .collect();
            let base = plan_peak(&bounds, PRIME - u256(1)).unwrap();
            for reach in [16, 235] {
                let expected = choices(&base, &depths, reach, 0)
                    .into_iter()
                    .map(|(g, r, p)| (g + 3 * r as u64, r, p, g))
                    .min()
                    .unwrap();
                let chosen = place_for_reach(&base, &depths, reach);
                let reads = loads(&chosen, &depths, reach, 0);
                assert_eq!(
                    (
                        chosen.gas + 3 * reads as u64,
                        reads,
                        chosen.peak,
                        chosen.gas
                    ),
                    expected
                );
                let mut leaves = Vec::new();
                let value = replay(&chosen, &bounds, &bounds, &mut leaves);
                assert_eq!(leaves, (0..n).collect::<Vec<_>>());
                assert_eq!(value, bounds.iter().copied().fold(U256::ZERO, field::add));
            }
        }
    }

    #[test]
    fn late_prime_prices_swap_and_separates_cache_policy() {
        let p1 = PRIME - u256(1);
        let ordinary = plan_peak(&[p1, p1], p1).unwrap();
        let late = plan_late(&[p1, p1], p1, true).unwrap();
        assert_eq!((ordinary.gas, ordinary.peak), (17, 3));
        assert_eq!((late.gas, late.peak), (20, 3));
        assert!(!Arc::ptr_eq(&ordinary, &late));
        assert!(Arc::ptr_eq(&late, &plan_late(&[p1, p1], p1, true).unwrap()));
        let bounds = [5, 1, 4, 2].map(|u| p1 * u256(u));
        let tree = plan_late(&bounds, p1, true).unwrap();
        assert_eq!((tree.gas, tree.peak), (43, 3));
        let mut leaves = Vec::new();
        let got = replay(&tree, &bounds, &bounds, &mut leaves);
        assert_eq!(leaves, vec![0, 1, 2, 3]);
        assert_eq!(got, bounds.into_iter().fold(U256::ZERO, field::add));
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
