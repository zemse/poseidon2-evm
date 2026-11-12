use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

use crate::field::{PRIME, U256, u256};

/// Reduction sites in q = x + b (or x + c), S = q + the other lane,
/// d = 2c, A = S + x, B = S + b, C = S + d. A stays lazy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::huff) enum Policy {
    SumDouble,
    PairOutputs,
    Lazy,
    SumB,
    SumC,
}

impl Policy {
    pub(super) const ALL: [Self; 5] = [
        Self::SumDouble,
        Self::PairOutputs,
        Self::Lazy,
        Self::SumB,
        Self::SumC,
    ];

    pub(super) fn bounds(self, b: U256, c: U256) -> Option<[U256; 3]> {
        let l = PRIME - u256(1);
        let plus = |a: U256, b: U256, reduce| {
            if reduce { Some(l) } else { a.checked_add(b) }
        };
        let swapped = self == Self::SumB;
        let q = plus(l, if swapped { c } else { b }, self == Self::PairOutputs)?;
        let sum = plus(
            q,
            if swapped { b } else { c },
            matches!(self, Self::SumDouble | Self::SumB | Self::SumC),
        )?;
        let d = plus(c, c, self == Self::SumDouble)?;
        let a = plus(sum, l, false)?;
        if a > l * u256(4) {
            return None;
        }
        Some([
            a,
            plus(sum, b, matches!(self, Self::PairOutputs | Self::SumB))?,
            plus(sum, d, matches!(self, Self::PairOutputs | Self::SumC))?,
        ])
    }

    pub(super) fn gas(self) -> u64 {
        93 + 8 * match self {
            Self::Lazy => 0,
            Self::PairOutputs => 3,
            _ => 2,
        }
    }
}

type Key = (usize, U256, U256);
type Choice = Option<(u64, Policy)>;
static CACHE: OnceLock<Mutex<HashMap<Key, Choice>>> = OnceLock::new();

/// Plan to the fused seam's b <= 3L, c <= L boundary. The active lane
/// stays <= 4L, so adding any field round constant cannot wrap.
pub(super) fn choose(b: U256, c: U256, rounds: usize) -> Option<Policy> {
    fn cost(b: U256, c: U256, rounds: usize) -> Choice {
        let l = PRIME - u256(1);
        if rounds == 0 {
            return (b <= l * u256(3) && c <= l).then_some((0, Policy::Lazy));
        }
        let key = (rounds, b, c);
        let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
        if let Some(found) = cache.lock().expect("t3 policy cache").get(&key) {
            return *found;
        }
        let mut best: Choice = None;
        for policy in Policy::ALL {
            let Some([_, b, c]) = policy.bounds(b, c) else {
                continue;
            };
            let Some((tail, _)) = cost(b, c, rounds - 1) else {
                continue;
            };
            let gas = policy.gas() + tail;
            if best.is_none_or(|(old, _)| gas < old) {
                best = Some((gas, policy));
            }
        }
        cache.lock().expect("t3 policy cache").insert(key, best);
        best
    }
    (rounds > 0)
        .then(|| cost(b, c, rounds))
        .flatten()
        .map(|(_, policy)| policy)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cycle_and_terminal_bounds() {
        let l = PRIME - u256(1);
        for (policy, b, c, out) in [
            (Policy::SumDouble, 4, 5, [2, 5, 2]),
            (Policy::PairOutputs, 5, 2, [4, 1, 1]),
            (Policy::Lazy, 1, 1, [4, 4, 5]),
        ] {
            assert_eq!(
                policy.bounds(l * u256(b), l * u256(c)),
                Some(out.map(|n| l * u256(n)))
            );
        }
        assert_eq!(Policy::Lazy.gas(), 93);
        assert!(Policy::SumDouble.bounds(l * u256(5), l * u256(2)).is_none());
        let (mut b, mut c) = (l * u256(4), l * u256(4));
        let mut gas = 0;
        for remaining in (1..=55).rev() {
            let policy = choose(b, c, remaining).unwrap();
            let [a, next_b, next_c] = policy.bounds(b, c).unwrap();
            assert!(a.checked_add(l).is_some());
            (b, c) = (next_b, next_c);
            gas += policy.gas();
        }
        assert_eq!((b, c, gas), (l * u256(3), l, 5859));
        for rounds in 1..=56 {
            for b in 1..=5 {
                for c in 1..=5 {
                    if let Some(policy) = choose(l * u256(b), l * u256(c), rounds) {
                        assert!(policy.bounds(l * u256(b), l * u256(c)).is_some());
                    }
                }
            }
        }
    }
}
