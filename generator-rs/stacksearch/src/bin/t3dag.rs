// Fixed-DAG t3 low phase after the S-box, from [x,c,b] to [a',P,c',b'].
// Bounds are x=1, b=3, c=2 in units of P-1. Each arithmetic node runs once.
// t3dag [window=8] [ub=56]; EXCHANGE=1 enables non-top swaps.
// REPLAY="..." checks a DSL program. One garbage slot is allowed; live
// copies and PRIME supply are limited only by the working window. The
// fixed DAG, once-only nodes and working window are not an EVM optimum.

#[path = "../fixed_dag.rs"]
mod fixed_dag;
use fixed_dag::Dag;

const OPS: [(u8, u8, bool); 6] = [
    (1, 2, false),
    (4, 3, true),
    (5, 1, false),
    (5, 2, false),
    (3, 3, false),
    (5, 8, false),
];
const LOW: Dag = Dag {
    ops: OPS,
    goal: [6, 0, 9, 7],
    names: ["q", "sum", "o0", "o1", "twoc", "o2"],
};

fn main() -> Result<(), String> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.len() > 2 {
        return Err("t3dag [window] [upper bound]".into());
    }
    let window = args
        .first()
        .map_or(Ok(8), |v| v.parse::<usize>().map_err(|e| e.to_string()))?;
    let ub = args
        .get(1)
        .map_or(Ok(56), |v| v.parse::<u32>().map_err(|e| e.to_string()))?;
    let exchange = std::env::var("EXCHANGE").is_ok_and(|v| v == "1");
    LOW.run(window, ub, exchange)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fixed_dag::{pack, unpack, ALL};
    const INCUMBENT: &str = "P P dup4 dup6 dup5 add=q addmod=sum dup1 dup6 add=o1 swap4 dup1 add=twoc dup2 add=o2 swap3 add=o0";

    #[test]
    fn incumbent_and_funded_bound() {
        assert_eq!(LOW.h(&[1, 3, 2], 0), Some(47));
        for exchange in [false, true] {
            assert_eq!(LOW.replay(INCUMBENT, 8, exchange).unwrap(), 56);
        }
        assert!(LOW.replay("P", 8, true).is_err());
        assert!(LOW.replay("exchange1,8", 8, true).is_err());
    }

    #[test]
    fn fixed_forms_and_bounds() {
        let mut forms = [[0u8; 3]; 10];
        let mut bounds = [0u8; 10];
        forms[1] = [1, 0, 0];
        forms[2] = [0, 1, 0];
        forms[3] = [0, 0, 1];
        bounds[1] = 1;
        bounds[2] = 3;
        bounds[3] = 2;
        for (i, &(a, b, reduce)) in OPS.iter().enumerate() {
            let (a, b) = (a as usize, b as usize);
            forms[i + 4] = std::array::from_fn(|k| forms[a][k] + forms[b][k]);
            bounds[i + 4] = if reduce { 1 } else { bounds[a] + bounds[b] };
            assert!(bounds[i + 4] <= 5);
        }
        assert_eq!(
            [forms[6], forms[7], forms[9]],
            [[2, 1, 1], [1, 2, 1], [1, 1, 3]]
        );
        assert_eq!([bounds[6], bounds[7], bounds[9]], [2, 4, 5]);
    }

    #[test]
    fn live_copies_and_prime_can_exceed_one_spare() {
        let stack = [1, 1, 1, 3, 2];
        let added = LOW
            .moves(&stack, 0, 11, true)
            .into_iter()
            .find(|m| LOW.name(m.1) == "dup1")
            .unwrap();
        assert_eq!(added.2, vec![1, 1, 1, 1, 3, 2]);
        assert_eq!(added.0, 3);
        let stack = [0, 0, 0, 1, 3, 2];
        let added = LOW
            .moves(&stack, 0, 11, true)
            .into_iter()
            .find(|m| m.1 == 40)
            .unwrap();
        assert_eq!(added.2, vec![0, 0, 0, 0, 1, 3, 2]);
        assert!(!LOW
            .moves(&stack, 0, stack.len(), true)
            .iter()
            .any(|m| m.1 <= 16 || m.1 == 40));
    }

    #[test]
    fn heuristic_is_consistent_on_reachable_prefixes() {
        use std::collections::HashSet;
        for exchange in [false, true] {
            let mut seen = HashSet::from([pack(&[1, 3, 2], 0)]);
            let mut layer = vec![pack(&[1, 3, 2], 0)];
            for _ in 0..4 {
                let mut next_layer = Vec::new();
                for key in layer {
                    let (stack, done) = unpack(key);
                    let before = LOW.h(&stack, done);
                    for (cost, _, mut next, mask) in LOW.moves(&stack, done, 7, exchange) {
                        LOW.canon(&mut next, mask);
                        let after = LOW.h(&next, mask);
                        match (before, after) {
                            (Some(a), Some(b)) => assert!(a <= cost + b),
                            (None, Some(_)) => panic!("lost value was recreated"),
                            _ => {}
                        }
                        if seen.insert(pack(&next, mask)) {
                            next_layer.push(pack(&next, mask));
                        }
                    }
                }
                layer = next_layer;
            }
        }
    }

    #[test]
    fn useful_stock_bounds_the_sub_incumbent_window() {
        let mut maximum = 0;
        for done in 0..=ALL {
            let valid = OPS.iter().enumerate().all(|(i, &(a, b, _))| {
                done & (1 << i) == 0 || [a, b].iter().all(|&v| v < 4 || done & (1 << (v - 4)) != 0)
            });
            if !valid {
                continue;
            }
            let useful = LOW.need(0, done)
                + (1..=9)
                    .filter(|&v| v < 4 || done & (1 << (v - 4)) != 0)
                    .map(|v| LOW.need(v, done))
                    .sum::<usize>();
            maximum = maximum.max(useful);
        }
        assert_eq!(maximum, 9);
        assert_eq!(
            maximum + (55 - LOW.h(&[1, 3, 2], 0).unwrap()) as usize / 3,
            11
        );
    }

    #[test]
    fn encoding_and_exchange_control() {
        for n in 0..=16 {
            let stack: Vec<_> = (0..n).map(|i| (i % 11) as u8).collect();
            for done in [0, 17, ALL] {
                assert_eq!(unpack(pack(&stack, done)), (stack.clone(), done));
            }
        }
        let stack = [1, 3, 2];
        let old = LOW.moves(&stack, 0, 8, false);
        let mut new = LOW.moves(&stack, 0, 8, true);
        let m = new.iter().find(|m| LOW.name(m.1) == "exchange1,2").unwrap();
        assert_eq!((m.0, m.2.as_slice(), m.3), (3, [1, 2, 3].as_slice(), 0));
        new.retain(|m| m.1 < 64);
        assert_eq!(new, old);
        assert_eq!(LOW.h(&[1, 3], 0), None);
    }
}
