// Schedule one t3 inactive-coordinate shear transition, u=b+c, v=c.
// q=x+u; s=q+v; a=q+x; v'=s+v; h=s+q; u'=h+u.
// sheardag <mask> <u-bound> <v-bound> [window=12] [ub=floor+10]
// Bit i chooses ADDMOD for node i; all other nodes use checked ADD bounds.
// The result is post-S-box model gas, not a whole permutation measurement.

#[path = "../fixed_dag.rs"]
mod fixed_dag;
use fixed_dag::Dag;

fn shear(mask: u32, u: u32, v: u32) -> Result<(Dag, [u8; 3]), String> {
    if mask > 63 || !(1..=5).contains(&u) || !(1..=5).contains(&v) {
        return Err("mask must be in 0..63 and bounds in 1..5".into());
    }
    let pairs = [(1, 2), (4, 3), (4, 1), (5, 3), (5, 4), (8, 2)];
    let ops = std::array::from_fn(|i| (pairs[i].0, pairs[i].1, mask & (1 << i) != 0));
    let mut bounds = [0u8; 10];
    bounds[1] = 1;
    bounds[2] = u as u8;
    bounds[3] = v as u8;
    for (i, &(a, b, reduce)) in ops.iter().enumerate() {
        bounds[i + 4] = if reduce {
            1
        } else {
            bounds[a as usize] + bounds[b as usize]
        };
        if bounds[i + 4] > 5 {
            return Err(format!("node {i} ADD exceeds five field bounds"));
        }
    }
    if bounds[6] > 4 {
        return Err("active output leaves no room for the next constant".into());
    }
    Ok((
        Dag {
            ops,
            goal: [6, 0, 7, 9],
            names: ["q", "s", "a", "v1", "h", "u1"],
        },
        [bounds[6], bounds[9], bounds[7]],
    ))
}

fn main() -> Result<(), String> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if !(3..=5).contains(&args.len()) {
        return Err("sheardag mask u-bound v-bound [window] [upper bound]".into());
    }
    let arg = |i: usize, fallback: u32| {
        args.get(i).map_or(Ok(fallback), |v| {
            v.parse::<u32>().map_err(|e| e.to_string())
        })
    };
    let (dag, bounds) = shear(arg(0, 0)?, arg(1, 0)?, arg(2, 0)?)?;
    let floor = dag.h(&[1, 3, 2], 0).expect("raw inputs");
    eprintln!("output bounds a,u,v = {bounds:?}");
    let window = arg(3, 12)? as usize;
    let ub = arg(4, floor + 10)?;
    let exchange = std::env::var("EXCHANGE").is_ok_and(|v| v == "1");
    dag.run(window, ub, exchange)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fixed_dag::{pack, unpack};
    const CASES: [(u32, u32, u32, [u8; 3]); 7] = [
        (10, 1, 4, [3, 4, 1]),
        (33, 4, 1, [2, 1, 3]),
        (24, 1, 3, [3, 2, 1]),
        (1, 2, 1, [2, 5, 3]),
        (41, 5, 3, [2, 1, 1]),
        (32, 1, 1, [3, 1, 4]),
        (40, 1, 1, [3, 1, 1]),
    ];

    #[test]
    fn recorded_policies_have_their_bounds_and_funded_costs() {
        for (mask, u, v, outputs) in CASES {
            let (dag, bounds) = shear(mask, u, v).unwrap();
            assert_eq!(bounds, outputs);
            assert_eq!(dag.h(&[1, 3, 2], 0), Some(39 + 8 * mask.count_ones()));
        }
        for (mask, u, v) in [(64, 1, 1), (0, 0, 1), (0, 1, 6), (0, 1, 4), (34, 3, 1)] {
            assert!(shear(mask, u, v).is_err());
        }
    }

    #[test]
    fn recorded_schedules_replay_with_suffix_bounds() {
        let programs = include_str!("../../results/astra-shear.program");
        assert_eq!(programs.lines().count(), CASES.len());
        for (line, (mask, u, v, _)) in programs.lines().zip(CASES) {
            let fields: Vec<_> = line.splitn(5, '\t').collect();
            assert_eq!(fields.len(), 5);
            let numbers: Vec<u32> = fields[..4].iter().map(|s| s.parse().unwrap()).collect();
            assert_eq!(numbers[..3], [mask, u, v]);
            let (dag, _) = shear(mask, u, v).unwrap();
            for exchange in [false, true] {
                assert_eq!(dag.replay(fields[4], 12, exchange).unwrap(), numbers[3]);
            }
            assert_eq!(numbers[3], dag.h(&[1, 3, 2], 0).unwrap() + 9);
        }
    }

    #[test]
    fn shear_nodes_match_independent_linear_formula() {
        const P: u128 = 101;
        for (mask, u_bound, v_bound, bounds) in CASES {
            let (dag, _) = shear(mask, u_bound, v_bound).unwrap();
            for trial in 0..64u128 {
                let mut values = [0u128; 10];
                values[1] = if trial == 0 { P - 1 } else { (trial * 37) % P };
                values[2] = if trial == 0 {
                    u_bound as u128 * (P - 1)
                } else {
                    trial * 71 % (u_bound as u128 * (P - 1) + 1)
                };
                values[3] = if trial == 0 {
                    v_bound as u128 * (P - 1)
                } else {
                    trial * 43 % (v_bound as u128 * (P - 1) + 1)
                };
                let (x, u, v) = (values[1], values[2], values[3]);
                for (i, &(a, b, reduce)) in dag.ops.iter().enumerate() {
                    let sum = values[a as usize] + values[b as usize];
                    values[i + 4] = if reduce { sum % P } else { sum };
                }
                assert_eq!(
                    [values[6] % P, values[9] % P, values[7] % P],
                    [
                        (2 * x + u) % P,
                        (2 * x + 3 * u + v) % P,
                        (x + u + 2 * v) % P
                    ]
                );
                for (value, bound) in [values[6], values[9], values[7]].into_iter().zip(bounds) {
                    assert!(value <= u128::from(bound) * (P - 1));
                }
            }
        }
    }

    #[test]
    fn heuristic_consistency_for_each_recorded_policy() {
        use std::collections::HashSet;
        for (mask, u, v, _) in CASES {
            let (dag, _) = shear(mask, u, v).unwrap();
            for exchange in [false, true] {
                let start = pack(&[1, 3, 2], 0);
                let mut seen = HashSet::from([start]);
                let mut layer = vec![start];
                for _ in 0..4 {
                    let mut next_layer = Vec::new();
                    for key in layer {
                        let (stack, done) = unpack(key);
                        for (cost, _, mut next, done_next) in dag.moves(&stack, done, 7, exchange) {
                            dag.canon(&mut next, done_next);
                            match (dag.h(&stack, done), dag.h(&next, done_next)) {
                                (Some(a), Some(b)) => assert!(a <= cost + b),
                                (None, Some(_)) => panic!("lost node recreated"),
                                _ => {}
                            }
                            let next_key = pack(&next, done_next);
                            if seen.insert(next_key) {
                                next_layer.push(next_key);
                            }
                        }
                    }
                    layer = next_layer;
                }
            }
        }
    }
}
