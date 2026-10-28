// Alternative fixed DAGs for the original-basis t3 low phase.
// t3variants <xb|xc|bc> <cc|sc> [window=11] [ub=56]
// cc computes 2c then sum+2c; sc computes sum+c then adds c again.
// Each DAG has the same checked bounds and [a',P,c',b'] boundary.

#[path = "../fixed_dag.rs"]
mod fixed_dag;
use fixed_dag::Dag;

fn variant(pair: &str, tail: &str) -> Result<Dag, String> {
    let (a, b, c) = match pair {
        "xb" => (1, 2, 3),
        "xc" => (1, 3, 2),
        "bc" => (2, 3, 1),
        _ => return Err("pair must be xb, xc or bc".into()),
    };
    let (last, name) = match tail {
        "cc" => ([(3, 3, false), (5, 8, false)], "twoc"),
        "sc" => ([(5, 3, false), (8, 3, false)], "sumc"),
        _ => return Err("tail must be cc or sc".into()),
    };
    Ok(Dag {
        ops: [
            (a, b, false),
            (4, c, true),
            (5, 1, false),
            (5, 2, false),
            last[0],
            last[1],
        ],
        goal: [6, 0, 9, 7],
        names: ["q", "sum", "o0", "o1", name, "o2"],
    })
}

fn main() -> Result<(), String> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if !(2..=4).contains(&args.len()) {
        return Err("t3variants pair tail [window] [upper bound]".into());
    }
    let dag = variant(&args[0], &args[1])?;
    let window = args
        .get(2)
        .map_or(Ok(11), |v| v.parse::<usize>().map_err(|e| e.to_string()))?;
    let ub = args
        .get(3)
        .map_or(Ok(56), |v| v.parse::<u32>().map_err(|e| e.to_string()))?;
    let exchange = std::env::var("EXCHANGE").is_ok_and(|v| v == "1");
    eprintln!(
        "original-basis t3 low DAG: pair {}, tail {}",
        args[0], args[1]
    );
    dag.run(window, ub, exchange)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fixed_dag::{pack, unpack};
    use std::collections::HashSet;

    #[test]
    fn all_variants_have_the_original_forms_and_bounds() {
        for pair in ["xb", "xc", "bc"] {
            for tail in ["cc", "sc"] {
                let dag = variant(pair, tail).unwrap();
                let mut forms = [[0u8; 3]; 10];
                forms[1] = [1, 0, 0];
                forms[2] = [0, 1, 0];
                forms[3] = [0, 0, 1];
                let mut bounds = [0u8; 10];
                bounds[1..4].copy_from_slice(&[1, 3, 2]);
                for (i, &(a, b, reduce)) in dag.ops.iter().enumerate() {
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
                assert_eq!(dag.h(&[1, 3, 2], 0), Some(47));
            }
        }
        assert!(variant("xx", "cc").is_err());
        assert!(variant("xb", "ss").is_err());
    }

    #[test]
    fn original_dag_and_incumbent_are_unchanged() {
        let dag = variant("xb", "cc").unwrap();
        let program = "P P dup4 dup6 dup5 add=q addmod=sum dup1 dup6 add=o1 swap4 dup1 add=twoc dup2 add=o2 swap3 add=o0";
        for exchange in [false, true] {
            assert_eq!(dag.replay(program, 11, exchange).unwrap(), 56);
        }
    }

    #[test]
    fn all_variant_heuristics_are_consistent_on_prefixes() {
        for pair in ["xb", "xc", "bc"] {
            for tail in ["cc", "sc"] {
                let dag = variant(pair, tail).unwrap();
                for exchange in [false, true] {
                    let start = pack(&[1, 3, 2], 0);
                    let mut seen = HashSet::from([start]);
                    let mut layer = vec![start];
                    for _ in 0..4 {
                        let mut next_layer = Vec::new();
                        for key in layer {
                            let (stack, done) = unpack(key);
                            for (cost, _, mut next, mask) in dag.moves(&stack, done, 7, exchange) {
                                dag.canon(&mut next, mask);
                                match (dag.h(&stack, done), dag.h(&next, mask)) {
                                    (Some(a), Some(b)) => assert!(a <= cost + b),
                                    (None, Some(_)) => panic!("lost node recreated"),
                                    _ => {}
                                }
                                let key = pack(&next, mask);
                                if seen.insert(key) {
                                    next_layer.push(key);
                                }
                            }
                        }
                        layer = next_layer;
                    }
                }
            }
        }
    }
}
