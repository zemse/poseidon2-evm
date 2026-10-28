// Alternative fixed DAGs for the original-basis t3 low phase.
// t3variants <xb|xc|bc> <cc|sc> [window=11] [ub=56]
// cc computes 2c then sum+2c; sc computes sum+c then adds c again.
// LAYOUT=cb-cb (default), cb-bc, bc-cb or bc-bc sets the inactive order.
// Bounds and arithmetic are unchanged; a' and PRIME remain the first two outputs.

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

fn oriented(pair: &str, tail: &str, layout: &str) -> Result<Dag, String> {
    let mut dag = variant(pair, tail)?;
    let (input, output) = layout.split_once('-').ok_or("layout needs input-output")?;
    if !["cb", "bc"].contains(&input) || !["cb", "bc"].contains(&output) {
        return Err("inactive orders must be cb or bc".into());
    }
    if input == "bc" {
        for (a, b, _) in &mut dag.ops {
            for v in [a, b] {
                *v = match *v {
                    2 => 3,
                    3 => 2,
                    v => v,
                };
            }
        }
    }
    if output == "bc" {
        dag.goal.swap(2, 3);
    }
    Ok(dag)
}

fn main() -> Result<(), String> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if !(2..=4).contains(&args.len()) {
        return Err("t3variants pair tail [window] [upper bound]".into());
    }
    let layout = std::env::var("LAYOUT").unwrap_or_else(|_| "cb-cb".into());
    let dag = oriented(&args[0], &args[1], &layout)?;
    let window = args
        .get(2)
        .map_or(Ok(11), |v| v.parse::<usize>().map_err(|e| e.to_string()))?;
    let ub = args
        .get(3)
        .map_or(Ok(56), |v| v.parse::<u32>().map_err(|e| e.to_string()))?;
    let exchange = std::env::var("EXCHANGE").is_ok_and(|v| v == "1");
    eprintln!(
        "original-basis t3 low DAG: pair {}, tail {}, layout {layout}",
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
    fn orientations_preserve_forms_bounds_and_default() {
        for pair in ["xb", "xc", "bc"] {
            for tail in ["cc", "sc"] {
                let original = variant(pair, tail).unwrap();
                let default = oriented(pair, tail, "cb-cb").unwrap();
                assert_eq!(default.ops, original.ops);
                assert_eq!(default.goal, original.goal);
                assert_eq!(default.names, original.names);
                for layout in ["cb-cb", "cb-bc", "bc-cb", "bc-bc"] {
                    let dag = oriented(pair, tail, layout).unwrap();
                    let mut forms = [[0u8; 3]; 10];
                    forms[1] = [1, 0, 0];
                    forms[2] = [0, 1, 0];
                    forms[3] = [0, 0, 1];
                    let mut bounds = [0u8; 10];
                    bounds[1..4].copy_from_slice(&[1, 3, 2]);
                    if layout.starts_with("bc-") {
                        forms.swap(2, 3);
                        bounds.swap(2, 3);
                    }
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
                    let expected = if layout.ends_with("-bc") {
                        [6, 0, 7, 9]
                    } else {
                        [6, 0, 9, 7]
                    };
                    assert_eq!(dag.goal, expected);
                    assert!(dag.goal(&expected, fixed_dag::ALL));
                    let mut wrong = expected;
                    wrong.swap(2, 3);
                    assert!(!dag.goal(&wrong, fixed_dag::ALL));
                }
            }
        }
        for layout in ["cb", "cb-", "-bc", "cb-cb-extra", "cc-bc"] {
            assert!(oriented("xb", "cc", layout).is_err());
        }
    }

    #[test]
    fn original_dag_and_incumbent_are_unchanged() {
        let dag = oriented("xb", "cc", "cb-cb").unwrap();
        let program = "P P dup4 dup6 dup5 add=q addmod=sum dup1 dup6 add=o1 swap4 dup1 add=twoc dup2 add=o2 swap3 add=o0";
        for exchange in [false, true] {
            assert_eq!(dag.replay(program, 11, exchange).unwrap(), 56);
        }
    }

    #[test]
    fn oriented_incumbents_charge_both_adapters() {
        let incumbent = "P P dup4 dup6 dup5 add=q addmod=sum dup1 dup6 add=o1 swap4 dup1 add=twoc dup2 add=o2 swap3 add=o0";
        for layout in ["cb-cb", "cb-bc", "bc-cb", "bc-bc"] {
            let dag = oriented("xb", "cc", layout).unwrap();
            for exchange in [false, true] {
                let mut program = Vec::new();
                let mut gas = 56;
                if layout.starts_with("bc-") {
                    program.push(if exchange {
                        "exchange1,2"
                    } else {
                        "swap1 swap2 swap1"
                    });
                    gas += if exchange { 3 } else { 9 };
                }
                program.push(incumbent);
                if layout.ends_with("-bc") {
                    program.push(if exchange {
                        "exchange2,3"
                    } else {
                        "swap2 swap3 swap2"
                    });
                    gas += if exchange { 3 } else { 9 };
                }
                assert_eq!(dag.replay(&program.join(" "), 11, exchange).unwrap(), gas);
            }
        }
    }

    fn consistent_prefixes(dag: &Dag, exchange: bool) {
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

    #[test]
    fn all_variant_heuristics_are_consistent_on_prefixes() {
        for pair in ["xb", "xc", "bc"] {
            for tail in ["cc", "sc"] {
                for layout in ["cb-cb", "cb-bc", "bc-cb", "bc-bc"] {
                    let dag = oriented(pair, tail, layout).unwrap();
                    for exchange in [false, true] {
                        consistent_prefixes(&dag, exchange);
                    }
                }
            }
        }
    }
}
