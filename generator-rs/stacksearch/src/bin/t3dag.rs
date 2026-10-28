// Fixed-DAG t3 low phase after the S-box, from [x,c,b] to [a',P,c',b'].
// Bounds are x=1, b=3, c=2 in units of P-1. Each arithmetic node runs once.
// t3dag [window=8] [ub=56]; EXCHANGE=1 enables non-top swaps.
// REPLAY="..." checks a DSL program. One garbage slot is allowed; live
// copies and PRIME supply are limited only by the working window. The
// fixed DAG, once-only nodes and working window are not an EVM optimum.

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};

const DEAD: u8 = 10;
const ALL: u8 = 63;
const GOAL: [u8; 4] = [6, 0, 9, 7];
const OPS: [(u8, u8, bool); 6] = [
    (1, 2, false),
    (4, 3, true),
    (5, 1, false),
    (5, 2, false),
    (3, 3, false),
    (5, 8, false),
];
const NAMES: [&str; 6] = ["q", "sum", "o0", "o1", "twoc", "o2"];

fn need(v: u8, done: u8) -> usize {
    if v == 0 {
        return 1 + OPS
            .iter()
            .enumerate()
            .filter(|(i, op)| done & (1 << i) == 0 && op.2)
            .count();
    }
    usize::from(GOAL.contains(&v))
        + OPS
            .iter()
            .enumerate()
            .filter(|(i, _)| done & (1 << i) == 0)
            .map(|(_, &(a, b, _))| usize::from(a == v) + usize::from(b == v))
            .sum::<usize>()
}

fn h(stack: &[u8], done: u8) -> Option<u32> {
    let mut cost: u32 = OPS
        .iter()
        .enumerate()
        .filter(|(i, _)| done & (1 << i) == 0)
        .map(|(_, op)| if op.2 { 8 } else { 3 })
        .sum();
    let count = |v| stack.iter().filter(|&&x| x == v).count();
    cost += 3 * need(0, done).saturating_sub(count(0)) as u32;
    for v in 1..=9 {
        let uses = need(v, done);
        let computed = v < 4 || done & (1 << (v - 4)) != 0;
        let have = if computed { count(v) } else { 1 };
        if computed && uses > 0 && have == 0 {
            return None;
        }
        cost += 3 * uses.saturating_sub(have) as u32;
    }
    Some(cost)
}

fn canon(stack: &mut [u8], done: u8) {
    for v in stack {
        if *v != 0 && need(*v, done) == 0 {
            *v = DEAD;
        }
    }
}

fn goal(stack: &[u8], done: u8) -> bool {
    done == ALL && (4..=5).contains(&stack.len()) && stack[..4] == GOAL
}

fn name(code: u8) -> String {
    match code {
        1..=16 => format!("dup{code}"),
        17..=31 => format!("swap{}", code - 16),
        40 => "P".into(),
        41 => "pop".into(),
        42..=47 => {
            let i = usize::from(code - 42);
            format!("{}={}", if OPS[i].2 { "addmod" } else { "add" }, NAMES[i])
        }
        _ => {
            let id = usize::from(code - 64);
            let k = (2..16)
                .find(|&k| id < k * (k - 1) / 2)
                .expect("exchange code");
            let j = id - (k - 1) * (k - 2) / 2 + 1;
            format!("exchange{j},{k}")
        }
    }
}

type Move = (u32, u8, Vec<u8>, u8);
fn moves(stack: &[u8], done: u8, window: usize, exchange: bool) -> Vec<Move> {
    let mut out = Vec::new();
    let n = stack.len();
    if n < window {
        let mut seen = [false; 11];
        for (k, &v) in stack.iter().enumerate() {
            if v == 0 || v == DEAD || seen[v as usize] {
                continue;
            }
            seen[v as usize] = true;
            if need(v, done) > 0 {
                let mut next = vec![v];
                next.extend_from_slice(stack);
                out.push((3, (k + 1) as u8, next, done));
            }
        }
        let mut next = vec![0];
        next.extend_from_slice(stack);
        out.push((3, 40, next, done));
    }
    for k in 1..n {
        if stack[0] != stack[k] {
            let mut next = stack.to_vec();
            next.swap(0, k);
            out.push((3, (16 + k) as u8, next, done));
        }
    }
    if exchange {
        for k in 2..n {
            for j in 1..k {
                if stack[j] != stack[k] {
                    let mut next = stack.to_vec();
                    next.swap(j, k);
                    out.push((3, (64 + (k - 1) * (k - 2) / 2 + j - 1) as u8, next, done));
                }
            }
        }
    }
    if n > 0 {
        out.push((2, 41, stack[1..].to_vec(), done));
    }
    for (i, &(a, b, reduce)) in OPS.iter().enumerate() {
        let take = if reduce { 3 } else { 2 };
        if done & (1 << i) != 0 || n < take {
            continue;
        }
        let pair = (stack[0] == a && stack[1] == b) || (stack[0] == b && stack[1] == a);
        if !pair || (reduce && stack[2] != 0) {
            continue;
        }
        let mut next = vec![4 + i as u8];
        next.extend_from_slice(&stack[take..]);
        out.push((
            if reduce { 8 } else { 3 },
            42 + i as u8,
            next,
            done | (1 << i),
        ));
    }
    out
}

fn pack(stack: &[u8], done: u8) -> u128 {
    let mut k = 0u128;
    for &v in stack.iter().rev() {
        k = (k << 4) | u128::from(v);
    }
    k | (u128::from(done) << 64) | ((stack.len() as u128) << 72)
}

fn unpack(key: u128) -> (Vec<u8>, u8) {
    let n = (key >> 72) as usize;
    let stack = (0..n).map(|i| ((key >> (4 * i)) & 15) as u8).collect();
    (stack, ((key >> 64) & 63) as u8)
}

fn replay(program: &str, window: usize, exchange: bool) -> Result<u32, String> {
    let (mut stack, mut done, mut cost) = (vec![1, 3, 2], 0, 0);
    let mut trace = vec![(stack.clone(), done, cost)];
    for op in program.split_whitespace() {
        let (gas, _, next, mask) = moves(&stack, done, window, exchange)
            .into_iter()
            .find(|(_, code, _, _)| name(*code) == op)
            .ok_or_else(|| format!("unavailable replay move {op}"))?;
        cost += gas;
        stack = next;
        done = mask;
        canon(&mut stack, done);
        trace.push((stack.clone(), done, cost));
    }
    if !goal(&stack, done) {
        return Err("replay goal".into());
    }
    for (stack, done, spent) in trace {
        if !h(&stack, done).is_some_and(|h| h <= cost - spent) {
            return Err("replay suffix bound".into());
        }
    }
    Ok(cost)
}

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
    if !(4..=16).contains(&window) {
        return Err("window must be in 4..16".into());
    }
    let exchange = std::env::var("EXCHANGE").is_ok_and(|v| v == "1");
    if let Ok(program) = std::env::var("REPLAY") {
        println!("replay cost {}", replay(&program, window, exchange)?);
        return Ok(());
    }
    let start = pack(&[1, 3, 2], 0);
    let mut best: HashMap<u128, (u32, Option<(u128, u8)>)> = HashMap::new();
    best.insert(start, (0, None));
    let mut queue = BinaryHeap::new();
    queue.push((Reverse(h(&[1, 3, 2], 0).unwrap()), 0, start));
    let mut expanded = 0u64;
    while let Some((Reverse(f), gas, key)) = queue.pop() {
        if best[&key].0 < gas {
            continue;
        }
        if f >= ub {
            break;
        }
        let (stack, done) = unpack(key);
        if goal(&stack, done) {
            let mut path = Vec::new();
            let mut at = key;
            while let Some((parent, code)) = best[&at].1 {
                path.push(name(code));
                at = parent;
            }
            path.reverse();
            println!("cost {gas}, expanded {expanded}, states {}", best.len());
            println!("dsl: {}", path.join(" "));
            return Ok(());
        }
        expanded += 1;
        if expanded.is_multiple_of(1_000_000) {
            eprintln!(
                "expanded {expanded} states {} queue {} f {f}",
                best.len(),
                queue.len()
            );
        }
        for (cost, code, mut next, mask) in moves(&stack, done, window, exchange) {
            canon(&mut next, mask);
            let ng = gas + cost;
            let Some(bound) = h(&next, mask) else {
                continue;
            };
            if ng + bound >= ub {
                continue;
            }
            let nk = pack(&next, mask);
            if best.get(&nk).is_some_and(|x| x.0 <= ng) {
                continue;
            }
            best.insert(nk, (ng, Some((key, code))));
            queue.push((Reverse(ng + bound), ng, nk));
        }
    }
    println!(
        "no solution below {ub}, expanded {expanded}, states {}",
        best.len()
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    const INCUMBENT: &str = "P P dup4 dup6 dup5 add=q addmod=sum dup1 dup6 add=o1 swap4 dup1 add=twoc dup2 add=o2 swap3 add=o0";

    #[test]
    fn incumbent_and_funded_bound() {
        assert_eq!(h(&[1, 3, 2], 0), Some(47));
        for exchange in [false, true] {
            assert_eq!(replay(INCUMBENT, 8, exchange).unwrap(), 56);
        }
        assert!(replay("P", 8, true).is_err());
        assert!(replay("exchange1,8", 8, true).is_err());
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
        let added = moves(&stack, 0, 11, true)
            .into_iter()
            .find(|m| name(m.1) == "dup1")
            .unwrap();
        assert_eq!(added.2, vec![1, 1, 1, 1, 3, 2]);
        assert_eq!(added.0, 3);
        let stack = [0, 0, 0, 1, 3, 2];
        let added = moves(&stack, 0, 11, true)
            .into_iter()
            .find(|m| m.1 == 40)
            .unwrap();
        assert_eq!(added.2, vec![0, 0, 0, 0, 1, 3, 2]);
        assert!(!moves(&stack, 0, stack.len(), true)
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
                    let before = h(&stack, done);
                    for (cost, _, mut next, mask) in moves(&stack, done, 7, exchange) {
                        canon(&mut next, mask);
                        let after = h(&next, mask);
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
            let useful = need(0, done)
                + (1..=9)
                    .filter(|&v| v < 4 || done & (1 << (v - 4)) != 0)
                    .map(|v| need(v, done))
                    .sum::<usize>();
            maximum = maximum.max(useful);
        }
        assert_eq!(maximum, 9);
        // Beyond mandatory supply, each extra stack entry costs at least 3.
        assert_eq!(maximum + (55 - h(&[1, 3, 2], 0).unwrap()) as usize / 3, 11);
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
        let old = moves(&stack, 0, 8, false);
        let mut new = moves(&stack, 0, 8, true);
        let m = new.iter().find(|m| name(m.1) == "exchange1,2").unwrap();
        assert_eq!((m.0, m.2.as_slice(), m.3), (3, [1, 2, 3].as_slice(), 0));
        new.retain(|m| m.1 < 64);
        assert_eq!(new, old);
        assert_eq!(h(&[1, 3], 0), None);
    }
}
