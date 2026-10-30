// Six-node ADD/ADDMOD DAG scheduler. Inputs 1,2,3 start as [1,3,2];
// nodes 4..9 run once. One trailing garbage slot is allowed. The graph,
// fixed boundary and working window restrict any optimality statement.

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};

const DEAD: u8 = 10;
pub const ALL: u8 = 63;
pub type Move = (u32, u8, Vec<u8>, u8);

pub struct Dag {
    pub ops: [(u8, u8, bool); 6],
    pub goal: [u8; 4],
    pub names: [&'static str; 6],
}

impl Dag {
    pub fn need(&self, v: u8, done: u8) -> usize {
        if v == 0 {
            return self.goal.iter().filter(|&&v| v == 0).count()
                + self
                    .ops
                    .iter()
                    .enumerate()
                    .filter(|(i, op)| done & (1 << i) == 0 && op.2)
                    .count();
        }
        usize::from(self.goal.contains(&v))
            + self
                .ops
                .iter()
                .enumerate()
                .filter(|(i, _)| done & (1 << i) == 0)
                .map(|(_, &(a, b, _))| usize::from(a == v) + usize::from(b == v))
                .sum::<usize>()
    }

    pub fn h(&self, stack: &[u8], done: u8) -> Option<u32> {
        let mut cost: u32 = self
            .ops
            .iter()
            .enumerate()
            .filter(|(i, _)| done & (1 << i) == 0)
            .map(|(_, op)| if op.2 { 8 } else { 3 })
            .sum();
        let count = |v| stack.iter().filter(|&&x| x == v).count();
        cost += 3 * self.need(0, done).saturating_sub(count(0)) as u32;
        for v in 1..=9 {
            let uses = self.need(v, done);
            let computed = v < 4 || done & (1 << (v - 4)) != 0;
            let have = if computed { count(v) } else { 1 };
            if computed && uses > 0 && have == 0 {
                return None;
            }
            cost += 3 * uses.saturating_sub(have) as u32;
        }
        Some(cost)
    }

    pub fn canon(&self, stack: &mut [u8], done: u8) {
        for v in stack {
            if *v != 0 && self.need(*v, done) == 0 {
                *v = DEAD;
            }
        }
    }

    pub fn goal(&self, stack: &[u8], done: u8) -> bool {
        done == ALL && (4..=5).contains(&stack.len()) && stack[..4] == self.goal
    }

    pub fn name(&self, code: u8) -> String {
        match code {
            1..=16 => format!("dup{code}"),
            17..=31 => format!("swap{}", code - 16),
            40 => "P".into(),
            41 => "pop".into(),
            42..=47 => {
                let i = usize::from(code - 42);
                format!(
                    "{}={}",
                    if self.ops[i].2 { "addmod" } else { "add" },
                    self.names[i]
                )
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

    pub fn moves(&self, stack: &[u8], done: u8, window: usize, exchange: bool) -> Vec<Move> {
        let mut out = Vec::new();
        let n = stack.len();
        if n < window {
            let mut seen = [false; 11];
            for (k, &v) in stack.iter().enumerate() {
                if v == 0 || v == DEAD || seen[v as usize] {
                    continue;
                }
                seen[v as usize] = true;
                if self.need(v, done) > 0 {
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
        for (i, &(a, b, reduce)) in self.ops.iter().enumerate() {
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

    pub fn replay(&self, program: &str, window: usize, exchange: bool) -> Result<u32, String> {
        let (mut stack, mut done, mut cost) = (vec![1, 3, 2], 0, 0);
        let mut trace = vec![(stack.clone(), done, cost)];
        for op in program.split_whitespace() {
            let (gas, _, next, mask) = self
                .moves(&stack, done, window, exchange)
                .into_iter()
                .find(|(_, code, _, _)| self.name(*code) == op)
                .ok_or_else(|| format!("unavailable replay move {op}"))?;
            cost += gas;
            stack = next;
            done = mask;
            self.canon(&mut stack, done);
            trace.push((stack.clone(), done, cost));
        }
        if !self.goal(&stack, done) {
            return Err("replay goal".into());
        }
        for (stack, done, spent) in trace {
            if !self.h(&stack, done).is_some_and(|h| h <= cost - spent) {
                return Err("replay suffix bound".into());
            }
        }
        Ok(cost)
    }

    pub fn run(&self, window: usize, ub: u32, exchange: bool) -> Result<(), String> {
        if !(4..=16).contains(&window) {
            return Err("window must be in 4..16".into());
        }
        if let Ok(program) = std::env::var("REPLAY") {
            println!("replay cost {}", self.replay(&program, window, exchange)?);
            return Ok(());
        }
        let start = pack(&[1, 3, 2], 0);
        let mut best: HashMap<u128, (u32, Option<(u128, u8)>)> = HashMap::new();
        best.insert(start, (0, None));
        let mut queue = BinaryHeap::new();
        let floor = self.h(&[1, 3, 2], 0).expect("raw inputs");
        eprintln!(
            "funded root bound {floor}, upper bound {ub}, window {window}, exchange {exchange}"
        );
        queue.push((Reverse(floor), 0, start));
        let mut expanded = 0u64;
        while let Some((Reverse(f), gas, key)) = queue.pop() {
            if best[&key].0 < gas {
                continue;
            }
            if f >= ub {
                break;
            }
            let (stack, done) = unpack(key);
            if self.goal(&stack, done) {
                let mut path = Vec::new();
                let mut at = key;
                while let Some((parent, code)) = best[&at].1 {
                    path.push(self.name(code));
                    at = parent;
                }
                path.reverse();
                let dsl = path.join(" ");
                assert_eq!(self.replay(&dsl, window, exchange)?, gas);
                println!("cost {gas}, expanded {expanded}, states {}", best.len());
                println!("dsl: {dsl}");
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
            for (cost, code, mut next, mask) in self.moves(&stack, done, window, exchange) {
                self.canon(&mut next, mask);
                let ng = gas + cost;
                let Some(bound) = self.h(&next, mask) else {
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
}

pub fn pack(stack: &[u8], done: u8) -> u128 {
    let mut k = 0u128;
    for &v in stack.iter().rev() {
        k = (k << 4) | u128::from(v);
    }
    k | (u128::from(done) << 64) | ((stack.len() as u128) << 72)
}

pub fn unpack(key: u128) -> (Vec<u8>, u8) {
    let n = (key >> 72) as usize;
    let stack = (0..n).map(|i| ((key >> (4 * i)) & 15) as u8).collect();
    (stack, ((key >> 64) & 63) as u8)
}
