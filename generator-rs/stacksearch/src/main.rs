// Exhaustive (A*) search over EVM stack programs for one Poseidon2 external
// round block: the S-boxes of the lanes and the linear layer, from a given
// input layout to a given output layout. Values are linear forms over the
// S-box outputs with a bound in units of P (ADD allowed while the bound stays
// <= 5, since 5P < 2^256 < 6P). Only a whitelist of useful forms is allowed.
//
//   stacksearch <t> <init layout> <goal layout> [reach] [max_garbage] [extra_depth] [run] [swaps]
//
// layouts are comma separated names, top first, e.g. "s0,P,s1,s2,s3" and
// "t6,P,t5,t7,t4"; "x0.." in the init are already S-boxed inputs; "_" in the
// goal is a wildcard. `run` bounds the stack moves between two arithmetic
// ops, `swaps` the swaps among them.

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Val,
    Input(u8),
    Prime,
    Four,
}

#[derive(Clone, Debug)]
struct Class {
    coeffs: [i32; 4],
    bound: u8,
    name: String,
    kind: Kind,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Op {
    Dup(u8),
    Swap(u8),
    PushP,
    Push4,
    Pop,
    Add,
    Addmod,
    Mulmod,
    SboxP(u8),
    SboxNoP(u8),
}

impl Op {
    fn is_move(self) -> bool {
        matches!(self, Op::Dup(_) | Op::Swap(_) | Op::PushP | Op::Push4)
    }
}

/// how a class can be produced: operands (class ids) and the op
#[derive(Clone, Debug)]
struct Production {
    operands: Vec<u8>,
    mulmod: bool,
    addmod: bool,
}

struct Problem {
    classes: Vec<Class>,
    prime: u8,
    four: u8,
    /// x_i class of input s_i
    sbox_out: Vec<u8>,
    sbox_in: Vec<u8>,
    init: Vec<u8>,
    init_computed: u32,
    goal: Vec<Option<u8>>,
    goal_set: u32,
    reach: usize,
    max_depth: usize,
    max_garbage: usize,
    max_run: u8,
    max_swaps: u8,
    /// heuristic groups: (members, op cost); a group needs one op while no
    /// member is computed
    groups: Vec<(Vec<u8>, u32)>,
    consumers: Vec<Vec<u8>>,
    productions: Vec<Vec<Production>>,
    by_form: HashMap<([i32; 4], u8), u8>,
}

const SBOX_P: u32 = 45; // C add + dupP dupP dup3 dup1 mulmod dup1 mulmod mulmod
const SBOX_NOP: u32 = 48; // C add + dupP dup2 dup1 mulmod dupP swap1 dup1 mulmod dupP swap2 mulmod

#[derive(Clone)]
struct St {
    stack: Vec<u8>,
    computed: u32,
    /// stack moves since the last arithmetic op, swaps among them
    run: u8,
    swaps: u8,
}

fn key(st: &St) -> u128 {
    let mut k: u128 = 0;
    for &c in &st.stack {
        k = (k << 5) | (c as u128 + 1);
    }
    (k << 32) | st.computed as u128 | ((st.run as u128) << 120) | ((st.swaps as u128) << 124)
}

impl Problem {
    fn needed_mask(&self, computed: u32) -> u32 {
        let n = self.classes.len();
        let mut memo = vec![0u8; n];
        fn rec(p: &Problem, c: usize, computed: u32, memo: &mut Vec<u8>, visiting: &mut Vec<bool>) -> bool {
            if memo[c] != 0 {
                return memo[c] == 2;
            }
            if visiting[c] {
                return false;
            }
            visiting[c] = true;
            let mut res = p.goal_set & (1 << c) != 0;
            if !res {
                for &e in &p.consumers[c] {
                    if computed & (1 << e) == 0 && rec(p, e as usize, computed, memo, visiting) {
                        res = true;
                        break;
                    }
                }
            }
            visiting[c] = false;
            memo[c] = if res { 2 } else { 1 };
            res
        }
        let mut mask = 0u32;
        let mut visiting = vec![false; n];
        for c in 0..n {
            if rec(self, c, computed, &mut memo, &mut visiting) {
                mask |= 1 << c;
            }
        }
        mask
    }

    fn heuristic(&self, stack: &[u8], computed: u32, needed: u32) -> u32 {
        let n = self.classes.len();
        let mut h = 0;
        let mut p_needed = 0i32;
        let mut four_needed = 0i32;
        // remaining uses per class: per open group, the min over its members
        // and their productions of the multiplicity
        let mut uses = vec![0i32; n];
        for (members, cost) in &self.groups {
            let any_computed = members.iter().any(|&m| computed & (1 << m) != 0);
            let any_needed = members.iter().any(|&m| needed & (1 << m) != 0);
            if any_computed || !any_needed {
                continue;
            }
            h += cost;
            let mut needs_p = true;
            let mut needs_4 = true;
            let mut min_use = vec![i32::MAX; n];
            for &m in members {
                for prod in &self.productions[m as usize] {
                    if !prod.addmod && !prod.mulmod {
                        needs_p = false;
                    }
                    if !prod.mulmod {
                        needs_4 = false;
                    }
                    let mut mult = vec![0i32; n];
                    for &o in &prod.operands {
                        mult[o as usize] += 1;
                    }
                    for c in 0..n {
                        if mult[c] < min_use[c] {
                            min_use[c] = mult[c];
                        }
                    }
                }
            }
            if needs_p {
                p_needed += 1;
            }
            if needs_4 {
                four_needed += 1;
            }
            for c in 0..n {
                if min_use[c] != i32::MAX {
                    uses[c] += min_use[c];
                }
            }
        }
        for &x in &self.sbox_out {
            if computed & (1 << x) == 0 && needed & (1 << x) != 0 {
                h += SBOX_P;
                p_needed += 1;
            }
        }
        let p_copies = stack.iter().filter(|&&c| c == self.prime).count() as i32;
        let four_copies = stack.iter().filter(|&&c| c == self.four).count() as i32;
        h += 3 * (p_needed - p_copies).max(0) as u32;
        h += 3 * (four_needed - four_copies).max(0) as u32;
        // goal copies
        for g in self.goal.iter().flatten() {
            if self.classes[*g as usize].kind == Kind::Val {
                uses[*g as usize] += 1;
            }
        }
        for c in 0..n {
            if self.classes[c].kind != Kind::Val || computed & (1 << c) == 0 {
                continue;
            }
            let copies = stack.iter().filter(|&&x| x as usize == c).count() as i32;
            h += 3 * (uses[c] - copies).max(0) as u32;
        }
        h
    }

    fn is_goal(&self, stack: &[u8]) -> bool {
        if stack.len() < self.goal.len() {
            return false;
        }
        self.goal
            .iter()
            .enumerate()
            .all(|(i, g)| g.map_or(true, |g| stack[i] == g))
    }

    fn garbage(&self, stack: &[u8], needed: u32) -> usize {
        stack
            .iter()
            .filter(|&&c| match self.classes[c as usize].kind {
                Kind::Val | Kind::Input(_) => needed & (1 << c) == 0,
                _ => false,
            })
            .count()
    }

    fn apply(&self, st: &St, needed: u32, op: Op) -> Option<(St, u32)> {
        let stack = &st.stack;
        let computed = st.computed;
        let len = stack.len();
        let cls = |c: u8| &self.classes[c as usize];
        if op.is_move() && st.run >= self.max_run {
            return None;
        }
        let (run, swaps) = if op.is_move() {
            (st.run + 1, st.swaps + matches!(op, Op::Swap(_)) as u8)
        } else {
            (0, 0)
        };
        let mk = |stack: Vec<u8>, computed: u32| St { stack, computed, run, swaps };
        match op {
            Op::Dup(k) => {
                let k = k as usize;
                if k < 1 || k > len || k > self.reach || len >= self.max_depth {
                    return None;
                }
                let v = stack[k - 1];
                match cls(v).kind {
                    Kind::Val | Kind::Input(_) => {}
                    _ => return None,
                }
                if needed & (1 << v) == 0 {
                    return None;
                }
                let mut s = Vec::with_capacity(len + 1);
                s.push(v);
                s.extend_from_slice(stack);
                Some((mk(s, computed), 3))
            }
            Op::Swap(k) => {
                let k = k as usize;
                if k < 1 || k >= len || k > self.reach || st.swaps >= self.max_swaps {
                    return None;
                }
                if stack[0] == stack[k] {
                    return None;
                }
                let mut s = stack.to_vec();
                s.swap(0, k);
                Some((mk(s, computed), 3))
            }
            Op::PushP => {
                if len >= self.max_depth {
                    return None;
                }
                let count = stack.iter().filter(|&&c| c == self.prime).count();
                if count >= 3 {
                    return None;
                }
                let mut s = Vec::with_capacity(len + 1);
                s.push(self.prime);
                s.extend_from_slice(stack);
                Some((mk(s, computed), 3))
            }
            Op::Push4 => {
                if len >= self.max_depth {
                    return None;
                }
                if stack.iter().any(|&c| c == self.four) {
                    return None;
                }
                let mut s = Vec::with_capacity(len + 1);
                s.push(self.four);
                s.extend_from_slice(stack);
                Some((mk(s, computed), 3))
            }
            Op::Pop => {
                if len == 0 {
                    return None;
                }
                let v = stack[0];
                let dead = match cls(v).kind {
                    Kind::Val | Kind::Input(_) => needed & (1 << v) == 0,
                    Kind::Prime | Kind::Four => true,
                };
                if !dead {
                    return None;
                }
                Some((mk(stack[1..].to_vec(), computed), 2))
            }
            Op::Add => {
                if len < 2 {
                    return None;
                }
                let (a, b) = (cls(stack[0]), cls(stack[1]));
                if a.kind != Kind::Val || b.kind != Kind::Val {
                    return None;
                }
                let bound = a.bound + b.bound;
                if bound > 5 {
                    return None;
                }
                let mut coeffs = [0i32; 4];
                for i in 0..4 {
                    coeffs[i] = a.coeffs[i] + b.coeffs[i];
                }
                let &c = self.by_form.get(&(coeffs, bound))?;
                if computed & (1 << c) != 0 || needed & (1 << c) == 0 {
                    return None;
                }
                let mut s = Vec::with_capacity(len - 1);
                s.push(c);
                s.extend_from_slice(&stack[2..]);
                Some((mk(s, computed | (1 << c)), 3))
            }
            Op::Addmod => {
                if len < 3 || stack[2] != self.prime {
                    return None;
                }
                let (a, b) = (cls(stack[0]), cls(stack[1]));
                if a.kind != Kind::Val || b.kind != Kind::Val {
                    return None;
                }
                let mut coeffs = [0i32; 4];
                for i in 0..4 {
                    coeffs[i] = a.coeffs[i] + b.coeffs[i];
                }
                let &c = self.by_form.get(&(coeffs, 1))?;
                if computed & (1 << c) != 0 || needed & (1 << c) == 0 {
                    return None;
                }
                let mut s = Vec::with_capacity(len - 2);
                s.push(c);
                s.extend_from_slice(&stack[3..]);
                Some((mk(s, computed | (1 << c)), 8))
            }
            Op::Mulmod => {
                if len < 3 || stack[2] != self.prime {
                    return None;
                }
                let (a, b) = (stack[0], stack[1]);
                let v = if a == self.four && cls(b).kind == Kind::Val {
                    b
                } else if b == self.four && cls(a).kind == Kind::Val {
                    a
                } else {
                    return None;
                };
                let mut coeffs = [0i32; 4];
                for i in 0..4 {
                    coeffs[i] = cls(v).coeffs[i] * 4;
                }
                let &c = self.by_form.get(&(coeffs, 1))?;
                if computed & (1 << c) != 0 || needed & (1 << c) == 0 {
                    return None;
                }
                let mut s = Vec::with_capacity(len - 2);
                s.push(c);
                s.extend_from_slice(&stack[3..]);
                Some((mk(s, computed | (1 << c)), 8))
            }
            Op::SboxP(i) | Op::SboxNoP(i) => {
                if len < 1 {
                    return None;
                }
                let top = stack[0];
                if cls(top).kind != Kind::Input(i) {
                    return None;
                }
                let x = self.sbox_out[i as usize];
                if computed & (1 << x) != 0 {
                    return None;
                }
                let with_p = matches!(op, Op::SboxP(_));
                if with_p {
                    if len < 2 || stack[1] != self.prime {
                        return None;
                    }
                    let mut s = Vec::with_capacity(len - 1);
                    s.push(x);
                    s.extend_from_slice(&stack[2..]);
                    Some((mk(s, computed | (1 << x)), SBOX_P))
                } else {
                    let mut s = Vec::with_capacity(len);
                    s.push(x);
                    s.extend_from_slice(&stack[1..]);
                    Some((mk(s, computed | (1 << x)), SBOX_NOP))
                }
            }
        }
    }

    fn ops(&self, len: usize) -> Vec<Op> {
        let mut ops = Vec::new();
        ops.push(Op::Add);
        ops.push(Op::Addmod);
        ops.push(Op::Mulmod);
        for i in 0..self.sbox_in.len() {
            ops.push(Op::SboxP(i as u8));
            ops.push(Op::SboxNoP(i as u8));
        }
        ops.push(Op::PushP);
        ops.push(Op::Push4);
        ops.push(Op::Pop);
        for k in 1..=len.min(self.reach) {
            ops.push(Op::Dup(k as u8));
        }
        for k in 1..len.min(self.reach + 1) {
            ops.push(Op::Swap(k as u8));
        }
        ops
    }
}

struct Node {
    key: u128,
    g: u32,
    parent: u32,
    op: Option<Op>,
}

fn decode(p: &Problem, key: u128) -> St {
    let run = ((key >> 120) & 0xf) as u8;
    let swaps = ((key >> 124) & 0xf) as u8;
    let computed = (key & 0xffff_ffff) as u32;
    let mut k = (key >> 32) & ((1u128 << 88) - 1);
    let mut stack = Vec::new();
    while k != 0 {
        stack.push((k & 31) as u8 - 1);
        k >>= 5;
    }
    stack.reverse();
    let _ = p;
    St { stack, computed, run, swaps }
}

fn search(p: &Problem) -> Option<(u32, Vec<(Op, Vec<u8>, u32)>)> {
    let mut nodes: Vec<Node> = Vec::new();
    let mut best: HashMap<u128, u32> = HashMap::new();
    let mut heap: BinaryHeap<(Reverse<u32>, u32, u32)> = BinaryHeap::new();
    let init = St { stack: p.init.clone(), computed: p.init_computed, run: 0, swaps: 0 };
    let k0 = key(&init);
    nodes.push(Node { key: k0, g: 0, parent: u32::MAX, op: None });
    best.insert(k0, 0);
    let needed0 = p.needed_mask(p.init_computed);
    heap.push((Reverse(p.heuristic(&init.stack, init.computed, needed0)), 0, 0));
    let mut expanded = 0usize;
    while let Some((Reverse(_f), g, idx)) = heap.pop() {
        let st = decode(p, nodes[idx as usize].key);
        if best.get(&nodes[idx as usize].key).copied().unwrap_or(u32::MAX) < g {
            continue;
        }
        if p.is_goal(&st.stack) {
            let mut path = Vec::new();
            let mut cur = idx;
            while nodes[cur as usize].parent != u32::MAX {
                let s = decode(p, nodes[cur as usize].key);
                path.push((nodes[cur as usize].op.unwrap(), s.stack, nodes[cur as usize].g));
                cur = nodes[cur as usize].parent;
            }
            path.reverse();
            eprintln!("expanded {expanded} nodes, {} states", best.len());
            return Some((g, path));
        }
        expanded += 1;
        if expanded % 1_000_000 == 0 {
            eprintln!("expanded {expanded}, states {}, g {g} f {}", best.len(), _f);
        }
        let needed = p.needed_mask(st.computed);
        for op in p.ops(st.stack.len()) {
            if let Some((s2, cost)) = p.apply(&st, needed, op) {
                let needed2 = if s2.computed != st.computed { p.needed_mask(s2.computed) } else { needed };
                if p.garbage(&s2.stack, needed2) > p.max_garbage {
                    continue;
                }
                let g2 = g + cost;
                let k2 = key(&s2);
                if best.get(&k2).copied().unwrap_or(u32::MAX) <= g2 {
                    continue;
                }
                best.insert(k2, g2);
                let h = p.heuristic(&s2.stack, s2.computed, needed2);
                nodes.push(Node { key: k2, g: g2, parent: idx, op: Some(op) });
                heap.push((Reverse(g2 + h), g2, (nodes.len() - 1) as u32));
            }
        }
    }
    None
}

fn build(t: usize, final_round: bool) -> (Vec<Class>, Vec<(Vec<String>, u32)>) {
    let mut classes = Vec::new();
    let mut add = |name: &str, coeffs: [i32; 4], bound: u8, kind: Kind| {
        classes.push(Class { coeffs, bound, name: name.to_string(), kind });
    };
    add("P", [0; 4], 0, Kind::Prime);
    add("4", [0; 4], 0, Kind::Four);
    for i in 0..t {
        add(&format!("s{i}"), [0; 4], 0, Kind::Input(i as u8));
    }
    for i in 0..t {
        let mut c = [0; 4];
        c[i] = 1;
        add(&format!("x{i}"), c, 1, Kind::Val);
    }
    let mut groups: Vec<(Vec<String>, u32)> = Vec::new();
    let g = |groups: &mut Vec<(Vec<String>, u32)>, names: &[&str], cost: u32| {
        groups.push((names.iter().map(|s| s.to_string()).collect(), cost));
    };
    match t {
        2 => {
            add("2x0", [2, 0, 0, 0], 2, Kind::Val);
            add("2x1", [0, 2, 0, 0], 2, Kind::Val);
            add("sum", [1, 1, 0, 0], 2, Kind::Val);
            if final_round {
                add("o0", [2, 1, 0, 0], 1, Kind::Val);
                add("o1", [1, 2, 0, 0], 1, Kind::Val);
                g(&mut groups, &["o0"], 8);
                g(&mut groups, &["o1"], 8);
            } else {
                add("o0", [2, 1, 0, 0], 3, Kind::Val);
                add("o1", [1, 2, 0, 0], 3, Kind::Val);
                g(&mut groups, &["o0"], 3);
                g(&mut groups, &["o1"], 3);
            }
        }
        3 => {
            for a in 0..=2 {
                for b in 0..=2 {
                    for c in 0..=2 {
                        let s = a + b + c;
                        if s < 2 || s > 4 {
                            continue;
                        }
                        let n = [a, b, c].iter().filter(|&&v| v == 2).count();
                        if n > 1 {
                            continue;
                        }
                        let (name, bound) = if [a, b, c] == [1, 1, 1] {
                            ("sum".to_string(), 3)
                        } else if [a, b, c] == [2, 1, 1] {
                            ("o0".to_string(), if final_round { 1 } else { 4 })
                        } else if [a, b, c] == [1, 2, 1] {
                            ("o1".to_string(), if final_round { 1 } else { 4 })
                        } else if [a, b, c] == [1, 1, 2] {
                            ("o2".to_string(), if final_round { 1 } else { 4 })
                        } else {
                            (format!("{a}{b}{c}"), s as u8)
                        };
                        add(&name, [a, b, c, 0], bound, Kind::Val);
                    }
                }
            }
            let cost = if final_round { 8 } else { 3 };
            g(&mut groups, &["o0"], cost);
            g(&mut groups, &["o1"], cost);
            g(&mut groups, &["o2"], cost);
        }
        4 => {
            add("t0", [1, 1, 0, 0], 2, Kind::Val);
            add("t1", [0, 0, 1, 1], 2, Kind::Val);
            add("2x1", [0, 2, 0, 0], 2, Kind::Val);
            add("2x3", [0, 0, 0, 2], 2, Kind::Val);
            add("u1", [0, 1, 1, 1], 3, Kind::Val);
            add("u3", [1, 1, 0, 1], 3, Kind::Val);
            add("t2", [0, 2, 1, 1], 1, Kind::Val);
            add("t3", [1, 1, 0, 2], 1, Kind::Val);
            add("4t0", [4, 4, 0, 0], 1, Kind::Val);
            add("4t1", [0, 0, 4, 4], 1, Kind::Val);
            if final_round {
                add("t4", [1, 1, 4, 6], 1, Kind::Val);
                add("t5", [4, 6, 1, 1], 1, Kind::Val);
                add("t6", [5, 7, 1, 3], 1, Kind::Val);
                add("t7", [1, 3, 5, 7], 1, Kind::Val);
            } else {
                add("t4", [1, 1, 4, 6], 2, Kind::Val);
                add("t5", [4, 6, 1, 1], 2, Kind::Val);
                add("t6", [5, 7, 1, 3], 3, Kind::Val);
                add("t7", [1, 3, 5, 7], 3, Kind::Val);
                add("t23", [1, 3, 1, 3], 2, Kind::Val);
            }
            let oc = if final_round { 8 } else { 3 };
            g(&mut groups, &["t0"], 3);
            g(&mut groups, &["t1"], 3);
            g(&mut groups, &["2x1", "u1"], 3);
            g(&mut groups, &["2x3", "u3"], 3);
            g(&mut groups, &["t2"], 8);
            g(&mut groups, &["t3"], 8);
            g(&mut groups, &["4t0"], 8);
            g(&mut groups, &["4t1"], 8);
            g(&mut groups, &["t4"], oc);
            g(&mut groups, &["t5"], oc);
            g(&mut groups, &["t6"], oc);
            g(&mut groups, &["t7"], oc);
        }
        _ => panic!("t"),
    }
    (classes, groups)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let t: usize = args[1].parse().unwrap();
    let init_names: Vec<&str> = args[2].split(',').collect();
    let goal_names: Vec<&str> = args[3].split(',').collect();
    let reach: usize = args.get(4).map_or(16, |s| s.parse().unwrap());
    let max_garbage: usize = args.get(5).map_or(2, |s| s.parse().unwrap());
    let extra_depth: usize = args.get(6).map_or(8, |s| s.parse().unwrap());
    let max_run: u8 = args.get(7).map_or(6, |s| s.parse().unwrap());
    let max_swaps: u8 = args.get(8).map_or(2, |s| s.parse().unwrap());
    let final_round = args.get(9).map_or(false, |s| s == "final");
    let (classes, groups) = build(t, final_round);
    let idx = |n: &str| -> u8 {
        classes
            .iter()
            .position(|c| c.name == n)
            .unwrap_or_else(|| panic!("unknown {n}")) as u8
    };
    let prime = idx("P");
    let four = idx("4");
    let sbox_out: Vec<u8> = (0..t).map(|i| idx(&format!("x{i}"))).collect();
    let sbox_in: Vec<u8> = (0..t).map(|i| idx(&format!("s{i}"))).collect();
    let init: Vec<u8> = init_names.iter().map(|n| idx(n)).collect();
    let mut init_computed = 0u32;
    for &c in &init {
        if classes[c as usize].kind == Kind::Val {
            init_computed |= 1 << c;
        }
    }
    let goal: Vec<Option<u8>> = goal_names
        .iter()
        .map(|n| if *n == "_" { None } else { Some(idx(n)) })
        .collect();
    let mut goal_set = 0u32;
    for g in goal.iter().flatten() {
        if classes[*g as usize].kind == Kind::Val {
            goal_set |= 1 << g;
        }
    }
    let mut by_form = HashMap::new();
    for (i, c) in classes.iter().enumerate() {
        if c.kind == Kind::Val {
            by_form.insert((c.coeffs, c.bound), i as u8);
        }
    }
    let n = classes.len();
    let mut consumers = vec![Vec::new(); n];
    let mut productions: Vec<Vec<Production>> = vec![Vec::new(); n];
    for d in 0..n {
        let dc = &classes[d];
        if dc.kind != Kind::Val {
            continue;
        }
        // sbox
        for (i, &x) in sbox_out.iter().enumerate() {
            if x as usize == d {
                productions[d].push(Production { operands: vec![sbox_in[i]], mulmod: false, addmod: false });
                consumers[sbox_in[i] as usize].push(d as u8);
            }
        }
        // add / addmod: d = c + e
        for c in 0..n {
            let cc = &classes[c];
            if cc.kind != Kind::Val {
                continue;
            }
            let mut rem = [0i32; 4];
            let mut ok = true;
            for i in 0..4 {
                rem[i] = dc.coeffs[i] - cc.coeffs[i];
                if rem[i] < 0 {
                    ok = false;
                }
            }
            if !ok {
                continue;
            }
            for e in c..n {
                let ec = &classes[e];
                if ec.kind != Kind::Val || ec.coeffs != rem {
                    continue;
                }
                if ec.bound + cc.bound == dc.bound {
                    productions[d].push(Production { operands: vec![c as u8, e as u8], mulmod: false, addmod: false });
                } else if dc.bound == 1 {
                    productions[d].push(Production { operands: vec![c as u8, e as u8], mulmod: false, addmod: true });
                } else {
                    continue;
                }
                if !consumers[c].contains(&(d as u8)) {
                    consumers[c].push(d as u8);
                }
                if !consumers[e].contains(&(d as u8)) {
                    consumers[e].push(d as u8);
                }
            }
            // mulmod by 4
            if dc.bound == 1 && cc.coeffs != [0; 4] && (0..4).all(|i| dc.coeffs[i] == 4 * cc.coeffs[i]) {
                productions[d].push(Production { operands: vec![c as u8], mulmod: true, addmod: false });
                if !consumers[c].contains(&(d as u8)) {
                    consumers[c].push(d as u8);
                }
            }
        }
    }
    let groups: Vec<(Vec<u8>, u32)> = groups
        .iter()
        .map(|(names, cost)| (names.iter().map(|n| idx(n)).collect(), *cost))
        .collect();
    let max_depth = (init.len() + extra_depth).min(17);
    let p = Problem {
        classes,
        prime,
        four,
        sbox_out,
        sbox_in,
        init,
        init_computed,
        goal,
        goal_set,
        reach,
        max_depth,
        max_garbage,
        max_run,
        max_swaps,
        groups,
        consumers,
        productions,
        by_form,
    };
    match search(&p) {
        Some((cost, path)) => {
            println!("cost {cost}");
            for (op, stack, g) in path {
                let names: Vec<&str> = stack.iter().map(|&c| p.classes[c as usize].name.as_str()).collect();
                println!("{:<12} {:>4}  [{}]", format!("{op:?}"), g, names.join(", "));
            }
        }
        None => println!("no solution"),
    }
}
