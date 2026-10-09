// A* over macro moves for one Poseidon2 external round block (see main.rs
// for the value model). A macro is the next arithmetic op with its
// production and, per operand, whether it is consumed in place or copied;
// in-place operands are brought to the top with a swap sequence from a
// precomputed table (at most 3 swaps), copies are DUPed (constants pushed)
// on top. A chain pre-places the operands of the op that consumes the
// result in place (the addTo pattern). Standalone PushP, Pop and shallow
// Swap moves arrange the goal layout.
//
//   macro <t> <init> <goal> [reach] [max_garbage] [extra_depth] [final] [chain]

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap, VecDeque};

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
enum Prim {
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

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum PKind {
    Add,
    Addmod,
    Mulmod,
    Sbox,
}

#[derive(Clone, Debug)]
struct Production {
    operands: Vec<u8>,
    kind: PKind,
}

const SBOX_P: u32 = 45;
const SBOX_NOP: u32 = 54;

struct Problem {
    classes: Vec<Class>,
    prime: u8,
    four: u8,
    sbox_out: Vec<u8>,
    sbox_in: Vec<u8>,
    init: Vec<u8>,
    init_computed: u32,
    goal: Vec<Option<u8>>,
    goal_set: u32,
    reach: usize,
    max_depth: usize,
    max_garbage: usize,
    chain: usize,
    strict: bool,
    groups: Vec<(Vec<u8>, u32)>,
    consumers: Vec<Vec<u8>>,
    productions: Vec<Vec<Production>>,
    /// swap sequences: positions (top-first, 1-based) of m items -> swaps
    /// that bring them to slots 1..m in that order
    swaps: HashMap<Vec<u8>, Vec<u8>>,
}

#[derive(Clone, Debug)]
struct St {
    stack: Vec<u8>,
    computed: u32,
}

#[derive(Clone, Copy, Debug)]
enum Item {
    Copy(u8),
    Inplace(u8),
    P,
    Four,
}

fn key(st: &St) -> u128 {
    let mut k: u128 = 0;
    for &c in &st.stack {
        k = (k << 5) | (c as u128 + 1);
    }
    (k << 32) | st.computed as u128
}

fn decode(key: u128) -> St {
    let computed = (key & 0xffff_ffff) as u32;
    let mut k = key >> 32;
    let mut stack = Vec::new();
    while k != 0 {
        stack.push((k & 31) as u8 - 1);
        k >>= 5;
    }
    stack.reverse();
    St { stack, computed }
}

/// Backward BFS over swap sequences: for m marked items, every position
/// tuple reachable from (1..m) within `depth` swaps.
fn swap_table(m: usize, reach: usize, depth: usize) -> HashMap<Vec<u8>, Vec<u8>> {
    let mut table: HashMap<Vec<u8>, Vec<u8>> = HashMap::new();
    let goal: Vec<u8> = (1..=m as u8).collect();
    table.insert(goal.clone(), Vec::new());
    let mut queue = VecDeque::new();
    queue.push_back(goal);
    while let Some(pos) = queue.pop_front() {
        let seq = table[&pos].clone();
        if seq.len() >= depth {
            continue;
        }
        for n in 1..=reach as u8 {
            // Swap(n) exchanges slot 1 and slot n + 1
            let mut next = pos.clone();
            for p in next.iter_mut() {
                if *p == 1 {
                    *p = n + 1;
                } else if *p == n + 1 {
                    *p = 1;
                }
            }
            if next.iter().any(|&p| p as usize > reach + 1) {
                continue;
            }
            if !table.contains_key(&next) {
                // the swaps to reach `next` from the goal reversed are the
                // swaps from `next` to the goal (a swap is its own inverse)
                let mut s = vec![n];
                s.extend_from_slice(&seq);
                table.insert(next.clone(), s);
                queue.push_back(next);
            }
        }
    }
    table
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
                    if prod.kind == PKind::Add {
                        needs_p = false;
                    }
                    if prod.kind != PKind::Mulmod {
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
        for c in 0..n {
            if self.goal_set & (1 << c) != 0 {
                uses[c] += 1;
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
        let mut seen = 0u32;
        for (i, g) in self.goal.iter().enumerate() {
            match g {
                None => {}
                Some(255) => {
                    let c = stack[i];
                    if self.goal_set & (1 << c) == 0 || seen & (1 << c) != 0 {
                        return false;
                    }
                    seen |= 1 << c;
                }
                Some(g) => {
                    if stack[i] != *g {
                        return false;
                    }
                }
            }
        }
        true
    }

    fn garbage(&self, stack: &[u8], needed: u32) -> usize {
        let dead = stack
            .iter()
            .filter(|&&c| match self.classes[c as usize].kind {
                Kind::Val | Kind::Input(_) => needed & (1 << c) == 0,
                _ => false,
            })
            .count();
        if !self.strict {
            return dead;
        }
        // strict: constants left over count as well, beyond the copies the
        // goal keeps
        let extra = |c: u8| {
            let on_stack = stack.iter().filter(|&&x| x == c).count();
            let kept = self.goal.iter().filter(|&&g| g == Some(c)).count();
            on_stack.saturating_sub(kept)
        };
        dead + extra(self.prime) + extra(self.four)
    }

    /// Brings the in-place items (top-first required order) to the top and
    /// pushes the copies (top-first order) above them. Returns the prims,
    /// the stack and the cost, or None when out of reach.
    fn realize(&self, stack: &[u8], inplace: &[u8], copies: &[Item], prims: &mut Vec<Prim>) -> Option<(Vec<u8>, u32)> {
        let mut s = stack.to_vec();
        let mut cost = 0;
        if !inplace.is_empty() {
            // positions: the shallowest copy of each, distinct slots
            let mut pos: Vec<u8> = Vec::new();
            for &c in inplace {
                let mut found = None;
                for (i, &x) in s.iter().enumerate() {
                    if x == c && !pos.contains(&(i as u8 + 1)) {
                        found = Some(i as u8 + 1);
                        break;
                    }
                }
                pos.push(found?);
            }
            let seq = match self.swaps.get(&pos) { Some(s) => s, None => { if std::env::var("DBG2").is_ok() { eprintln!("no swap seq for {:?} (table {})", pos, self.swaps.len()); } return None; } };
            for &n in seq {
                if n as usize >= s.len() {
                    return None;
                }
                s.swap(0, n as usize);
                prims.push(Prim::Swap(n));
                cost += 3;
            }
        }
        for item in copies.iter().rev() {
            if s.len() >= self.max_depth {
                return None;
            }
            match *item {
                Item::Copy(c) => {
                    let k = s.iter().position(|&x| x == c)? + 1;
                    if k > self.reach {
                        return None;
                    }
                    s.insert(0, c);
                    prims.push(Prim::Dup(k as u8));
                }
                Item::P => {
                    s.insert(0, self.prime);
                    prims.push(Prim::PushP);
                }
                Item::Four => {
                    s.insert(0, self.four);
                    prims.push(Prim::Push4);
                }
                Item::Inplace(_) => unreachable!(),
            }
            cost += 3;
        }
        Some((s, cost))
    }

    /// The operand layouts of a production: (in-place top-first, copies
    /// top-first, the op prim, its arity) for every in-place choice.
    fn layouts(&self, prod: &Production) -> Vec<(Vec<u8>, Vec<Item>, Prim, usize)> {
        let mut out = Vec::new();
        match prod.kind {
            PKind::Sbox => {
                let s = prod.operands[0];
                let lane = match self.classes[s as usize].kind {
                    Kind::Input(i) => i,
                    _ => unreachable!(),
                };
                out.push((vec![s], vec![], Prim::SboxNoP(lane), 1));
                out.push((vec![s, self.prime], vec![], Prim::SboxP(lane), 2));
                out.push((vec![], vec![Item::Copy(s)], Prim::SboxNoP(lane), 1));
                out.push((vec![], vec![Item::Copy(s), Item::P], Prim::SboxP(lane), 2));
                out.push((vec![self.prime], vec![Item::Copy(s)], Prim::SboxP(lane), 2));
            }
            PKind::Add => {
                let (a, b) = (prod.operands[0], prod.operands[1]);
                out.push((vec![], vec![Item::Copy(a), Item::Copy(b)], Prim::Add, 2));
                if a != b {
                    out.push((vec![], vec![Item::Copy(b), Item::Copy(a)], Prim::Add, 2));
                }
                out.push((vec![a], vec![Item::Copy(b)], Prim::Add, 2));
                if a != b {
                    out.push((vec![b], vec![Item::Copy(a)], Prim::Add, 2));
                }
                out.push((vec![a, b], vec![], Prim::Add, 2));
                if a != b {
                    out.push((vec![b, a], vec![], Prim::Add, 2));
                }
            }
            PKind::Addmod => {
                let (a, b) = (prod.operands[0], prod.operands[1]);
                let p = self.prime;
                out.push((vec![], vec![Item::Copy(a), Item::Copy(b), Item::P], Prim::Addmod, 3));
                if a != b {
                    out.push((vec![], vec![Item::Copy(b), Item::Copy(a), Item::P], Prim::Addmod, 3));
                }
                out.push((vec![p], vec![Item::Copy(a), Item::Copy(b)], Prim::Addmod, 3));
                if a != b {
                    out.push((vec![p], vec![Item::Copy(b), Item::Copy(a)], Prim::Addmod, 3));
                }
                out.push((vec![a, p], vec![Item::Copy(b)], Prim::Addmod, 3));
                if a != b {
                    out.push((vec![b, p], vec![Item::Copy(a)], Prim::Addmod, 3));
                }
                out.push((vec![a, b, p], vec![], Prim::Addmod, 3));
                if a != b {
                    out.push((vec![b, a, p], vec![], Prim::Addmod, 3));
                }
            }
            PKind::Mulmod => {
                let v = prod.operands[0];
                let p = self.prime;
                out.push((vec![], vec![Item::Four, Item::Copy(v), Item::P], Prim::Mulmod, 3));
                out.push((vec![], vec![Item::Copy(v), Item::Four, Item::P], Prim::Mulmod, 3));
                out.push((vec![p], vec![Item::Four, Item::Copy(v)], Prim::Mulmod, 3));
                out.push((vec![p], vec![Item::Copy(v), Item::Four], Prim::Mulmod, 3));
                out.push((vec![v, p], vec![Item::Four], Prim::Mulmod, 3));
            }
        }
        out
    }

    fn op_cost(prim: Prim) -> u32 {
        match prim {
            Prim::Add => 3,
            Prim::Addmod | Prim::Mulmod => 8,
            Prim::SboxP(_) => SBOX_P,
            Prim::SboxNoP(_) => SBOX_NOP,
            _ => unreachable!(),
        }
    }

    /// Every macro from a state: (prims, new state, cost).
    fn expand(&self, st: &St, needed: u32) -> Vec<(Vec<Prim>, St, u32)> {
        let mut out = Vec::new();
        let n = self.classes.len();
        // standalone moves
        if st.stack.len() < self.max_depth && st.stack.iter().filter(|&&c| c == self.prime).count() < 3 {
            let mut s = st.stack.clone();
            s.insert(0, self.prime);
            out.push((vec![Prim::PushP], St { stack: s, computed: st.computed }, 3));
        }
        if let Some(&top) = st.stack.first() {
            let dead = match self.classes[top as usize].kind {
                Kind::Val | Kind::Input(_) => needed & (1 << top) == 0,
                _ => true,
            };
            if dead {
                out.push((vec![Prim::Pop], St { stack: st.stack[1..].to_vec(), computed: st.computed }, 2));
            }
        }
        for k in 1..=4usize.min(st.stack.len().saturating_sub(1)) {
            if st.stack[0] != st.stack[k] {
                let mut s = st.stack.clone();
                s.swap(0, k);
                out.push((vec![Prim::Swap(k as u8)], St { stack: s, computed: st.computed }, 3));
            }
        }
        // arithmetic macros with chains
        for d in 0..n {
            if st.computed & (1 << d) != 0 || needed & (1 << d) == 0 {
                continue;
            }
            for prod in &self.productions[d] {
                // operands must exist
                if prod.operands.iter().any(|&o| self.classes[o as usize].kind == Kind::Val && st.computed & (1 << o) == 0) {
                    continue;
                }
                if prod.operands.iter().any(|&o| matches!(self.classes[o as usize].kind, Kind::Input(_)) && !st.stack.contains(&o)) {
                    continue;
                }
                self.chain(st, needed, d as u8, prod, &Vec::new(), &st.stack, 0, 0, &mut out);
            }
        }
        out
    }

    /// Macro of d via prod after `pre` prims (the pre-placements of the
    /// chain so far, giving `stack`), then recursively the ops the chain
    /// continues with.
    #[allow(clippy::too_many_arguments)]
    fn chain(
        &self,
        st: &St,
        needed: u32,
        d: u8,
        prod: &Production,
        pre: &Vec<Prim>,
        stack: &[u8],
        pre_cost: u32,
        depth: usize,
        out: &mut Vec<(Vec<Prim>, St, u32)>,
    ) {
        // chain continuation: an op consuming d in place with its other
        // operands pre-placed now
        if depth < self.chain {
            for &d2 in &self.consumers[d as usize] {
                if st.computed & (1 << d2) != 0 || needed & (1 << d2) == 0 {
                    continue;
                }
                for prod2 in &self.productions[d2 as usize] {
                    if !prod2.operands.contains(&d) || prod2.kind == PKind::Sbox {
                        continue;
                    }
                    // the other operands must be computed
                    let others: Vec<u8> = {
                        let mut v = prod2.operands.clone();
                        let i = v.iter().position(|&o| o == d).unwrap();
                        v.remove(i);
                        v
                    };
                    if others.iter().any(|&o| st.computed & (1 << o) == 0) {
                        continue;
                    }
                    // pre-placements: for add [b]; addmod [b, P]; mulmod [P] (4 after)
                    let variants: Vec<(Vec<u8>, Vec<Item>)> = match prod2.kind {
                        PKind::Add => {
                            let b = others[0];
                            vec![(vec![], vec![Item::Copy(b)]), (vec![b], vec![])]
                        }
                        PKind::Addmod => {
                            let b = others[0];
                            vec![
                                (vec![], vec![Item::Copy(b), Item::P]),
                                (vec![self.prime], vec![Item::Copy(b)]),
                                (vec![b, self.prime], vec![]),
                            ]
                        }
                        PKind::Mulmod => vec![(vec![], vec![Item::P]), (vec![self.prime], vec![])],
                        PKind::Sbox => unreachable!(),
                    };
                    for (inplace, copies) in variants {
                        let mut prims = pre.clone();
                        let Some((s2, c2)) = self.realize(stack, &inplace, &copies, &mut prims) else {
                            continue;
                        };
                        // continue the chain with d's macro on top of the pre-placement, then op2
                        let mut sub = Vec::new();
                        self.chain(st, needed, d, prod, &prims, &s2, pre_cost + c2, depth + 1, &mut sub);
                        for (mut p3, st3, c3) in sub {
                            // apply op2: d on top, operands below
                            let arity = match prod2.kind {
                                PKind::Add => 2,
                                _ => 3,
                            };
                            let mut s3 = st3.stack.clone();
                            if s3.len() < arity || s3[0] != d {
                                continue;
                            }
                            let prim = match prod2.kind {
                                PKind::Add => Prim::Add,
                                PKind::Addmod => Prim::Addmod,
                                PKind::Mulmod => {
                                    // push 4 on top of d
                                    if s3.len() >= self.max_depth {
                                        continue;
                                    }
                                    s3.insert(0, self.four);
                                    p3.push(Prim::Push4);
                                    Prim::Mulmod
                                }
                                PKind::Sbox => unreachable!(),
                            };
                            let extra = if prod2.kind == PKind::Mulmod { 3 } else { 0 };
                            // check operand layout
                            let ok = match prod2.kind {
                                PKind::Add => s3[1] == others[0],
                                PKind::Addmod => s3[1] == others[0] && s3[2] == self.prime,
                                PKind::Mulmod => s3[1] == d && s3[2] == self.prime,
                                PKind::Sbox => false,
                            };
                            if !ok {
                                continue;
                            }
                            let mut s4 = vec![d2];
                            s4.extend_from_slice(&s3[arity..]);
                            p3.push(prim);
                            let st4 = St { stack: s4, computed: st3.computed | (1 << d2) };
                            if self.valid(&st4) {
                                out.push((p3, st4, c3 + extra + Self::op_cost(prim)));
                            }
                        }
                    }
                }
            }
        }
        // d itself
        for (inplace, copies, prim, arity) in self.layouts(prod) {
            let mut prims = pre.clone();
            let Some((s2, c2)) = self.realize(stack, &inplace, &copies, &mut prims) else {
                continue;
            };
            // the in-place operands and the copies now sit on top; apply
            let mut s3 = vec![d];
            s3.extend_from_slice(&s2[arity..]);
            prims.push(prim);
            let st3 = St { stack: s3, computed: st.computed | (1 << d) };
            if self.valid(&st3) {
                out.push((prims, st3, pre_cost + c2 + Self::op_cost(prim)));
            }
        }
    }

    /// every goal value can still be produced from what is on the stack
    /// (a computed value that left the stack is lost), garbage within the
    /// limit
    fn valid(&self, st: &St) -> bool {
        let n = self.classes.len();
        let mut avail = vec![false; n];
        for &c in &st.stack {
            avail[c as usize] = true;
        }
        avail[self.prime as usize] = true;
        avail[self.four as usize] = true;
        loop {
            let mut changed = false;
            for d in 0..n {
                if avail[d] || st.computed & (1 << d) != 0 || self.classes[d].kind != Kind::Val {
                    continue;
                }
                if self.productions[d].iter().any(|prod| prod.operands.iter().all(|&o| avail[o as usize])) {
                    avail[d] = true;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        for c in 0..n {
            if self.goal_set & (1 << c) != 0 && !avail[c] {
                return false;
            }
        }
        let needed = self.needed_mask(st.computed);
        self.garbage(&st.stack, needed) <= self.max_garbage
    }
}

struct Node {
    key: u128,
    g: u32,
    parent: u32,
    prims: Vec<Prim>,
}

fn search(p: &Problem) -> Option<(u32, Vec<(Prim, Vec<u8>)>)> {
    let mut nodes: Vec<Node> = Vec::new();
    let mut best: HashMap<u128, u32> = HashMap::new();
    let mut heap: BinaryHeap<(Reverse<u32>, u32, u32)> = BinaryHeap::new();
    let init = St { stack: p.init.clone(), computed: p.init_computed };
    let k0 = key(&init);
    nodes.push(Node { key: k0, g: 0, parent: u32::MAX, prims: Vec::new() });
    best.insert(k0, 0);
    let needed0 = p.needed_mask(p.init_computed);
    heap.push((Reverse(p.heuristic(&init.stack, init.computed, needed0)), 0, 0));
    let mut expanded = 0usize;
    while let Some((Reverse(f), g, idx)) = heap.pop() {
        let st = decode(nodes[idx as usize].key);
        if best.get(&nodes[idx as usize].key).copied().unwrap_or(u32::MAX) < g {
            continue;
        }
        if p.is_goal(&st.stack) {
            let mut macros = Vec::new();
            let mut cur = idx;
            while nodes[cur as usize].parent != u32::MAX {
                macros.push((nodes[cur as usize].prims.clone(), nodes[cur as usize].parent));
                cur = nodes[cur as usize].parent;
            }
            macros.reverse();
            // replay for the stack after every prim
            let mut path = Vec::new();
            let mut s = p.init.clone();
            for (prims, _) in macros {
                for prim in prims {
                    apply_prim(p, &mut s, prim);
                    path.push((prim, s.clone()));
                }
            }
            eprintln!("expanded {expanded} nodes, {} states", best.len());
            return Some((g, path));
        }
        expanded += 1;
        if expanded % 100_000 == 0 {
            eprintln!("expanded {expanded}, states {}, g {g} f {f}", best.len());
        }
        let needed = p.needed_mask(st.computed);
        let dbg = std::env::var("DBG").is_ok();
        for (prims, s2, cost) in p.expand(&st, needed) {
            if dbg {
                let names: Vec<&str> = s2.stack.iter().map(|&c| p.classes[c as usize].name.as_str()).collect();
                eprintln!("  from g={g} {:?} -> g={} [{}] h={}", prims, g + cost, names.join(","), p.heuristic(&s2.stack, s2.computed, p.needed_mask(s2.computed)));
            }
            let g2 = g + cost;
            let k2 = key(&s2);
            if best.get(&k2).copied().unwrap_or(u32::MAX) <= g2 {
                continue;
            }
            best.insert(k2, g2);
            let needed2 = p.needed_mask(s2.computed);
            let h = p.heuristic(&s2.stack, s2.computed, needed2);
            nodes.push(Node { key: k2, g: g2, parent: idx, prims });
            heap.push((Reverse(g2 + h), g2, (nodes.len() - 1) as u32));
        }
    }
    None
}

fn apply_prim(p: &Problem, s: &mut Vec<u8>, prim: Prim) {
    match prim {
        Prim::Dup(k) => {
            let v = s[k as usize - 1];
            s.insert(0, v);
        }
        Prim::Swap(k) => s.swap(0, k as usize),
        Prim::PushP => s.insert(0, p.prime),
        Prim::Push4 => s.insert(0, p.four),
        Prim::Pop => {
            s.remove(0);
        }
        Prim::Add => {
            let (a, b) = (s[0], s[1]);
            let (ca, cb) = (&p.classes[a as usize], &p.classes[b as usize]);
            let mut coeffs = [0; 4];
            for i in 0..4 {
                coeffs[i] = ca.coeffs[i] + cb.coeffs[i];
            }
            let bound = ca.bound + cb.bound;
            let r = p.classes.iter().position(|c| c.kind == Kind::Val && c.coeffs == coeffs && c.bound == bound).unwrap();
            s.drain(0..2);
            s.insert(0, r as u8);
        }
        Prim::Addmod => {
            let (a, b) = (s[0], s[1]);
            let (ca, cb) = (&p.classes[a as usize], &p.classes[b as usize]);
            let mut coeffs = [0; 4];
            for i in 0..4 {
                coeffs[i] = ca.coeffs[i] + cb.coeffs[i];
            }
            let r = p.classes.iter().position(|c| c.kind == Kind::Val && c.coeffs == coeffs && c.bound == 1).unwrap();
            s.drain(0..3);
            s.insert(0, r as u8);
        }
        Prim::Mulmod => {
            let (a, b) = (s[0], s[1]);
            let v = if a == p.four { b } else { a };
            let cv = &p.classes[v as usize];
            let mut coeffs = [0; 4];
            for i in 0..4 {
                coeffs[i] = 4 * cv.coeffs[i];
            }
            let r = p.classes.iter().position(|c| c.kind == Kind::Val && c.coeffs == coeffs && c.bound == 1).unwrap();
            s.drain(0..3);
            s.insert(0, r as u8);
        }
        Prim::SboxP(i) => {
            s.drain(0..2);
            s.insert(0, p.sbox_out[i as usize]);
        }
        Prim::SboxNoP(i) => {
            s.remove(0);
            s.insert(0, p.sbox_out[i as usize]);
        }
    }
}

fn build(t: usize, final_round: bool, lazy: bool) -> (Vec<Class>, Vec<(Vec<String>, u32)>) {
    let b: u8 = if lazy { 2 } else { 1 };
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
        add(&format!("x{i}"), c, b, Kind::Val);
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
            let (b, c) = if final_round { (1, 8) } else { (3, 3) };
            add("o0", [2, 1, 0, 0], b, Kind::Val);
            add("o1", [1, 2, 0, 0], b, Kind::Val);
            g(&mut groups, &["sum", "2x0", "2x1"], 3);
            g(&mut groups, &["o0"], c);
            g(&mut groups, &["o1"], c);
        }
        3 => {
            let mut two: Vec<String> = Vec::new();
            let mut three: Vec<String> = Vec::new();
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
                        if s == 2 {
                            two.push(name.clone());
                        } else if s == 3 {
                            three.push(name.clone());
                        }
                        add(&name, [a, b, c, 0], bound, Kind::Val);
                    }
                }
            }
            let cost = if final_round { 8 } else { 3 };
            let two: Vec<&str> = two.iter().map(|s| s.as_str()).collect();
            let three: Vec<&str> = three.iter().map(|s| s.as_str()).collect();
            g(&mut groups, &two, 3);
            g(&mut groups, &three, 3);
            g(&mut groups, &["o0"], cost);
            g(&mut groups, &["o1"], cost);
            g(&mut groups, &["o2"], cost);
        }
        4 => {
            add("t0", [1, 1, 0, 0], 2 * b, Kind::Val);
            add("t1", [0, 0, 1, 1], 2 * b, Kind::Val);
            add("2x1", [0, 2, 0, 0], 2 * b, Kind::Val);
            add("2x3", [0, 0, 0, 2], 2 * b, Kind::Val);
            if !lazy {
                add("u1", [0, 1, 1, 1], 3, Kind::Val);
                add("u3", [1, 1, 0, 1], 3, Kind::Val);
            }
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
            if lazy {
                g(&mut groups, &["2x1"], 3);
                g(&mut groups, &["2x3"], 3);
            } else {
                g(&mut groups, &["2x1", "u1"], 3);
                g(&mut groups, &["2x3", "u3"], 3);
            }
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
    let final_round = args.get(7).map_or(false, |s| s == "final");
    let chain: usize = args.get(8).map_or(2, |s| s.parse().unwrap());
    let lazy = args.get(9).map_or(false, |s| s.contains("lazy"));
    let strict = args.get(9).map_or(false, |s| s.contains("strict"));
    let (classes, groups) = build(t, final_round, lazy);
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
        .map(|n| if *n == "_" { None } else if *n == "O" { Some(255) } else { Some(idx(n)) })
        .collect();
    let mut goal_set = 0u32;
    for g in goal.iter().flatten() {
        if *g == 255 {
            for (i, c) in classes.iter().enumerate() {
                if c.kind == Kind::Val && (c.name.starts_with('o') || ["t4", "t5", "t6", "t7"].contains(&c.name.as_str())) {
                    goal_set |= 1 << i;
                }
            }
        } else if classes[*g as usize].kind == Kind::Val {
            goal_set |= 1 << g;
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
        for (i, &x) in sbox_out.iter().enumerate() {
            if x as usize == d {
                productions[d].push(Production { operands: vec![sbox_in[i]], kind: PKind::Sbox });
                consumers[sbox_in[i] as usize].push(d as u8);
            }
        }
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
                    productions[d].push(Production { operands: vec![c as u8, e as u8], kind: PKind::Add });
                } else if dc.bound == 1 {
                    productions[d].push(Production { operands: vec![c as u8, e as u8], kind: PKind::Addmod });
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
            if dc.bound == 1 && cc.coeffs != [0; 4] && (0..4).all(|i| dc.coeffs[i] == 4 * cc.coeffs[i]) {
                productions[d].push(Production { operands: vec![c as u8], kind: PKind::Mulmod });
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
    let mut swaps = HashMap::new();
    for m in 1..=3 {
        swaps.extend(swap_table(m, reach, 3));
    }
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
        chain,
        strict,
        groups,
        consumers,
        productions,
        swaps,
    };
    match search(&p) {
        Some((cost, path)) => {
            println!("cost {cost}");
            if let Some((_, stack)) = path.last() {
                let names: Vec<&str> = stack.iter().map(|&c| p.classes[c as usize].name.as_str()).collect();
                println!("layout {}", names.join(","));
            }
            let mut g = 0;
            for (prim, stack) in path {
                g += match prim {
                    Prim::Pop => 2,
                    Prim::Add => 3,
                    Prim::Addmod | Prim::Mulmod => 8,
                    Prim::SboxP(_) => SBOX_P,
                    Prim::SboxNoP(_) => SBOX_NOP,
                    _ => 3,
                };
                let names: Vec<&str> = stack.iter().map(|&c| p.classes[c as usize].name.as_str()).collect();
                println!("{:<12} {:>4}  [{}]", format!("{prim:?}"), g, names.join(", "));
            }
        }
        None => println!("no solution"),
    }
}
