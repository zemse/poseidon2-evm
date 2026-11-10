// One block of a streamed external round (Osaka `externalStream`, t >= 16):
// u_i = x_i + S_i, the M4 of the block (the DAG of the `block` program of
// BLOCKS) and lane by lane s_i' + c_i and its S-box, stored to its memory
// slot or kept on the stack. A* from an empty working stack over a fixed
// floor (the column sums S0..S3, a PRIME copy, the block's inputs where
// they sit on the stack, dead slots) to an empty working stack, or to the
// kept S-box outputs in any order. Without lanes (`ordered_blocks`): `exit`
// ends with the M4 outputs [o0, o1, o2, o3] on top, `exit0` with [o0, P,
// o1, o2, o3] (block 0 before the internal rounds), `final` with the
// reduced outputs (ADDMOD for every o<i>).
//
//   sblock <floor> [stored|kept|exit|exit0|final] [max_working=8]
//          [ub | trace <program>]
//
// The floor is comma separated, top first: S0..S3, P, x0..x3 (an input on
// the stack; an input not in the floor is loaded from memory) and `_` for a
// slot nothing reads; it is only ever DUPed. Moves: DUP1..16 of a value an
// op still needs, no more copies than uses, or `P`, of the nearest PRIME
// copy, no more than the ops left need (3); SWAP1.. within the working
// stack (3); POP of a dead value or a spare copy (2); ADD (3) / ADDMOD (8,
// over a PRIME copy) of a node whose operands are on top; and three macros
// with a fixed program: `u<i>` = DUP x_i (PUSH2 MLOAD from memory) DUP S_i
// ADD (9 / 12), `q=<n>` = PUSH1 4 MULMOD of t on top over a PRIME copy
// (11), and `lane=<z>` = PUSH32 c_i ADD and the S-box (5 DUPs, 3 MULMODs)
// of s_i' on top over a PRIME copy (45), then PUSH2 MSTORE (6) when stored.
// The heuristic: the ops and macros still to run, a DUP for every use of a
// value beyond its copies on the working stack, a PRIME copy for every
// ADDMOD / q / lane beyond those on it, a POP for every dead value or spare
// copy. `ub` keeps only programs below it; `trace` replays a program and
// prints its gas instead. WEIGHT=w orders by g + w/10 h (w > 10 finds a
// program sooner, not the cheapest).
//
// REACH=n: the deepest slot a DUP reaches (16; 235 on Amsterdam).
// EXCHANGE=1: EIP-8024 exchanges of two non-top working slots (3 gas),
// with zero-based indices n < m and n + m <= 30. The floor stays fixed.
// GARBAGE=1: dead values and spare copies may stay (Amsterdam), so a DUP
// may make one copy beyond the uses left and no POP is needed. ROLL=1, with
// GARBAGE=1, bounds blocks interleaved with their neighbours: seen from one
// block a SWAP with another block's value moves one of its values to the
// top (`roll<d>`) or the top down (`bury<d>`), and the two blocks share its
// 3 gas, so each move costs 1.5 here (gas in halves; a spare DUP gives the
// same order of the live values as a roll and is left out). Its optimum is
// a lower bound per block for any interleaving within the window, with the
// macros kept whole.
// LIFT=1 adds 3 to h where a kept S-box output on top covers a working
// value still to be consumed (`buried`), LIFT=2 also where two lanes are
// still to run (`lanes_left`); both are admissible. ANY=1 accepts the exit
// / final outputs on top in any order, ANY=2 anywhere on the working stack
// with the first on top (with GARBAGE=1, dead values between them).
// DAG= also takes `d=shl(u)` (PUSH1 1 SHL, 6) and `z=store(o)` (MSIZE
// MSTORE, 5; the stores run in the order of the spec), with `stored` mode.
// The states sit in an arena of 24 bytes (key, g, parent, move) behind an
// open-addressing table of indices, the queue in one u64 an entry.

use std::collections::{BinaryHeap, HashMap};

const G: u8 = 0;
const P: u8 = 1;
const S0: u8 = 2; // + i
const X0: u8 = 6; // + i
const N0: u8 = 10; // + node
const LANE: u32 = 45;
/// the nodes computed are the low bits of `computed`; with TAKE=1 the
/// floor slot a take parked a value in (plus one, 0 for none) and that
/// value sit above them
const NODES: u32 = 23;
const MASK: u64 = (1 << NODES) - 1;
/// parked values at most (TAKE=n)
const PARKS: usize = 3;
const STORE: u32 = 6;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Op {
    U,
    Add,
    Addmod,
    Q,
    Lane,
    /// PUSH1 1 SHL of the top (a doubling with no copy)
    Shl,
    /// MSIZE MSTORE of the top (the last round's outputs in word order:
    /// the stores run in the order of the spec)
    Store,
}

struct Node {
    name: String,
    op: Op,
    args: Vec<u8>,
}

struct Dag {
    nodes: Vec<Node>,
    floor: Vec<u8>,
    kept: bool,
    /// exit / exit0 / final: the goal, top first (empty: any order)
    order: Vec<u8>,
    max_working: usize,
    lanes: Vec<u8>,
    /// GARBAGE=1: dead values may stay on the working stack (Amsterdam,
    /// where DUPN reaches past them), so a DUP may leave one spare copy and
    /// nothing is POPed
    garbage: bool,
    /// ROLL=1: the interleaving bound, gas doubled and a SWAP with another
    /// block's value as `roll<d>` / `bury<d>` at half a SWAP
    roll: bool,
    /// EXCHANGE=1: EIP-8024 exchanges within the working stack
    exchange: bool,
    /// the deepest slot a DUP reaches (REACH, 16)
    reach: usize,
    /// TAKE=1: `takex<i>` / `takeS<i>` SWAPs x_i / S_i up from the floor
    /// (its last read; S only with TAKE_S=1), parking the working top in
    /// its slot, and adds the other operand of u_i; SWAP and DUP then reach
    /// the parked value, which the goal accepts only dead or kept
    take: usize,
    take_s: bool,
    /// ORDER=<names>: the ops run in this order (only the stack moves and
    /// the way each u is made are searched)
    order_ops: Vec<usize>,
    /// LIFT=1: charge a buried working value under a kept output (`buried`);
    /// LIFT=2: or two lanes still to run (`lanes_left`)
    lift: u8,
    /// ANY=1: exit / final outputs on top in any order
    any_order: u8,
}

/// the floor slots values are parked in, by slot
fn parked(computed: u64) -> impl Iterator<Item = (usize, u8)> {
    (0..PARKS).filter_map(move |e| {
        let r = computed >> (NODES as usize + 9 * e);
        let slot = (r & 15) as usize;
        (slot > 0).then(|| (slot - 1, ((r >> 4) & 31) as u8))
    })
}

fn parked_at(computed: u64, slot: usize) -> Option<u8> {
    parked(computed).find(|p| p.0 == slot).map(|p| p.1)
}

fn park(computed: u64, slot: usize, v: u8) -> u64 {
    let mut ps: Vec<(usize, u8)> = parked(computed).filter(|p| p.0 != slot).collect();
    ps.push((slot, v));
    ps.sort();
    let mut c = computed & MASK;
    for (e, (slot, v)) in ps.into_iter().enumerate() {
        c |= ((slot as u64 + 1) | ((v as u64) << 4)) << (NODES as usize + 9 * e);
    }
    c
}

impl Dag {
    fn build(floor: Vec<u8>, mode: &str, max_working: usize) -> Dag {
        let m4 = "u0=u(x0,S0);u1=u(x1,S1);u2=u(x2,S2);u3=u(x3,S3);\
            t0=add(u0,u1);q0=q(t0);t1=add(u2,u3);d3=add(u3,u3);\
            t3=addmod(t0,d3);d1=add(u1,u1);q1=q(t1);o3=add(q1,t3);\
            t2=addmod(t1,d1);o2=add(o3,t2);o1=add(q0,t2);o0=add(t3,o1)";
        // DAG=<spec>: another M4 DAG in the same syntax, used as is (its
        // outputs o0..o3, its lanes z0..z3 when the mode keeps or stores)
        let spec = match std::env::var("DAG") {
            Ok(spec) => spec,
            Err(_) => match mode {
                "stored" | "kept" => {
                    format!("{m4};z0=lane(o0);z1=lane(o1);z2=lane(o2);z3=lane(o3)")
                }
                "exit" | "exit0" => m4.to_string(),
                // the last round's outputs, reduced
                "final" => m4
                    .replace("=add(q", "=addmod(q")
                    .replace("=add(o3", "=addmod(o3")
                    .replace("=add(t3,o1", "=addmod(t3,o1"),
                _ => panic!("{mode}"),
            },
        };
        let out = if matches!(mode, "stored" | "kept") {
            'z'
        } else {
            'o'
        };
        let mut nodes: Vec<Node> = Vec::new();
        for part in spec.split(';') {
            let (name, rhs) = part.split_once('=').unwrap();
            let (op, args) = rhs.trim_end_matches(')').split_once('(').unwrap();
            let op = match op {
                "u" => Op::U,
                "add" => Op::Add,
                "addmod" => Op::Addmod,
                "q" => Op::Q,
                "shl" => Op::Shl,
                "store" => Op::Store,
                "lane" => Op::Lane,
                _ => panic!("{op}"),
            };
            let args = args.split(',').map(|a| item(a, &nodes)).collect();
            nodes.push(Node {
                name: name.to_string(),
                op,
                args,
            });
        }
        let lanes = (0..4)
            .map(|i| {
                N0 + nodes
                    .iter()
                    .position(|n| n.name == format!("{out}{i}"))
                    .unwrap() as u8
            })
            .collect::<Vec<u8>>();
        // the outputs in order on top; exit0 (the block before the internal
        // rounds) with a PRIME copy under s0'
        let order = match mode {
            "exit" | "final" => lanes.clone(),
            "exit0" => vec![lanes[0], P, lanes[1], lanes[2], lanes[3]],
            _ => Vec::new(),
        };
        let mut dag = Dag {
            nodes,
            floor,
            kept: mode != "stored",
            order,
            max_working,
            lanes,
            garbage: std::env::var("GARBAGE").is_ok_and(|v| v == "1"),
            roll: std::env::var("ROLL").is_ok_and(|v| v == "1"),
            exchange: std::env::var("EXCHANGE").is_ok_and(|v| v == "1"),
            reach: std::env::var("REACH").map_or(16, |v| v.parse().unwrap()),
            take: std::env::var("TAKE").map_or(0, |v| v.parse::<usize>().unwrap().min(PARKS)),
            take_s: std::env::var("TAKE_S").is_ok_and(|v| v == "1"),
            order_ops: Vec::new(),
            lift: std::env::var("LIFT").map_or(0, |v| v.parse().unwrap()),
            any_order: std::env::var("ANY").map_or(0, |v| v.parse().unwrap()),
        };
        if let Ok(order) = std::env::var("ORDER") {
            dag.order_ops = order
                .split(',')
                .map(|n| dag.nodes.iter().position(|x| x.name == n).expect(n))
                .collect();
        }
        dag
    }

    /// with ORDER, whether op j is the next one
    fn next_op(&self, j: usize, computed: u64) -> bool {
        self.order_ops.is_empty()
            || self.order_ops.iter().find(|&&k| computed & (1 << k) == 0) == Some(&j)
    }

    /// gas units: 2 a gas with ROLL
    fn m(&self) -> u32 {
        if self.roll {
            2
        } else {
            1
        }
    }

    fn cost(&self, j: usize) -> u32 {
        self.m() * self.cost1(j)
    }

    fn cost1(&self, j: usize) -> u32 {
        let nd = &self.nodes[j];
        match nd.op {
            Op::U => {
                if self.floor.contains(&nd.args[0]) {
                    9
                } else {
                    12
                }
            }
            Op::Add => 3,
            Op::Addmod => 8,
            Op::Q => 11,
            Op::Shl => 6,
            Op::Store => 5,
            Op::Lane => LANE + if self.kept { 0 } else { STORE },
        }
    }

    /// the uses still to come of a value: the args of the nodes not yet
    /// computed, and a kept S-box output's place in the goal
    fn uses(&self, it: u8, computed: u64) -> u32 {
        let mut u = 0;
        for (j, nd) in self.nodes.iter().enumerate() {
            if computed & (1 << j) == 0 && nd.op != Op::U {
                u += nd.args.iter().filter(|&&a| a == it).count() as u32;
            }
        }
        if self.kept && self.lanes.contains(&it) {
            u += 1;
        }
        u
    }

    /// the PRIME copies the ops left consume
    fn primes(&self, computed: u64) -> u32 {
        self.order.iter().filter(|&&v| v == P).count() as u32
            + self
                .nodes
                .iter()
                .enumerate()
                .filter(|(j, nd)| {
                    computed & (1 << j) == 0 && matches!(nd.op, Op::Addmod | Op::Q | Op::Lane)
                })
                .count() as u32
    }

    fn need(&self, v: u8, computed: u64) -> u32 {
        match v {
            G => 0,
            P => self.primes(computed),
            v => self.uses(v, computed),
        }
    }

    fn canon(&self, s: &mut [u8], computed: &mut u64) {
        for v in s.iter_mut() {
            if *v >= N0 && self.uses(*v, *computed) == 0 {
                *v = G;
            }
        }
        let dead: Vec<usize> = parked(*computed)
            .filter(|&(_, v)| v >= N0 && self.uses(v, *computed) == 0)
            .map(|p| p.0)
            .collect();
        for slot in dead {
            *computed = park(*computed, slot, G);
        }
    }

    fn h(&self, s: &[u8], computed: u64) -> u32 {
        let mut h = 0;
        for j in 0..self.nodes.len() {
            if computed & (1 << j) == 0 {
                h += self.cost(j);
            }
        }
        let count = |c: u8| s.iter().filter(|&&x| x == c).count() as i32;
        let primes = self.primes(computed) as i32;
        let m = self.m();
        // POPs of spare copies and dead values, none with GARBAGE
        let pop = if self.garbage { 0 } else { 2 * m };
        h += 3 * m * (primes - count(P)).max(0) as u32;
        h += pop * (count(P) - primes).max(0) as u32;
        h += pop * count(G) as u32;
        for it in N0..N0 + self.nodes.len() as u8 {
            let u = self.uses(it, computed) as i32;
            let have = if computed & (1 << (it - N0)) == 0 {
                1
            } else {
                count(it) + parked(computed).filter(|p| p.1 == it).count() as i32
            };
            h += 3 * m * (u - have).max(0) as u32;
            h += pop * (have - u).max(0) as u32 * (computed >> (it - N0) & 1) as u32;
        }
        if (self.lift >= 1 && self.buried(s, computed))
            || (self.lift >= 2 && self.lanes_left(computed) >= 2)
        {
            // a roll lifts it for half a SWAP
            h += if self.roll { 3 } else { 3 * m };
        }
        h
    }

    /// The lanes not run yet. Every output reads every u, so all the u are
    /// made (no take is left) before the first lane runs, and when the last
    /// lane but one runs, the last output or a value it reads is live under
    /// the kept output that lands on top (or parked): it comes up by a SWAP
    /// or a copy beyond its uses, 3 gas that nothing else in h counts.
    /// kept S-box outputs (not the M4 outputs of exit / final)
    fn kept_lanes(&self) -> bool {
        self.kept && self.nodes[(self.lanes[0] - N0) as usize].op == Op::Lane
    }

    fn lanes_left(&self, computed: u64) -> u32 {
        if !self.kept_lanes() {
            return 0;
        }
        self.lanes
            .iter()
            .filter(|&&z| computed & (1 << (z - N0)) == 0)
            .count() as u32
    }

    /// LIFT=1: a kept S-box output on top (it has no use left and stays)
    /// over a working value whose every copy is still to be consumed (a
    /// PRIME copy with no spare, a dead value to POP): no op takes the
    /// output, so that value comes up by a SWAP with the top or by a copy
    /// beyond its uses (a DUP more, or a PRIME copy more), 3 gas either way
    fn buried(&self, s: &[u8], computed: u64) -> bool {
        if !self.kept_lanes() || s.len() < 2 || !self.lanes.contains(&s[0]) {
            return false;
        }
        // a take parks the top in the floor for the price of a u
        let takes_left = parked(computed).count() < self.take
            && self
                .nodes
                .iter()
                .enumerate()
                .any(|(j, nd)| nd.op == Op::U && computed & (1 << j) == 0);
        if takes_left {
            return false;
        }
        let count = |v: u8| {
            s.iter().filter(|&&x| x == v).count() as u32
                + parked(computed).filter(|p| p.1 == v).count() as u32
        };
        s[1..].iter().any(|&v| match v {
            G => !self.garbage,
            v if self.lanes.contains(&v) => false,
            v => {
                let need = self.need(v, computed);
                need > 0 && need >= count(v)
            }
        })
    }

    fn is_goal(&self, s: &[u8], computed: u64) -> bool {
        let pv_ok =
            |kept: bool| parked(computed).all(|(_, v)| v == G || (kept && self.lanes.contains(&v)));
        let done = computed & MASK == (1 << self.nodes.len()) - 1;
        if !self.order.is_empty() {
            // ANY=2: the outputs anywhere on the working stack (garbage
            // between them), the first output on top
            if self.any_order == 2 {
                let mut rest = s.to_vec();
                for &o in &self.order {
                    if o == P {
                        continue;
                    }
                    let Some(k) = rest.iter().position(|&v| v == o) else {
                        return false;
                    };
                    rest[k] = G;
                }
                return done
                    && s.first() == self.order.first()
                    && rest.iter().all(|&v| v == G || v == P)
                    && pv_ok(false);
            }
            // ANY=1: the outputs on top in any order (P where the order has it)
            if self.any_order == 1 {
                let mut a = s.to_vec();
                let mut b = self.order.clone();
                a.sort();
                b.sort();
                let fixed = self
                    .order
                    .iter()
                    .zip(s)
                    .all(|(&o, &v)| (o == P) == (v == P));
                return done && s.len() == self.order.len() && a == b && fixed && pv_ok(false);
            }
            return done && s == self.order && pv_ok(false);
        }
        done && pv_ok(self.kept)
            && s.iter().all(|&v| {
                (self.kept && self.lanes.contains(&v)) || (self.garbage && (v == G || v == P))
            })
    }

    fn name(&self, v: u8) -> String {
        match v {
            G => "_".into(),
            P => "P".into(),
            v if v < X0 => format!("S{}", v - S0),
            v if v < N0 => format!("x{}", v - X0),
            v => self.nodes[(v - N0) as usize].name.clone(),
        }
    }

    /// depth (1-based) of the nearest copy of v below the working stack s
    fn depth(&self, s: &[u8], v: u8, computed: u64) -> Option<usize> {
        if let Some(k) = s.iter().position(|&x| x == v) {
            return Some(k + 1);
        }
        (0..self.floor.len())
            .find(|&k| parked_at(computed, k).unwrap_or(self.floor[k]) == v)
            .map(|k| s.len() + k + 1)
    }

    fn moves(&self, s: &[u8], computed: u64, out: &mut Vec<(u32, String, Vec<u8>, u64)>) {
        out.clear();
        let d = s.len();
        let top = |v: u8| {
            let mut t = Vec::with_capacity(d + 1);
            t.push(v);
            t.extend_from_slice(s);
            t
        };
        let count = |v: u8| {
            s.iter().filter(|&&x| x == v).count() as u32
                + parked(computed).filter(|p| p.1 == v).count() as u32
        };
        let m = self.m();
        // copies allowed beyond the uses left: one spare with GARBAGE (a
        // roll gives the same order of the live values for less)
        let spare = (self.garbage && !self.roll) as u32;
        if d < self.max_working {
            let mut seen = [false; 64];
            for k in 1..=d {
                let v = s[k - 1];
                if v == G || v == P || seen[v as usize] {
                    continue;
                }
                seen[v as usize] = true;
                let need = self.need(v, computed);
                if need > 0 && need + spare > count(v) {
                    out.push((3 * m, format!("dup{k}"), top(v), computed));
                }
            }
            let primes = self.primes(computed);
            if primes > 0
                && primes + spare > count(P)
                && self.depth(s, P, computed).is_some_and(|k| k <= self.reach)
            {
                out.push((3 * m, "P".into(), top(P), computed));
            }
        }
        for k in 1..d {
            if s[k] != s[0] {
                let mut t = s.to_vec();
                t.swap(0, k);
                out.push((3 * m, format!("swap{k}"), t, computed));
            }
        }
        if self.exchange {
            for n in 1..d {
                for k in n + 1..d {
                    if exchange_valid(n, k, d) && s[n] != s[k] {
                        let mut t = s.to_vec();
                        t.swap(n, k);
                        out.push((3 * m, format!("exchange{n},{k}"), t, computed));
                    }
                }
            }
        }
        if self.roll {
            // what a SWAP with a value of another block does to this one's
            // stack: one of its values to the top, or the top down
            for k in 2..d {
                let mut t = s.to_vec();
                let v = t.remove(k);
                t.insert(0, v);
                out.push((3, format!("roll{k}"), t, computed));
                let mut t = s.to_vec();
                let v = t.remove(0);
                t.insert(k, v);
                out.push((3, format!("bury{k}"), t, computed));
            }
        }
        if !self.garbage && d >= 1 && self.need(s[0], computed) < count(s[0]) {
            out.push((2 * m, "pop".into(), s[1..].to_vec(), computed));
        }
        for (j, nd) in self.nodes.iter().enumerate() {
            if computed & (1 << j) != 0 || !self.next_op(j, computed) {
                continue;
            }
            let a = &nd.args;
            let pair = |x: u8, y: u8| (s[0] == x && s[1] == y) || (s[0] == y && s[1] == x);
            let (ok, k) = match nd.op {
                Op::U => {
                    // DUP (or load) x_i, then DUP S_i, both within reach
                    let reach = |v: u8, extra: usize| {
                        self.floor
                            .iter()
                            .position(|&x| x == v)
                            .map(|p| d + extra + p < self.reach)
                    };
                    let x_ok = reach(a[0], 0).unwrap_or(true);
                    let s_ok = reach(a[1], 1).unwrap_or(false);
                    (d + 2 <= self.max_working.max(2) && x_ok && s_ok, 0)
                }
                Op::Add => (d >= 2 && pair(a[0], a[1]), 2),
                Op::Addmod => (d >= 3 && s[2] == P && pair(a[0], a[1]), 3),
                Op::Q | Op::Lane => (d >= 2 && s[0] == a[0] && s[1] == P, 2),
                Op::Shl => (d >= 1 && s[0] == a[0], 1),
                Op::Store => (
                    d >= 1
                        && s[0] == a[0]
                        && self.nodes[..j]
                            .iter()
                            .enumerate()
                            .all(|(i, n)| n.op != Op::Store || computed & (1 << i) != 0),
                    1,
                ),
            };
            if !ok {
                continue;
            }
            let mut t = Vec::with_capacity(d + 1);
            if (nd.op != Op::Lane || self.kept) && nd.op != Op::Store {
                t.push(N0 + j as u8);
            }
            t.extend_from_slice(&s[k..]);
            let name = match nd.op {
                Op::U => nd.name.clone(),
                op => format!("{}={}", format!("{op:?}").to_lowercase(), nd.name),
            };
            out.push((self.cost(j), name, t, computed | (1 << j)));
        }
        if self.take == 0 || d == 0 {
            return;
        }
        let mut parks = 0;
        for (slot, pv) in parked(computed) {
            parks += 1;
            // the parked value: a DUP, or a SWAP that parks the top instead
            let n = d + slot;
            if pv != G && d < self.max_working && n < self.reach {
                let need = self.need(pv, computed);
                if need > 0 && need + spare > count(pv) {
                    out.push((3 * m, format!("dup{}", n + 1), top(pv), computed));
                }
            }
            if n <= self.reach && s[0] != pv {
                let mut t = s.to_vec();
                t[0] = pv;
                out.push((3 * m, format!("swap{n}"), t, park(computed, slot, s[0])));
            }
        }
        // PARK_LIVE=1: park only values with uses left
        if parks >= self.take
            || (std::env::var("PARK_LIVE").is_ok() && self.need(s[0], computed) == 0)
        {
            return;
        }
        for (j, nd) in self.nodes.iter().enumerate() {
            if nd.op != Op::U || computed & (1 << j) != 0 || !self.next_op(j, computed) {
                continue;
            }
            let i = nd.args[0] - X0;
            let mut ways = vec![(format!("takex{i}"), nd.args[0], nd.args[1])];
            if self.take_s {
                ways.push((format!("take{i}"), nd.args[1], nd.args[0]));
            }
            for (name, v, other) in ways {
                let Some(slot) = self.floor.iter().position(|&x| x == v) else {
                    continue;
                };
                // SWAP the top with the slot, DUP the other operand, ADD
                let Some(o) = self.depth(s, other, computed) else {
                    continue;
                };
                if parked_at(computed, slot).is_some() || d + slot > self.reach || o > self.reach {
                    continue;
                }
                let mut t = s.to_vec();
                t[0] = N0 + j as u8;
                out.push((9 * m, name, t, park(computed | (1 << j), slot, s[0])));
            }
        }
    }
}

fn exchange_valid(n: usize, m: usize, depth: usize) -> bool {
    n > 0 && n < m && m < depth && n + m <= 30
}

fn item(a: &str, nodes: &[Node]) -> u8 {
    match a {
        "P" => return P,
        "_" => return G,
        _ => {}
    }
    let (kind, i) = a.split_at(1);
    if let Ok(i) = i.parse::<u8>() {
        if i < 4 {
            match kind {
                "S" => return S0 + i,
                "x" => return X0 + i,
                _ => {}
            }
        }
    }
    N0 + nodes
        .iter()
        .position(|x| x.name == a)
        .unwrap_or_else(|| panic!("{a}")) as u8
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let floor: Vec<u8> = args[1].split(',').map(|a| item(a, &[])).collect();
    let mode = args.get(2).map_or("stored", |a| a.as_str());
    let max_working: usize = args.get(3).map_or(8, |s| s.parse().unwrap());
    assert!(max_working <= 16);
    let dag = Dag::build(floor, mode, max_working);
    let nn = dag.nodes.len();
    assert!(nn <= NODES as usize);
    let show = |s: &[u8]| s.iter().map(|&v| dag.name(v)).collect::<Vec<_>>().join(",");
    let gas = |g: u32| format!("{}", g as f64 / dag.m() as f64);
    if args.get(4).is_some_and(|a| a == "trace") {
        // replay: every move must be one the search could make
        let (mut s, mut c, mut g) = (Vec::new(), 0u64, 0u32);
        let mut buf = Vec::new();
        for m in args[5].split_whitespace() {
            dag.moves(&s, c, &mut buf);
            let Some((cost, _, t, tc)) = buf.iter().find(|x| x.1 == m).cloned() else {
                panic!("move {m} not available at [{}]", show(&s));
            };
            g += cost;
            s = t;
            c = tc;
            dag.canon(&mut s, &mut c);
            if std::env::var("VERBOSE").is_ok() {
                let parked: String = parked(c)
                    .map(|(k, v)| format!(" | slot {k}: {}", dag.name(v)))
                    .collect();
                println!("{g:4} {m:12} [{}]{parked}", show(&s));
            }
        }
        println!("gas {} goal {}", gas(g), dag.is_goal(&s, c));
        println!("layout {}", show(&s));
        println!("h0 {}", gas(dag.h(&[], 0)));
        return;
    }
    let ub: u32 = args
        .get(4)
        .map_or(u32::MAX, |s| s.parse::<u32>().unwrap() * dag.m());
    assert!(max_working <= 12);
    let pack = |s: &[u8], c: u64| -> u128 {
        let mut k: u128 = 0;
        for &v in s.iter().rev() {
            k = (k << 5) | v as u128;
        }
        k | ((s.len() as u128) << 60) | ((c as u128) << 64)
    };
    let unpack = |k: u128| -> (Vec<u8>, u64) {
        let len = ((k >> 60) & 15) as usize;
        let mut s = Vec::with_capacity(len);
        let mut x = k;
        for _ in 0..len {
            s.push((x & 31) as u8);
            x >>= 5;
        }
        (s, (k >> 64) as u64)
    };
    let weight: u32 = std::env::var("WEIGHT").map_or(10, |v| v.parse().unwrap());
    // the states in an arena (key, g, parent, move: 24 bytes), found through
    // an open-addressing table of arena indices; the queue holds f, g and
    // the index in one u64 (least f, then largest g, then the latest first)
    let mut keys: Vec<u128> = Vec::new();
    let mut gs: Vec<u16> = Vec::new();
    let mut parents: Vec<u32> = Vec::new();
    let mut mvs: Vec<u16> = Vec::new();
    let mut table: Vec<u32> = vec![u32::MAX; 1 << 20];
    let slot = |table: &[u32], keys: &[u128], k: u128| -> usize {
        let mask = table.len() - 1;
        let mut i = ((k as u64 ^ (k >> 64) as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15) >> 20)
            as usize
            & mask;
        while table[i] != u32::MAX && keys[table[i] as usize] != k {
            i = (i + 1) & mask;
        }
        i
    };
    let entry = |f: u32, g: u32, ix: u32| -> u64 {
        ((0xffff - f as u64) << 48) | ((g as u64) << 32) | ix as u64
    };
    let start = pack(&[], 0);
    keys.push(start);
    gs.push(0);
    parents.push(u32::MAX);
    mvs.push(u16::MAX);
    let i = slot(&table, &keys, start);
    table[i] = 0;
    let mut pq: BinaryHeap<u64> = BinaryHeap::new();
    pq.push(entry(dag.h(&[], 0), 0, 0));
    let mut names: Vec<String> = Vec::new();
    let mut name_ix: HashMap<String, u16> = HashMap::new();
    let mut buf = Vec::new();
    let mut expanded = 0u64;
    eprintln!("h0 {}", gas(dag.h(&[], 0)));
    while let Some(e) = pq.pop() {
        let (f, g, ix) = (
            0xffff - (e >> 48) as u32,
            (e >> 32) as u32 & 0xffff,
            e as u32,
        );
        if g > gs[ix as usize] as u32 {
            continue;
        }
        expanded += 1;
        if expanded.is_multiple_of(1_000_000) {
            eprintln!("expanded {expanded}, states {}, f {}", keys.len(), gas(f));
        }
        let key = keys[ix as usize];
        let (s, computed) = unpack(key);
        if dag.is_goal(&s, computed) {
            let mut prog = Vec::new();
            let mut k = ix;
            while k != 0 {
                prog.push(names[mvs[k as usize] as usize].clone());
                k = parents[k as usize];
            }
            prog.reverse();
            println!("gas {}", gas(g));
            println!("{}", prog.join(" "));
            println!("layout {}", show(&s));
            eprintln!("expanded {expanded} nodes, {} states", keys.len());
            return;
        }
        dag.moves(&s, computed, &mut buf);
        for (c, m, mut t, tc) in buf.drain(..) {
            let mut tc = tc;
            dag.canon(&mut t, &mut tc);
            let ng = g + c;
            let hh = dag.h(&t, tc);
            if ng + hh >= ub {
                continue;
            }
            let tk = pack(&t, tc);
            let i = slot(&table, &keys, tk);
            let old = table[i];
            if old != u32::MAX && gs[old as usize] as u32 <= ng {
                continue;
            }
            let mi = *name_ix.entry(m.clone()).or_insert_with(|| {
                names.push(m);
                (names.len() - 1) as u16
            });
            let nix = if old == u32::MAX {
                keys.push(tk);
                gs.push(ng as u16);
                parents.push(ix);
                mvs.push(mi);
                let nix = (keys.len() - 1) as u32;
                table[i] = nix;
                if keys.len() * 10 > table.len() * 7 {
                    let mut bigger = vec![u32::MAX; table.len() * 2];
                    for (j, &k) in keys.iter().enumerate() {
                        let s = slot(&bigger, &keys, k);
                        bigger[s] = j as u32;
                    }
                    table = bigger;
                }
                nix
            } else {
                gs[old as usize] = ng as u16;
                parents[old as usize] = ix;
                mvs[old as usize] = mi;
                old
            };
            pq.push(entry(ng + hh * weight / 10, ng, nix));
        }
    }
    println!("no solution");
    eprintln!("expanded {expanded} nodes, {} states", keys.len());
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dag(exchange: bool) -> Dag {
        let floor = "S0,S1,S2,S3,P,_,_,_,_,x0,x1,x2,x3"
            .split(',')
            .map(|a| item(a, &[]))
            .collect();
        let mut dag = Dag::build(floor, "kept", 9);
        dag.exchange = exchange;
        dag.garbage = false;
        dag.roll = false;
        dag.reach = 235;
        dag
    }

    fn replay(dag: &Dag, initial: &[u8], program: &str) -> (u32, Vec<u8>, u64) {
        let (mut gas, mut s, mut computed) = (0, initial.to_vec(), 0);
        let mut moves = Vec::new();
        for op in program.split_whitespace() {
            dag.moves(&s, computed, &mut moves);
            let (cost, _, next, done) = moves.iter().find(|m| m.1 == op).expect(op);
            gas += cost;
            s = next.clone();
            computed = *done;
            dag.canon(&mut s, &mut computed);
        }
        (gas, s, computed)
    }

    #[test]
    fn exchange_pair_limits() {
        assert!(exchange_valid(1, 2, 3));
        assert!(exchange_valid(1, 29, 30));
        assert!(exchange_valid(14, 16, 17));
        for (n, m, depth) in [(0, 2, 3), (2, 1, 3), (1, 1, 3), (1, 2, 2), (15, 16, 17)] {
            assert!(!exchange_valid(n, m, depth));
        }
    }

    #[test]
    fn exchange_moves_preserve_floor_and_existing_moves() {
        let mut enabled = dag(true);
        let mut disabled = dag(false);
        for depth in 0..=16 {
            enabled.max_working = depth;
            disabled.max_working = depth;
            let s: Vec<u8> = (N0..N0 + depth as u8).collect();
            let mut with = Vec::new();
            let mut without = Vec::new();
            enabled.moves(&s, 0, &mut with);
            disabled.moves(&s, 0, &mut without);
            let mut exchanges = 0;
            for (cost, name, next, computed) in &with {
                if let Some(pair) = name.strip_prefix("exchange") {
                    exchanges += 1;
                    let (n, m) = pair.split_once(',').unwrap();
                    let (n, m) = (n.parse().unwrap(), m.parse().unwrap());
                    assert!(exchange_valid(n, m, depth));
                    let mut expected = s.clone();
                    expected.swap(0, n);
                    expected.swap(0, m);
                    expected.swap(0, n);
                    assert_eq!(*next, expected);
                    assert_eq!(*cost, 3);
                    assert_eq!(*computed, 0);
                }
            }
            assert_eq!(
                exchanges,
                depth.saturating_sub(1) * depth.saturating_sub(2) / 2
            );
            with.retain(|m| !m.1.starts_with("exchange"));
            assert_eq!(with, without);
        }
        let mut moves = Vec::new();
        enabled.moves(&[P, P, P], 0, &mut moves);
        assert!(!moves.iter().any(|m| m.1.starts_with("exchange")));
    }

    #[test]
    fn exchange_replay_cost_and_incumbent() {
        let enabled = dag(true);
        let disabled = dag(false);
        let initial = [N0, P, N0 + 1];
        let (gas, stack, computed) = replay(&enabled, &initial, "exchange1,2");
        let (old_gas, old_stack, old_computed) = replay(&disabled, &initial, "swap1 swap2 swap1");
        assert_eq!((stack, computed), (old_stack, old_computed));
        assert_eq!((gas, old_gas), (3, 9));
        let incumbent = "u0 u3 u2 dup2 add=t1 P P u1 P dup2 dup1 add=d1 dup6 addmod=t2 swap6 add=t0 dup5 P dup3 q=q0 dup8 add=o1 swap6 add=d3 addmod=t3 P P P dup7 lane=z1 swap5 q=q1 dup3 add=o3 P dup2 lane=z3 swap7 add=o2 lane=z2 swap4 add=o0 lane=z0";
        let old = replay(&disabled, &[], incumbent);
        let new = replay(&enabled, &[], incumbent);
        assert_eq!(new, old);
        assert_eq!(new.0, 347);
        assert!(enabled.is_goal(&new.1, new.2));
        assert_eq!(enabled.h(&[], 0), 332);
    }
}
