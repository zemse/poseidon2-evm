// One block of a streamed external round (Osaka `externalStream`, t >= 16):
// u_i = x_i + S_i, the M4 of the block (the DAG of the `block` program of
// BLOCKS) and lane by lane s_i' + c_i and its S-box, stored to its memory
// slot or kept on the stack. A* from an empty working stack over a fixed
// floor (the column sums S0..S3, a PRIME copy, the block's inputs where
// they sit on the stack, dead slots) to an empty working stack, or to the
// kept S-box outputs in any order.
//
//   sblock <floor> [stored|kept] [max_working=8] [ub | trace <program>]
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

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};

const G: u8 = 0;
const P: u8 = 1;
const S0: u8 = 2; // + i
const X0: u8 = 6; // + i
const N0: u8 = 10; // + node
const LANE: u32 = 45;
const STORE: u32 = 6;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Op {
    U,
    Add,
    Addmod,
    Q,
    Lane,
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
    max_working: usize,
    lanes: Vec<u8>,
}

impl Dag {
    fn build(floor: Vec<u8>, kept: bool, max_working: usize) -> Dag {
        let spec = "u0=u(x0,S0);u1=u(x1,S1);u2=u(x2,S2);u3=u(x3,S3);\
            t0=add(u0,u1);q0=q(t0);t1=add(u2,u3);d3=add(u3,u3);\
            t3=addmod(t0,d3);d1=add(u1,u1);q1=q(t1);o3=add(q1,t3);\
            t2=addmod(t1,d1);o2=add(o3,t2);o1=add(q0,t2);o0=add(t3,o1);\
            z0=lane(o0);z1=lane(o1);z2=lane(o2);z3=lane(o3)";
        let mut nodes: Vec<Node> = Vec::new();
        for part in spec.split(';') {
            let (name, rhs) = part.split_once('=').unwrap();
            let (op, args) = rhs.trim_end_matches(')').split_once('(').unwrap();
            let op = match op {
                "u" => Op::U,
                "add" => Op::Add,
                "addmod" => Op::Addmod,
                "q" => Op::Q,
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
                    .position(|n| n.name == format!("z{i}"))
                    .unwrap() as u8
            })
            .collect();
        Dag {
            nodes,
            floor,
            kept,
            max_working,
            lanes,
        }
    }

    fn cost(&self, j: usize) -> u32 {
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
            Op::Lane => LANE + if self.kept { 0 } else { STORE },
        }
    }

    /// the uses still to come of a value: the args of the nodes not yet
    /// computed, and a kept S-box output's place in the goal
    fn uses(&self, it: u8, computed: u32) -> u32 {
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
    fn primes(&self, computed: u32) -> u32 {
        self.nodes
            .iter()
            .enumerate()
            .filter(|(j, nd)| {
                computed & (1 << j) == 0 && matches!(nd.op, Op::Addmod | Op::Q | Op::Lane)
            })
            .count() as u32
    }

    fn need(&self, v: u8, computed: u32) -> u32 {
        match v {
            G => 0,
            P => self.primes(computed),
            v => self.uses(v, computed),
        }
    }

    fn canon(&self, s: &mut [u8], computed: u32) {
        for v in s.iter_mut() {
            if *v >= N0 && self.uses(*v, computed) == 0 {
                *v = G;
            }
        }
    }

    fn h(&self, s: &[u8], computed: u32) -> u32 {
        let mut h = 0;
        for j in 0..self.nodes.len() {
            if computed & (1 << j) == 0 {
                h += self.cost(j);
            }
        }
        let count = |c: u8| s.iter().filter(|&&x| x == c).count() as i32;
        let primes = self.primes(computed) as i32;
        h += 3 * (primes - count(P)).max(0) as u32;
        h += 2 * (count(P) - primes).max(0) as u32;
        h += 2 * count(G) as u32;
        for it in N0..N0 + self.nodes.len() as u8 {
            let u = self.uses(it, computed) as i32;
            let have = if computed & (1 << (it - N0)) == 0 {
                1
            } else {
                count(it)
            };
            h += 3 * (u - have).max(0) as u32;
            h += 2 * (have - u).max(0) as u32 * (computed >> (it - N0) & 1);
        }
        h
    }

    fn is_goal(&self, s: &[u8], computed: u32) -> bool {
        computed == (1 << self.nodes.len()) - 1
            && s.iter().all(|&v| self.kept && self.lanes.contains(&v))
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
    fn depth(&self, s: &[u8], v: u8) -> Option<usize> {
        if let Some(k) = s.iter().position(|&x| x == v) {
            return Some(k + 1);
        }
        self.floor
            .iter()
            .position(|&x| x == v)
            .map(|k| s.len() + k + 1)
    }

    fn moves(&self, s: &[u8], computed: u32, out: &mut Vec<(u32, String, Vec<u8>, u32)>) {
        out.clear();
        let d = s.len();
        let top = |v: u8| {
            let mut t = Vec::with_capacity(d + 1);
            t.push(v);
            t.extend_from_slice(s);
            t
        };
        let count = |v: u8| s.iter().filter(|&&x| x == v).count() as u32;
        if d < self.max_working {
            let mut seen = [false; 64];
            for k in 1..=d {
                let v = s[k - 1];
                if v == G || v == P || seen[v as usize] {
                    continue;
                }
                seen[v as usize] = true;
                if self.need(v, computed) > count(v) {
                    out.push((3, format!("dup{k}"), top(v), computed));
                }
            }
            if self.primes(computed) > count(P) && self.depth(s, P).is_some_and(|k| k <= 16) {
                out.push((3, "P".into(), top(P), computed));
            }
        }
        for k in 1..d {
            if s[k] != s[0] {
                let mut t = s.to_vec();
                t.swap(0, k);
                out.push((3, format!("swap{k}"), t, computed));
            }
        }
        if d >= 1 && self.need(s[0], computed) < count(s[0]) {
            out.push((2, "pop".into(), s[1..].to_vec(), computed));
        }
        for (j, nd) in self.nodes.iter().enumerate() {
            if computed & (1 << j) != 0 {
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
                            .map(|p| d + extra + p < 16)
                    };
                    let x_ok = reach(a[0], 0).unwrap_or(true);
                    let s_ok = reach(a[1], 1).unwrap_or(false);
                    (d + 2 <= self.max_working.max(2) && x_ok && s_ok, 0)
                }
                Op::Add => (d >= 2 && pair(a[0], a[1]), 2),
                Op::Addmod => (d >= 3 && s[2] == P && pair(a[0], a[1]), 3),
                Op::Q | Op::Lane => (d >= 2 && s[0] == a[0] && s[1] == P, 2),
            };
            if !ok {
                continue;
            }
            let mut t = Vec::with_capacity(d + 1);
            if nd.op != Op::Lane || self.kept {
                t.push(N0 + j as u8);
            }
            t.extend_from_slice(&s[k..]);
            let name = match nd.op {
                Op::U => nd.name.clone(),
                op => format!("{}={}", format!("{op:?}").to_lowercase(), nd.name),
            };
            out.push((self.cost(j), name, t, computed | (1 << j)));
        }
    }
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
    let kept = args.get(2).is_some_and(|a| a == "kept");
    let max_working: usize = args.get(3).map_or(8, |s| s.parse().unwrap());
    assert!(max_working <= 16);
    let dag = Dag::build(floor, kept, max_working);
    let nn = dag.nodes.len();
    assert!(nn <= 24);
    let show = |s: &[u8]| s.iter().map(|&v| dag.name(v)).collect::<Vec<_>>().join(",");
    if args.get(4).is_some_and(|a| a == "trace") {
        // replay: every move must be one the search could make
        let (mut s, mut c, mut g) = (Vec::new(), 0u32, 0u32);
        let mut buf = Vec::new();
        for m in args[5].split_whitespace() {
            dag.moves(&s, c, &mut buf);
            let Some((cost, _, t, tc)) = buf.iter().find(|x| x.1 == m).cloned() else {
                panic!("move {m} not available at [{}]", show(&s));
            };
            g += cost;
            s = t;
            c = tc;
            dag.canon(&mut s, c);
        }
        println!("gas {g} goal {}", dag.is_goal(&s, c));
        println!("layout {}", show(&s));
        println!("h0 {}", dag.h(&[], 0));
        return;
    }
    let ub: u32 = args.get(4).map_or(u32::MAX, |s| s.parse().unwrap());
    let pack = |s: &[u8], c: u32| -> u128 {
        let mut k: u128 = 0;
        for &v in s.iter().rev() {
            k = (k << 5) | v as u128;
        }
        k | ((c as u128) << 80) | ((s.len() as u128) << 120)
    };
    let unpack = |k: u128| -> (Vec<u8>, u32) {
        let len = (k >> 120) as usize;
        let mut s = Vec::with_capacity(len);
        let mut x = k;
        for _ in 0..len {
            s.push((x & 31) as u8);
            x >>= 5;
        }
        (s, ((k >> 80) as u32) & ((1u32 << 24) - 1))
    };
    let weight: u32 = std::env::var("WEIGHT").map_or(10, |v| v.parse().unwrap());
    let start = pack(&[], 0);
    let mut dist: HashMap<u128, (u32, u128, u16)> = HashMap::new();
    dist.insert(start, (0, start, u16::MAX));
    // equal f: larger g first
    let mut pq = BinaryHeap::new();
    pq.push((Reverse(dag.h(&[], 0)), 0u32, start));
    let mut names: Vec<String> = Vec::new();
    let mut name_ix: HashMap<String, u16> = HashMap::new();
    let mut buf = Vec::new();
    let mut expanded = 0u64;
    eprintln!("h0 {}", dag.h(&[], 0));
    while let Some((Reverse(f), g, key)) = pq.pop() {
        if g > dist[&key].0 {
            continue;
        }
        expanded += 1;
        if expanded.is_multiple_of(1_000_000) {
            eprintln!("expanded {expanded}, states {}, f {f}", dist.len());
        }
        let (s, computed) = unpack(key);
        if dag.is_goal(&s, computed) {
            let mut prog = Vec::new();
            let mut k = key;
            while k != start {
                let (_, parent, m) = dist[&k];
                prog.push(names[m as usize].clone());
                k = parent;
            }
            prog.reverse();
            println!("gas {g}");
            println!("{}", prog.join(" "));
            println!("layout {}", show(&s));
            eprintln!("expanded {expanded} nodes, {} states", dist.len());
            return;
        }
        dag.moves(&s, computed, &mut buf);
        for (c, m, mut t, tc) in buf.drain(..) {
            dag.canon(&mut t, tc);
            let ng = g + c;
            let hh = dag.h(&t, tc);
            if ng + hh >= ub {
                continue;
            }
            let tk = pack(&t, tc);
            if dist.get(&tk).is_none_or(|e| ng < e.0) {
                let mi = *name_ix.entry(m.clone()).or_insert_with(|| {
                    names.push(m);
                    (names.len() - 1) as u16
                });
                dist.insert(tk, (ng, key, mi));
                pq.push((Reverse(ng + hh * weight / 10), ng, tk));
            }
        }
    }
    println!("no solution");
    eprintln!("expanded {expanded} nodes, {} states", dist.len());
}
