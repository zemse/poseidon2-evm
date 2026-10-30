// The schedule of a fixed DAG for the forms the t = 4 hash entry's round 0
// S-boxes (see hashpre.rs for the forms), over single opcodes, with the
// inputs loaded from calldata at will. A* from the PRIME copy SETUP leaves
// to a stack with p0 on top of a PRIME copy and p1, p2, p3 anywhere below
// (the round program from `s0,P,s1,s2,s3`, its DUP/SWAP indices rewritten,
// takes them there).
//
//   hashdag <n> <dag> [max_depth=12] [ub]
//
// The DAG is `;`-separated nodes `name=op(a,b)`: op add, addmod, mulmod
// (b may be the constant 4), mod (a raw input over a PRIME copy); operands
// are earlier nodes or raw inputs r0, r1, r2 (PUSH offset, CALLDATALOAD:
// 6 gas, any number of times). Nodes p0..p3 are the goal. Moves: DUP1..16
// of a value (3), a PRIME copy (3, DUP or PUSH32), PUSH1 4 (3), a raw
// load (6), SWAP1..16 (3), POP (2), the op of a node whose operands are
// on top (ADD 3, ADDMOD / MULMOD 8 with PRIME third, MOD 5 with PRIME
// second). A node is computed once; a value no consumer and no goal needs
// any more is garbage. The heuristic: the ops still to run, a DUP or load
// for every use beyond the copies on the stack, and a PRIME copy or a 4
// for every op (and the goal) that needs one beyond those on the stack.
// UB=<gas> as the fourth argument keeps only programs below it; WEIGHT=w
// orders the open list by g + w h / 10 (w > 10 finds a program sooner but
// not the cheapest).

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};

const G: u8 = 0;
const P: u8 = 1;
const K4: u8 = 2;
const R0: u8 = 3; // + input
const N0: u8 = 6; // + node

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Op {
    Add,
    Addmod,
    Mulmod,
    Mod,
}

struct Node {
    name: String,
    op: Op,
    args: Vec<u8>, // R0 + i, N0 + j or K4
}

struct Dag {
    n: usize,
    nodes: Vec<Node>,
    goal: [u8; 4],
    max_depth: usize,
}

impl Dag {
    fn op_cost(op: Op) -> u32 {
        match op {
            Op::Add => 3,
            Op::Addmod | Op::Mulmod => 8,
            Op::Mod => 5,
        }
    }
    /// the uses still to come of an item: the args of the nodes not yet
    /// computed, and a goal node's place in the goal
    fn uses(&self, item: u8, computed: u32) -> u32 {
        let mut u = 0;
        for (j, nd) in self.nodes.iter().enumerate() {
            if computed & (1 << j) == 0 {
                u += nd.args.iter().filter(|&&a| a == item).count() as u32;
            }
        }
        if self.goal.contains(&item) {
            u += 1;
        }
        u
    }
    fn canon(&self, s: &mut Vec<u8>, computed: u32) {
        for v in s.iter_mut() {
            if *v >= R0 && self.uses(*v, computed) == 0 {
                *v = G;
            }
        }
        while s.last() == Some(&G) {
            s.pop();
        }
    }
    fn h(&self, s: &[u8], computed: u32) -> u32 {
        let mut h = 0;
        let mut primes = 0i32;
        let mut fours = 0i32;
        for (j, nd) in self.nodes.iter().enumerate() {
            if computed & (1 << j) == 0 {
                h += Self::op_cost(nd.op);
                if nd.op != Op::Add {
                    primes += 1;
                }
                fours += nd.args.iter().filter(|&&a| a == K4).count() as i32;
            }
        }
        primes += 1; // the goal's
        let count = |c: u8| s.iter().filter(|&&x| x == c).count() as i32;
        h += 3 * (primes - count(P)).max(0) as u32;
        h += 3 * (fours - count(K4)).max(0) as u32;
        // every use beyond the copies on the stack (or the one the op
        // makes) takes a DUP or a load
        for item in R0..N0 + self.nodes.len() as u8 {
            if item < N0 && item >= R0 + self.n as u8 {
                continue;
            }
            let u = self.uses(item, computed) as i32;
            let have = if item >= N0 && computed & (1 << (item - N0)) == 0 {
                1
            } else {
                count(item)
            };
            h += 3 * (u - have).max(0) as u32;
            // a raw input not on the stack takes a load first
            if item < N0 && u > 0 && have == 0 {
                h += 3;
            }
        }
        h
    }
    fn is_goal(&self, s: &[u8]) -> bool {
        s.len() >= 2
            && s[0] == self.goal[0]
            && s[1] == P
            && self.goal[1..].iter().all(|g| s.contains(g))
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
        if d < self.max_depth {
            for k in 1..=d.min(16) {
                let v = s[k - 1];
                if v >= R0 {
                    out.push((3, format!("dup{k}"), top(v), computed));
                }
            }
            out.push((3, "P".into(), top(P), computed));
            out.push((3, "4".into(), top(K4), computed));
            for i in 0..self.n {
                if self.uses(R0 + i as u8, computed) > 0 {
                    out.push((6, format!("r{i}"), top(R0 + i as u8), computed));
                }
            }
        }
        for k in 1..d.min(17) {
            if s[k] != s[0] {
                let mut t = s.to_vec();
                t.swap(0, k);
                out.push((3, format!("swap{k}"), t, computed));
            }
        }
        if d >= 1 {
            out.push((2, "pop".into(), s[1..].to_vec(), computed));
        }
        for (j, nd) in self.nodes.iter().enumerate() {
            if computed & (1 << j) != 0 {
                continue;
            }
            let (k, ok) = match nd.op {
                Op::Mod => (2, d >= 2 && s[0] == nd.args[0] && s[1] == P),
                Op::Add => (
                    2,
                    d >= 2
                        && ((s[0] == nd.args[0] && s[1] == nd.args[1])
                            || (s[0] == nd.args[1] && s[1] == nd.args[0])),
                ),
                Op::Addmod | Op::Mulmod => (
                    3,
                    d >= 3
                        && s[2] == P
                        && ((s[0] == nd.args[0] && s[1] == nd.args[1])
                            || (s[0] == nd.args[1] && s[1] == nd.args[0])),
                ),
            };
            if ok {
                let mut t = vec![N0 + j as u8];
                t.extend_from_slice(&s[k..]);
                let name = format!("{}={}", format!("{:?}", nd.op).to_lowercase(), nd.name);
                out.push((Self::op_cost(nd.op), name, t, computed | (1 << j)));
            }
        }
    }
}

fn parse(n: usize, spec: &str) -> Vec<Node> {
    let mut nodes: Vec<Node> = Vec::new();
    for part in spec.split(';').filter(|p| !p.is_empty()) {
        let (name, rhs) = part.split_once('=').expect("name=op(a,b)");
        let (op, args) = rhs.trim_end_matches(')').split_once('(').expect("op(a,b)");
        let op = match op {
            "add" => Op::Add,
            "addmod" => Op::Addmod,
            "mulmod" => Op::Mulmod,
            "mod" => Op::Mod,
            _ => panic!("op {op}"),
        };
        let args = args
            .split(',')
            .map(|a| {
                if a == "4" {
                    K4
                } else if let Some(i) = a.strip_prefix('r') {
                    let i: usize = i.parse().unwrap();
                    assert!(i < n);
                    R0 + i as u8
                } else {
                    N0 + nodes
                        .iter()
                        .position(|x| x.name == a)
                        .unwrap_or_else(|| panic!("{a}")) as u8
                }
            })
            .collect();
        nodes.push(Node {
            name: name.to_string(),
            op,
            args,
        });
    }
    assert!(nodes.len() <= 24, "5 bits a slot");
    nodes
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args[1].parse().unwrap();
    let nodes = parse(n, &args[2]);
    let max_depth: usize = args.get(3).map_or(12, |s| s.parse().unwrap());
    let ub: u32 = args.get(4).map_or(u32::MAX, |s| s.parse().unwrap());
    let find = |name: &str| N0 + nodes.iter().position(|x| x.name == name).expect("p0..p3") as u8;
    // hash_1's p2 and p3 are one value: a DAG without p3 takes p2 for both
    let p3 = if nodes.iter().any(|x| x.name == "p3") {
        "p3"
    } else {
        "p2"
    };
    let goal = [find("p0"), find("p1"), find("p2"), find(p3)];
    let dag = Dag {
        n,
        nodes,
        goal,
        max_depth,
    };
    let pack = |s: &[u8], c: u32| -> u128 {
        let mut k: u128 = c as u128;
        for &v in s.iter().rev() {
            k = (k << 5) | (v as u128 + 1);
        }
        k | ((s.len() as u128) << 120)
    };
    let unpack = |k: u128, nodes: usize| -> (Vec<u8>, u32) {
        let len = (k >> 120) as usize;
        let mut s = Vec::with_capacity(len);
        let mut x = k & ((1u128 << 120) - 1);
        for _ in 0..len {
            s.push(((x & 31) as u8) - 1);
            x >>= 5;
        }
        (s, (x as u32) & ((1u32 << nodes) - 1))
    };
    // WEIGHT=w orders by g + w/10 h: faster, no longer optimal
    let weight: u32 = std::env::var("WEIGHT").map_or(10, |v| v.parse().unwrap());
    // KEEP=1 leaves the PRIME copy SETUP pushed where it is, under everything
    let init = if std::env::var("KEEP").is_ok() {
        Vec::new()
    } else {
        vec![P]
    };
    let start = pack(&init, 0);
    let mut dist: HashMap<u128, (u32, u128, u16)> = HashMap::new();
    dist.insert(start, (0, start, u16::MAX));
    let mut pq = BinaryHeap::new();
    pq.push(Reverse((dag.h(&init, 0), 0u32, start)));
    let mut names: Vec<String> = Vec::new();
    let mut name_ix: HashMap<String, u16> = HashMap::new();
    let mut buf = Vec::new();
    let mut expanded = 0u64;
    let nn = dag.nodes.len();
    while let Some(Reverse((f, g, key))) = pq.pop() {
        if g > dist[&key].0 {
            continue;
        }
        expanded += 1;
        if expanded % 1_000_000 == 0 {
            eprintln!("expanded {expanded}, states {}, f {f}", dist.len());
        }
        let (s, computed) = unpack(key, nn);
        if computed == (1 << nn) - 1 && dag.is_goal(&s) {
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
            let names: Vec<String> = s
                .iter()
                .map(|&v| match v {
                    G => "_".to_string(),
                    P => "P".to_string(),
                    K4 => "4".to_string(),
                    v if v < N0 => format!("r{}", v - R0),
                    v => dag.nodes[(v - N0) as usize].name.clone(),
                })
                .collect();
            println!("layout {}", names.join(","));
            eprintln!("expanded {expanded} nodes, {} states", dist.len());
            return;
        }
        dag.moves(&s, computed, &mut buf);
        for (c, m, mut t, tc) in buf.drain(..) {
            dag.canon(&mut t, tc);
            if t.len() > max_depth.max(2) {
                continue;
            }
            let ng = g + c;
            let hh = dag.h(&t, tc);
            if ng + hh >= ub {
                continue;
            }
            let nf = ng + hh * weight / 10;
            if false {
                continue;
            }
            let tk = pack(&t, tc);
            if dist.get(&tk).map_or(true, |e| ng < e.0) {
                let mi = *name_ix.entry(m.clone()).or_insert_with(|| {
                    names.push(m);
                    (names.len() - 1) as u16
                });
                dist.insert(tk, (ng, key, mi));
                pq.push(Reverse((nf, ng, tk)));
            }
        }
    }
    println!("no solution");
    eprintln!("expanded {expanded} nodes, {} states", dist.len());
}
