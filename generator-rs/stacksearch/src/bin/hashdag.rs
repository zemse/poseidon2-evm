// The schedule of a fixed DAG over single opcodes: the forms the t = 4
// hash entry's round 0 S-boxes take, with the inputs loaded from calldata
// at will, alone or with the round's S-boxes and linear layer, or a seam
// of rounds from a given stack. A* from the PRIME copy SETUP leaves (or
// INIT) to a stack with p0 on top of a PRIME copy and p1, p2, p3 anywhere
// below (the round program from `s0,P,s1,s2,s3`, its DUP/SWAP indices
// rewritten, takes them there), or to the LAYOUT given.
//
//   hashdag <n> <dag> [max_depth=12] [ub]
//
// The DAG is `;`-separated nodes `name=op(a,b)`: op add, addmod, mulmod,
// mod (a raw input over a PRIME copy) and sbox (an S-box with its round
// constant over a PRIME copy, 45 gas); operands are earlier nodes, raw
// inputs r0, r1, r2 (PUSH offset, CALLDATALOAD: 6 gas, any number of
// times), constants (4, or #name for a PUSH32: 3 gas, any number of times)
// or the values INIT starts with. Nodes p0..p3 are the goal. Moves:
// DUP1..16 of a value (3), a PRIME copy (3, DUP or PUSH32), a constant
// (3), a raw load (6), SWAP1..16 (3), POP (2), the op of a node whose
// operands are on top (ADD 3, ADDMOD / MULMOD 8 with PRIME third, MOD 5
// with PRIME second). A node is computed once; a value no consumer and no
// goal needs any more is garbage. The heuristic: the ops still to run, a
// DUP, load or push for every use beyond the copies on the stack, and a
// PRIME copy for every op (and the goal) that needs one beyond those on
// the stack.
//
// UB=<gas> as the fourth argument keeps only programs below it; WEIGHT=w
// orders the open list by g + w h / 10 (w > 10 finds a program sooner but
// not the cheapest). KEEP=1 starts from an empty stack over SETUP's PRIME
// copy, which stays where it is; INIT="s0,P,s1,s2,s3" (top first, P a
// PRIME copy, other names values only the stack holds) from that stack.
// LAYOUT="a0,P,a1,a2,a3" (top first, _ anything) is the goal as an exact
// stack prefix instead of p0 over a PRIME copy.

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};

const G: u8 = 0;
const P: u8 = 1;
const L0: u8 = 2; // + leaf

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Op {
    Add,
    Addmod,
    Mulmod,
    Mul,
    Mod,
    Sbox,
}

struct Node {
    name: String,
    op: Op,
    args: Vec<u8>, // L0 + leaf or n0 + node
}

/// a value the DAG starts from: a raw input (load 6), a constant (push 3)
/// or a value INIT holds (no move makes it)
struct Leaf {
    name: String,
    load: Option<u32>,
}

struct Dag {
    leaves: Vec<Leaf>,
    n0: u8,
    nodes: Vec<Node>,
    goal: Vec<u8>,
    layout: Option<Vec<u8>>,
    goal_primes: i32,
    max_depth: usize,
    // ORDER: per node, the nodes that must be made before it
    before: Vec<u64>,
    live_dup: bool,
    // per item: the nodes taking it once, twice, and its place in the goal
    cons: Vec<(u64, u64, u32)>,
}

impl Dag {
    fn op_cost(op: Op) -> u32 {
        match op {
            Op::Add => 3,
            Op::Mul => 5,
            Op::Addmod | Op::Mulmod => 8,
            Op::Mod => 5,
            Op::Sbox => 45,
        }
    }
    /// the uses still to come of an item: the args of the nodes not yet
    /// computed, and a goal node's place in the goal
    fn uses(&self, item: u8, computed: u64) -> u32 {
        let (once, twice, goal) = self.cons[item as usize];
        (once & !computed).count_ones() + (twice & !computed).count_ones() + goal
    }
    fn canon(&self, s: &mut Vec<u8>, computed: u64) {
        for v in s.iter_mut() {
            if *v >= L0 && self.uses(*v, computed) == 0 {
                *v = G;
            }
        }
        while s.last() == Some(&G) {
            s.pop();
        }
    }
    /// a lower bound on the gas left, None when a value only the stack
    /// held is gone while still needed
    fn h(&self, s: &[u8], computed: u64) -> Option<u32> {
        let mut h = 0;
        let mut primes = self.goal_primes;
        for (j, nd) in self.nodes.iter().enumerate() {
            if computed & (1 << j) == 0 {
                h += Self::op_cost(nd.op);
                if !matches!(nd.op, Op::Add | Op::Mul) {
                    primes += 1;
                }
            }
        }
        let count = |c: u8| s.iter().filter(|&&x| x == c).count() as i32;
        h += 3 * (primes - count(P)).max(0) as u32;
        // every use beyond the copies on the stack (or the one the op
        // makes) takes a DUP, load or push
        for item in L0..self.n0 + self.nodes.len() as u8 {
            let u = self.uses(item, computed) as i32;
            if u == 0 {
                continue;
            }
            let have = if item >= self.n0 && computed & (1 << (item - self.n0)) == 0 {
                1
            } else {
                count(item)
            };
            h += 3 * (u - have).max(0) as u32;
            if item < self.n0 && have == 0 {
                match self.leaves[(item - L0) as usize].load {
                    // a raw input not on the stack takes a load first
                    Some(c) => h += c - 3,
                    None => return None,
                }
            }
        }
        // an op left whose operands are all on the stack already, none a
        // load or push and none with a DUP counted above: an op leaves its
        // result on top, so the move right before it is a DUP, SWAP or POP
        // (2 at least) that nothing else counts, one for each such op (an
        // op that can run now needs none)
        let mut now = false;
        for (j, nd) in self.nodes.iter().enumerate() {
            if computed & (1 << j) != 0 {
                continue;
            }
            let on_stack = nd.args.iter().all(|&v| {
                if v >= self.n0 {
                    computed & (1 << (v - self.n0)) != 0
                } else {
                    self.leaves[(v - L0) as usize].load.is_none()
                }
            });
            if !on_stack
                || nd.args.iter().any(|&v| {
                    let have = count(v);
                    have == 0 || self.uses(v, computed) as i32 > have
                })
            {
                continue;
            }
            if !now && self.ready(nd, s).is_some() {
                now = true;
                continue;
            }
            h += 2;
        }
        Some(h)
    }
    /// how many slots the op of a node takes from the top, if it can run
    fn ready(&self, nd: &Node, s: &[u8]) -> Option<usize> {
        let d = s.len();
        let ok = match nd.op {
            Op::Mod | Op::Sbox => d >= 2 && s[0] == nd.args[0] && s[1] == P,
            Op::Add | Op::Mul => {
                d >= 2
                    && ((s[0] == nd.args[0] && s[1] == nd.args[1])
                        || (s[0] == nd.args[1] && s[1] == nd.args[0]))
            }
            Op::Addmod | Op::Mulmod => {
                d >= 3
                    && s[2] == P
                    && ((s[0] == nd.args[0] && s[1] == nd.args[1])
                        || (s[0] == nd.args[1] && s[1] == nd.args[0]))
            }
        };
        let k = match nd.op {
            Op::Addmod | Op::Mulmod => 3,
            _ => 2,
        };
        ok.then_some(k)
    }
    fn is_goal(&self, s: &[u8]) -> bool {
        if let Some(l) = &self.layout {
            return s.len() >= l.len() && l.iter().zip(s).all(|(&g, &v)| g == G || g == v);
        }
        s.len() >= 2
            && s[0] == self.goal[0]
            && s[1] == P
            && self.goal[1..].iter().all(|g| s.contains(g))
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
        if d < self.max_depth {
            for k in 1..=d.min(16) {
                let v = s[k - 1];
                // LIVEDUP=1: copy only a value with more uses left than
                // copies (a restriction, not a bound)
                let spare = self.live_dup
                    && s.iter().filter(|&&x| x == v).count() as u32 >= self.uses(v, computed);
                if v >= L0 && !spare {
                    out.push((3, format!("dup{k}"), top(v), computed));
                }
            }
            out.push((3, "P".into(), top(P), computed));
            for (i, leaf) in self.leaves.iter().enumerate() {
                if let Some(c) = leaf.load {
                    if self.uses(L0 + i as u8, computed) > 0 {
                        out.push((c, leaf.name.clone(), top(L0 + i as u8), computed));
                    }
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
            if computed & self.before[j] != self.before[j] {
                continue;
            }
            if let Some(k) = self.ready(nd, s) {
                let mut t = vec![self.n0 + j as u8];
                t.extend_from_slice(&s[k..]);
                let name = format!("{}={}", format!("{:?}", nd.op).to_lowercase(), nd.name);
                out.push((Self::op_cost(nd.op), name, t, computed | (1 << j)));
            }
        }
    }
    fn name(&self, v: u8) -> String {
        match v {
            G => "_".to_string(),
            P => "P".to_string(),
            v if v < self.n0 => self.leaves[(v - L0) as usize].name.clone(),
            v => self.nodes[(v - self.n0) as usize].name.clone(),
        }
    }
}

/// the leaves (raw inputs, constants, then INIT's values) and nodes
fn parse(n: usize, spec: &str, init: &[&str]) -> (Vec<Leaf>, Vec<Node>) {
    let parts: Vec<(&str, &str, Vec<&str>)> = spec
        .split(';')
        .filter(|p| !p.is_empty())
        .map(|part| {
            let (name, rhs) = part.split_once('=').expect("name=op(a,b)");
            let (op, args) = rhs.trim_end_matches(')').split_once('(').expect("op(a,b)");
            (name, op, args.split(',').collect())
        })
        .collect();
    let mut leaves: Vec<Leaf> = (0..n)
        .map(|i| Leaf {
            name: format!("r{i}"),
            load: Some(6),
        })
        .collect();
    let is_node = |a: &str| parts.iter().any(|(name, _, _)| *name == a);
    for (_, _, args) in &parts {
        for &a in args {
            if !is_node(a)
                && !a.starts_with('r')
                && !init.contains(&a)
                && !leaves.iter().any(|l| l.name == a)
            {
                assert!(a == "4" || a.starts_with('#'), "unknown operand {a}");
                leaves.push(Leaf {
                    name: a.to_string(),
                    load: Some(3),
                });
            }
        }
    }
    for &a in init {
        if a != "P" && a != "_" && !leaves.iter().any(|l| l.name == a) {
            leaves.push(Leaf {
                name: a.to_string(),
                load: None,
            });
        }
    }
    let n0 = L0 + leaves.len() as u8;
    let mut nodes: Vec<Node> = Vec::new();
    for (name, op, args) in parts {
        let op = match op {
            "add" => Op::Add,
            "addmod" => Op::Addmod,
            "mulmod" => Op::Mulmod,
            "mul" => Op::Mul,
            "mod" => Op::Mod,
            "sbox" => Op::Sbox,
            _ => panic!("op {op}"),
        };
        let args = args
            .iter()
            .map(|&a| match nodes.iter().position(|x| x.name == a) {
                Some(j) => n0 + j as u8,
                None => {
                    if let Some(i) = a.strip_prefix('r').and_then(|i| i.parse::<usize>().ok()) {
                        assert!(i < n, "r{i}");
                    }
                    L0 + leaves
                        .iter()
                        .position(|l| l.name == a)
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
    assert!(nodes.len() <= 63, "a u64 of computed nodes");
    assert!(n0 as usize + nodes.len() <= 63, "6 bits a slot");
    (leaves, nodes)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args[1].parse().unwrap();
    let init_spec = std::env::var("INIT").ok();
    let init_names: Vec<&str> = init_spec
        .as_deref()
        .map_or(vec![], |s| s.split(',').collect());
    let (leaves, nodes) = parse(n, &args[2], &init_names);
    let n0 = L0 + leaves.len() as u8;
    let max_depth: usize = args.get(3).map_or(12, |s| s.parse().unwrap());
    let ub: u32 = args.get(4).map_or(u32::MAX, |s| s.parse().unwrap());
    let item = |leaves: &[Leaf], nodes: &[Node], name: &str| -> u8 {
        match name {
            "P" => P,
            "_" => G,
            _ => match nodes.iter().position(|y| y.name == name) {
                Some(j) => n0 + j as u8,
                None => {
                    L0 + leaves
                        .iter()
                        .position(|l| l.name == name)
                        .unwrap_or_else(|| panic!("{name}")) as u8
                }
            },
        }
    };
    let layout: Option<Vec<u8>> = std::env::var("LAYOUT")
        .ok()
        .map(|l| l.split(',').map(|a| item(&leaves, &nodes, a)).collect());
    let goal: Vec<u8> = match &layout {
        Some(l) => l.iter().copied().filter(|&v| v >= L0).collect(),
        None => {
            // hash_1's p2 and p3 are one value: a DAG without p3 takes p2
            // for both
            let p3 = if nodes.iter().any(|x| x.name == "p3") {
                "p3"
            } else {
                "p2"
            };
            ["p0", "p1", "p2", p3]
                .map(|a| item(&leaves, &nodes, a))
                .to_vec()
        }
    };
    let goal_primes = match &layout {
        Some(l) => l.iter().filter(|&&v| v == P).count() as i32,
        None => 1,
    };
    assert!(
        6 * max_depth.max(2) + nodes.len() <= 120,
        "the packed state"
    );
    let dag = Dag {
        leaves,
        n0,
        nodes,
        goal,
        layout,
        goal_primes,
        max_depth,
        cons: vec![],
        before: vec![],
        live_dup: std::env::var_os("LIVEDUP").is_some(),
    };
    let mut dag = dag;
    dag.cons = (0..dag.n0 + dag.nodes.len() as u8)
        .map(|item| {
            let mut c = (0, 0, u32::from(dag.goal.contains(&item)));
            for (j, nd) in dag.nodes.iter().enumerate() {
                let k = nd.args.iter().filter(|&&a| a == item).count();
                if k >= 1 {
                    c.0 |= 1 << j;
                }
                if k >= 2 {
                    c.1 |= 1 << j;
                }
            }
            c
        })
        .collect();
    // ORDER=a,b,...: these nodes are made in this order (the moves between
    // them are searched), the others whenever
    dag.before = vec![0; dag.nodes.len()];
    if let Ok(order) = std::env::var("ORDER") {
        let mut mask = 0u64;
        for name in order.split(',') {
            let j = dag
                .nodes
                .iter()
                .position(|x| x.name == name)
                .unwrap_or_else(|| panic!("ORDER {name}"));
            dag.before[j] = mask;
            mask |= 1 << j;
        }
    }
    let dag = dag;
    let pack = |s: &[u8], c: u64| -> u128 {
        let mut k: u128 = c as u128;
        for &v in s.iter().rev() {
            k = (k << 6) | (v as u128 + 1);
        }
        k | ((s.len() as u128) << 120)
    };
    let unpack = |k: u128, nodes: usize| -> (Vec<u8>, u64) {
        let len = (k >> 120) as usize;
        let mut s = Vec::with_capacity(len);
        let mut x = k & ((1u128 << 120) - 1);
        for _ in 0..len {
            s.push(((x & 63) as u8) - 1);
            x >>= 6;
        }
        (s, (x as u64) & ((1u64 << nodes) - 1))
    };
    // WEIGHT=w orders by g + w/10 h: faster, no longer optimal
    let weight: u32 = std::env::var("WEIGHT").map_or(10, |v| v.parse().unwrap());
    let init: Vec<u8> = if !init_names.is_empty() {
        init_names
            .iter()
            .map(|&a| item(&dag.leaves, &dag.nodes, a))
            .collect()
    } else if std::env::var("KEEP").is_ok() {
        Vec::new()
    } else {
        vec![P]
    };
    let mut init = init;
    dag.canon(&mut init, 0);
    // REPLAY="<moves>": score a program in the printed move names instead,
    // its stack and the heuristic after each move
    if let Ok(program) = std::env::var("REPLAY") {
        let (mut s, mut c, mut g) = (init.clone(), 0u64, 0u32);
        let mut buf = Vec::new();
        for mv in program.split_whitespace() {
            dag.moves(&s, c, &mut buf);
            let Some((cost, _, mut t, tc)) = buf.drain(..).find(|m| m.1 == mv) else {
                println!(
                    "no move {mv} from [{}]",
                    s.iter().map(|&v| dag.name(v)).collect::<Vec<_>>().join(",")
                );
                return;
            };
            dag.canon(&mut t, tc);
            g += cost;
            (s, c) = (t, tc);
            let names: Vec<String> = s.iter().map(|&v| dag.name(v)).collect();
            println!("{g:4} h {:?} {mv:12} [{}]", dag.h(&s, c), names.join(","));
        }
        let done = c == (1u64 << dag.nodes.len()) - 1 && dag.is_goal(&s);
        println!("gas {g}, goal {done}");
        return;
    }
    let start = pack(&init, 0);
    // a node a state reached at its cost: the key in two halves, the
    // parent node, g and the move; the map holds the node of a key's
    // best cost, the queue (f, g, node) packed in a u64
    struct Rec {
        lo: u64,
        hi: u64,
        parent: u32,
        g: u16,
        mv: u16,
    }
    let key2 = |k: u128| [k as u64, (k >> 64) as u64];
    let mut nodes: Vec<Rec> = vec![Rec {
        lo: start as u64,
        hi: (start >> 64) as u64,
        parent: u32::MAX,
        g: 0,
        mv: u16::MAX,
    }];
    let mut dist: HashMap<[u64; 2], u32, Fx> = HashMap::default();
    dist.insert(key2(start), 0);
    // equal f: the larger g first, so a goal on the plateau comes out sooner
    let entry =
        |f: u32, g: u32, i: u32| -> u64 { (f as u64) << 48 | (0xffff - g as u64) << 32 | i as u64 };
    let mut pq = BinaryHeap::new();
    let h0 = dag
        .h(&init, 0)
        .expect("INIT holds every value the DAG needs");
    pq.push(Reverse(entry(h0, 0, 0)));
    let mut names: Vec<String> = Vec::new();
    let mut name_ix: HashMap<String, u16> = HashMap::new();
    let mut buf = Vec::new();
    let mut expanded = 0u64;
    let nn = dag.nodes.len();
    while let Some(Reverse(e)) = pq.pop() {
        let (f, i) = ((e >> 48) as u32, e as u32);
        let nd = &nodes[i as usize];
        let key = nd.lo as u128 | (nd.hi as u128) << 64;
        let g = nd.g as u32;
        if dist[&key2(key)] != i {
            continue;
        }
        expanded += 1;
        if expanded % 1_000_000 == 0 {
            eprintln!("expanded {expanded}, states {}, f {f}", dist.len());
        }
        let (s, computed) = unpack(key, nn);
        if computed == (1 << nn) - 1 && dag.is_goal(&s) {
            let mut prog = Vec::new();
            let mut j = i;
            while nodes[j as usize].parent != u32::MAX {
                prog.push(names[nodes[j as usize].mv as usize].clone());
                j = nodes[j as usize].parent;
            }
            prog.reverse();
            println!("gas {g}");
            println!("{}", prog.join(" "));
            let names: Vec<String> = s.iter().map(|&v| dag.name(v)).collect();
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
            let Some(hh) = dag.h(&t, tc) else {
                continue;
            };
            if ng + hh >= ub {
                continue;
            }
            let nf = ng + hh * weight / 10;
            let tk = pack(&t, tc);
            let better = match dist.get(&key2(tk)) {
                Some(&j) => ng < nodes[j as usize].g as u32,
                None => true,
            };
            if better {
                let mi = *name_ix.entry(m.clone()).or_insert_with(|| {
                    names.push(m);
                    (names.len() - 1) as u16
                });
                let j = nodes.len() as u32;
                nodes.push(Rec {
                    lo: tk as u64,
                    hi: (tk >> 64) as u64,
                    parent: i,
                    g: ng as u16,
                    mv: mi,
                });
                dist.insert(key2(tk), j);
                pq.push(Reverse(entry(nf, ng, j)));
            }
        }
    }
    println!("no solution");
    eprintln!("expanded {expanded} nodes, {} states", dist.len());
}

/// FxHash (rustc's): one multiply a word
#[derive(Default, Clone, Copy)]
struct Fx(u64);

impl std::hash::Hasher for Fx {
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.write_u64(b as u64);
        }
    }
    fn write_u64(&mut self, x: u64) {
        self.0 = (self.0.rotate_left(5) ^ x).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
    }
    fn write_usize(&mut self, x: usize) {
        self.write_u64(x as u64);
    }
    fn finish(&self) -> u64 {
        self.0
    }
}

impl std::hash::BuildHasher for Fx {
    type Hasher = Fx;
    fn build_hasher(&self) -> Fx {
        Fx(0)
    }
}
