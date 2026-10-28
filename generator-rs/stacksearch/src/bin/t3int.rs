// A* over single opcodes for the t = 3 internal round after its S-box:
// from [x, s2, s1] (top first) to [s0', P, s2', s1'] + at most G garbage.
// Values are linear forms (cx, c1, c2) over x, s1, s2 with a bound in units
// of P (ADD only while the bound stays <= 5). Costs: DUP/SWAP/PUSHP 3,
// POP 2, ADD 3, ADDMOD 8, MUL2 (PUSH1 2 MULMOD on [v, P]) 11.
//
//   t3int B1in B2in B1out B2out G MAXLEN [B0=4] [UB]
// EXCHANGE=1 adds non-top exchanges within MAXLEN. REPLAY="..." replays
// the printed DSL and checks the goal and every suffix's heuristic bound.
// The positive-form whitelist, live-only DUP filter and window restrict
// the search; a bounded result is not an unrestricted EVM optimum.
use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};

const MAXD: usize = 16;
type Form = [u8; 3];
const TARGETS: [Form; 3] = [[2, 1, 1], [1, 2, 1], [1, 1, 3]];

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct St {
    len: u8,
    s: [u8; MAXD], // bottom first; 0 = P, else 1 + form_index * 6 + bound
}

struct Pb {
    tb: [u8; 3],
    g: usize,
    maxlen: usize,
    exchange: bool,
    forms: Vec<Form>,
    idx: HashMap<Form, usize>,
}

struct Replay {
    state: St,
    cost: u32,
    trace: Vec<(St, u32)>,
}

fn exchange_code(j: usize, k: usize) -> Option<u8> {
    if j == 0 || j >= k || k >= MAXD || j + k > 30 {
        return None;
    }
    u8::try_from(45 + (k - 1) * (k - 2) / 2 + j - 1).ok()
}

fn exchange_pair(code: u8) -> Option<(usize, usize)> {
    let code = usize::from(code.checked_sub(45)?);
    let k = (2..MAXD).find(|&k| code < k * (k - 1) / 2)?;
    Some((code - (k - 1) * (k - 2) / 2 + 1, k))
}

fn le(a: Form, b: Form) -> bool {
    a.iter().zip(b.iter()).all(|(x, y)| x <= y)
}

impl Pb {
    fn replay(&self, initial: St, program: &str) -> Result<Replay, String> {
        let (mut state, mut cost) = (initial, 0u32);
        let mut trace = vec![(state, cost)];
        let mut moves = Vec::new();
        for op in program.split_whitespace() {
            self.moves(&state, &mut moves);
            let (gas, _, next) = moves
                .iter()
                .find(|(_, mv, _)| mvname(*mv) == op)
                .ok_or_else(|| format!("replay move {op} is not available"))?;
            cost += gas;
            state = *next;
            trace.push((state, cost));
        }
        Ok(Replay { state, cost, trace })
    }

    fn check_replay(&self, replay: &Replay) -> Result<(), String> {
        if !self.goal(&replay.state) {
            return Err("replay did not reach the goal".to_string());
        }
        for &(state, spent) in &replay.trace {
            if !self.h(&state).is_some_and(|h| h <= replay.cost - spent) {
                return Err(format!("heuristic exceeds replay suffix at gas {spent}"));
            }
        }
        Ok(())
    }

    fn enc(&self, f: Form, k: u8) -> u8 {
        (1 + self.idx[&f] * 6 + k as usize) as u8
    }
    fn dec(&self, v: u8) -> (Form, u8) {
        let i = (v - 1) as usize;
        (self.forms[i / 6], (i % 6) as u8)
    }
    fn tgt(&self, f: Form, k: u8) -> Option<usize> {
        TARGETS
            .iter()
            .position(|&t| t == f)
            .filter(|&i| k <= self.tb[i])
    }
    fn missing(&self, st: &St) -> [bool; 3] {
        let mut m = [true; 3];
        for &v in &st.s[..st.len as usize] {
            if v != 0 {
                let (f, k) = self.dec(v);
                if let Some(i) = self.tgt(f, k) {
                    m[i] = false;
                }
            }
        }
        m
    }
    fn useful(&self, f: Form, m: &[bool; 3]) -> bool {
        (0..3).any(|i| m[i] && le(f, TARGETS[i]))
    }
    fn live(&self, f: Form, k: u8, m: &[bool; 3]) -> bool {
        // an operand for a missing target (not an output itself)
        (0..3).any(|i| m[i] && le(f, TARGETS[i]) && !(f == TARGETS[i] && k <= self.tb[i]))
    }
    fn h(&self, st: &St) -> Option<u32> {
        let m = self.missing(st);
        let mut cost = 0u32;
        let mut pneed = 1i32;
        for (i, &missing) in m.iter().enumerate() {
            if missing {
                if self.tb[i] < 2 {
                    cost += 8;
                    pneed += 1;
                } else {
                    cost += 3;
                }
            }
        }
        let pc = st.s[..st.len as usize].iter().filter(|&&v| v == 0).count() as i32;
        let mut moves = (pneed - pc).max(0) as u32;
        // copies: only a DUP adds an entry carrying a leaf, and every
        // missing target is an entry carrying each of its leaves
        let mut dups = 0i32;
        for l in 0..3 {
            let need = (0..3).filter(|&i| m[i] && TARGETS[i][l] > 0).count() as i32;
            let have = st.s[..st.len as usize]
                .iter()
                .filter(|&&v| {
                    v != 0 && {
                        let (f, k) = self.dec(v);
                        f[l] > 0 && self.live(f, k, &m)
                    }
                })
                .count() as i32;
            if need > 0 && have == 0 {
                return None;
            }
            dups = dups.max(need - have);
        }
        moves += dups.max(0) as u32;
        // Spare PRIME copies can feed intermediate reductions; omit cleanup.
        Some(cost + 3 * moves)
    }
    fn goal(&self, st: &St) -> bool {
        let n = st.len as usize;
        if n < 4 || n - 4 > self.g {
            return false;
        }
        let t = |k: usize| st.s[n - 1 - k];
        let is = |v: u8, i: usize| {
            v != 0 && {
                let (f, k) = self.dec(v);
                f == TARGETS[i] && k <= self.tb[i]
            }
        };
        is(t(0), 0) && t(1) == 0 && is(t(2), 2) && is(t(3), 1)
    }
    fn moves(&self, st: &St, out: &mut Vec<(u32, u8, St)>) {
        out.clear();
        let n = st.len as usize;
        let m = self.missing(st);
        let top = |k: usize| st.s[n - 1 - k];
        if n < self.maxlen {
            for k in 0..n.min(16) {
                let v = top(k);
                if v == 0 {
                    continue;
                }
                let (f, kk) = self.dec(v);
                if !self.live(f, kk, &m) {
                    continue;
                }
                let mut ns = *st;
                ns.s[n] = v;
                ns.len += 1;
                out.push((3, (k + 1) as u8, ns));
            }
            let mut ns = *st;
            ns.s[n] = 0;
            ns.len += 1;
            out.push((3, 40, ns));
        }
        for k in 1..n.min(17) {
            if top(0) == top(k) {
                continue;
            }
            let mut ns = *st;
            ns.s.swap(n - 1, n - 1 - k);
            out.push((3, (16 + k) as u8, ns));
        }
        if self.exchange {
            for k in 2..n {
                for j in 1..k {
                    if top(j) == top(k) {
                        continue;
                    }
                    let mut ns = *st;
                    ns.s.swap(n - 1 - j, n - 1 - k);
                    let code = exchange_code(j, k).expect("working-window exchange");
                    out.push((3, code, ns));
                }
            }
        }
        if n >= 1 {
            let mut ns = *st;
            ns.len -= 1;
            ns.s[n - 1] = 0;
            out.push((2, 41, ns));
        }
        if n >= 2 && top(0) != 0 && top(1) != 0 {
            let (a, ka) = self.dec(top(0));
            let (b, kb) = self.dec(top(1));
            let f = [a[0] + b[0], a[1] + b[1], a[2] + b[2]];
            if ka + kb <= 5 && self.idx.contains_key(&f) && self.useful(f, &m) {
                let mut ns = *st;
                ns.len -= 1;
                ns.s[n - 1] = 0;
                ns.s[n - 2] = self.enc(f, ka + kb);
                out.push((3, 42, ns));
            }
        }
        if n >= 3 && top(0) != 0 && top(1) != 0 && top(2) == 0 {
            let (a, _) = self.dec(top(0));
            let (b, _) = self.dec(top(1));
            let f = [a[0] + b[0], a[1] + b[1], a[2] + b[2]];
            if self.idx.contains_key(&f) && self.useful(f, &m) {
                let mut ns = *st;
                ns.len -= 2;
                ns.s[n - 1] = 0;
                ns.s[n - 2] = 0;
                ns.s[n - 3] = self.enc(f, 1);
                out.push((8, 43, ns));
            }
        }
        if n >= 2 && top(0) != 0 && top(1) == 0 {
            let (a, _) = self.dec(top(0));
            let f = [2 * a[0], 2 * a[1], 2 * a[2]];
            if self.idx.contains_key(&f) && self.useful(f, &m) {
                let mut ns = *st;
                ns.len -= 1;
                ns.s[n - 1] = 0;
                ns.s[n - 2] = self.enc(f, 1);
                out.push((11, 44, ns));
            }
        }
    }
    fn name(&self, v: u8) -> String {
        if v == 0 {
            return "P".into();
        }
        let (f, k) = self.dec(v);
        let n = match f {
            [1, 0, 0] => "x".to_string(),
            [0, 1, 0] => "s1".to_string(),
            [0, 0, 1] => "s2".to_string(),
            [2, 1, 1] => "s0'".to_string(),
            [1, 2, 1] => "s1'".to_string(),
            [1, 1, 3] => "s2'".to_string(),
            [1, 1, 1] => "sum".to_string(),
            _ => {
                let mut p = vec![];
                for (c, nm) in f.iter().zip(["x", "s1", "s2"]) {
                    if *c == 1 {
                        p.push(nm.to_string());
                    } else if *c > 1 {
                        p.push(format!("{c}{nm}"));
                    }
                }
                p.join("+")
            }
        };
        format!("{n}<{k}")
    }
}

fn mvname(m: u8) -> String {
    match m {
        1..=16 => format!("dup{m}"),
        17..=39 => format!("swap{}", m - 16),
        40 => "P".into(),
        41 => "pop".into(),
        42 => "add".into(),
        43 => "addmod".into(),
        44 => "mul2".into(),
        _ => {
            let (j, k) = exchange_pair(m).expect("exchange move");
            format!("exchange{j},{k}")
        }
    }
}

fn problem(a: &[String], exchange: bool) -> Result<(Pb, St, u32), String> {
    if a.len() > 8 {
        return Err("too many arguments".to_string());
    }
    let arg = |i: usize, d: u32| {
        a.get(i).map_or(Ok(d), |s| {
            s.parse::<u32>()
                .map_err(|_| format!("invalid argument {}: {s}", i + 1))
        })
    };
    let b1 = arg(0, 1)?;
    let b2 = arg(1, 1)?;
    let o1 = arg(2, 1)?;
    let o2 = arg(3, 1)?;
    let g = arg(4, 2)? as usize;
    let maxlen = arg(5, 10)? as usize;
    let b0 = arg(6, 4)?;
    let ub = arg(7, 1 << 30)?;
    if !(4..=MAXD).contains(&maxlen) {
        return Err("MAXLEN must be in 4..16".to_string());
    }
    if ![b0, b1, b2, o1, o2].iter().all(|b| (1..=5).contains(b)) {
        return Err("bounds must be in 1..5".to_string());
    }
    let mut forms = vec![];
    for x in 0..=2u8 {
        for y in 0..=2u8 {
            for z in 0..=3u8 {
                let f = [x, y, z];
                if f != [0, 0, 0] && TARGETS.iter().any(|&t| le(f, t)) {
                    forms.push(f);
                }
            }
        }
    }
    let idx = forms.iter().enumerate().map(|(i, &f)| (f, i)).collect();
    let pb = Pb {
        tb: [b0 as u8, o1 as u8, o2 as u8],
        g,
        maxlen,
        exchange,
        forms,
        idx,
    };
    let mut init = St {
        len: 0,
        s: [0; MAXD],
    };
    for (f, k) in [([0, 1, 0], b1 as u8), ([0, 0, 1], b2 as u8), ([1, 0, 0], 1)] {
        init.s[init.len as usize] = pb.enc(f, k);
        init.len += 1;
    }
    Ok((pb, init, ub))
}

fn main() -> Result<(), String> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let exchange = std::env::var("EXCHANGE").is_ok_and(|v| v == "1");
    let (pb, init, ub) = problem(&args, exchange)?;
    if let Ok(program) = std::env::var("REPLAY") {
        let replay = pb.replay(init, &program)?;
        pb.check_replay(&replay)?;
        println!("replay cost {}, goal true", replay.cost);
        return Ok(());
    }
    let mut best: HashMap<St, (u32, Option<(St, u8)>)> = HashMap::new();
    best.insert(init, (0, None));
    let mut pq = BinaryHeap::new();
    pq.push(Reverse((pb.h(&init).unwrap(), Reverse(0u32), 0u64, init)));
    let mut cnt = 0u64;
    let mut exp = 0u64;
    let mut buf = vec![];
    let mut lastf = 0;
    while let Some(Reverse((f, Reverse(g), _, st))) = pq.pop() {
        if best[&st].0 < g {
            continue;
        }
        if f >= ub {
            println!("no program below {ub}, expanded {exp}");
            return Ok(());
        }
        if f > lastf {
            lastf = f;
            eprintln!("f {f} expanded {exp} states {}", best.len());
        }
        if pb.goal(&st) {
            let mut path = vec![];
            let mut s = st;
            while let (_, Some((ps, mv))) = &best[&s] {
                path.push((mvname(*mv), s));
                s = *ps;
            }
            path.reverse();
            println!("cost {g}, expanded {exp}");
            for (mv, s) in &path {
                let names: Vec<String> = s.s[..s.len as usize]
                    .iter()
                    .rev()
                    .map(|&v| pb.name(v))
                    .collect();
                println!("  {mv:8} [{}]", names.join(", "));
            }
            let dsl: Vec<&str> = path.iter().map(|(m, _)| m.as_str()).collect();
            println!("dsl: {}", dsl.join(" "));
            return Ok(());
        }
        exp += 1;
        if exp.is_multiple_of(1_000_000) {
            eprintln!(
                "expanded {exp} states {} queue {} f {f}",
                best.len(),
                pq.len()
            );
        }
        pb.moves(&st, &mut buf);
        for (c, mv, ns) in buf.drain(..) {
            let ng = g + c;
            if best.get(&ns).is_some_and(|b| b.0 <= ng) {
                continue;
            }
            let Some(hh) = pb.h(&ns) else { continue };
            if ng + hh >= ub {
                continue;
            }
            best.insert(ns, (ng, Some((st, mv))));
            cnt += 1;
            pq.push(Reverse((ng + hh, Reverse(ng), u64::MAX - cnt, ns)));
        }
    }
    println!(
        "no solution below {ub}, expanded {exp}, states {}",
        best.len()
    );
    Ok(())
}

#[cfg(test)]
#[path = "../t3int_tests.rs"]
mod tests;
