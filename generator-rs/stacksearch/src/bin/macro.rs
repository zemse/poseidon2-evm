// A* over macro moves for one Poseidon2 external round block (see main.rs
// for the value model). A macro is the next arithmetic op with its
// production and, per operand, whether it is consumed in place or copied;
// in-place operands are brought to the top with a swap sequence from a
// precomputed table (at most 3 swaps), copies are DUPed (constants pushed)
// on top. A chain pre-places the operands of the op that consumes the
// result in place (the addTo pattern). Standalone PushP, Pop and shallow
// Swap moves arrange the goal layout.
//
//   macro <t> <init> <goal> [reach] [max_garbage] [extra_depth] [final] [chain] [lazy,strict] [--no-swap]
//
// The search is partial-expansion A* (PEA*): a node stores only the
// children whose f is within its current threshold and comes back to the
// open list at the f of the cheapest child it dropped, so the memory holds
// the expanded nodes and the frontier at the optimal f rather than every
// child ever generated. A node is its key (the stack layout at 5 bits a
// slot and the computed mask), its parent, g and the threshold: 24 bytes,
// found through an open-addressing table of indices; the path is rebuilt
// by expanding the parents again. The parts of the heuristic and of the
// validity check that depend only on the computed mask (or on it and the
// set of classes on the stack) are memoized.

use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};

#[cfg(feature = "dhat-heap")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

/// hotpath::measure_block! under the profile feature, the block itself
/// otherwise
macro_rules! measure_block {
    ($name:expr, $body:block) => {{
        #[cfg(feature = "profile")]
        {
            hotpath::measure_block!($name, $body)
        }
        #[cfg(not(feature = "profile"))]
        {
            $body
        }
    }};
}

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

#[derive(Clone, Copy, Debug)]
enum Item {
    Copy(u8),
    P,
    Four,
}

/// the operand layout of a macro: the in-place operands (top-first) and
/// the copies (top-first) above them
#[derive(Clone, Copy, Debug)]
struct Layout {
    inplace: [u8; 3],
    ninplace: u8,
    copies: [Item; 3],
    ncopies: u8,
    prim: Prim,
    arity: u8,
}

impl Layout {
    fn new(inplace: &[u8], copies: &[Item], prim: Prim, arity: u8) -> Layout {
        let mut l = Layout {
            inplace: [0; 3],
            ninplace: inplace.len() as u8,
            copies: [Item::P; 3],
            ncopies: copies.len() as u8,
            prim,
            arity,
        };
        l.inplace[..inplace.len()].copy_from_slice(inplace);
        l.copies[..copies.len()].copy_from_slice(copies);
        l
    }
    fn inplace(&self) -> &[u8] {
        &self.inplace[..self.ninplace as usize]
    }
    fn copies(&self) -> &[Item] {
        &self.copies[..self.ncopies as usize]
    }
}

#[derive(Clone, Debug)]
struct Production {
    operands: Vec<u8>,
    kind: PKind,
    layouts: Vec<Layout>,
}

/// an op that can consume d in place, with the pre-placements of its other
/// operand (prim and arity of the layouts are those of the op)
#[derive(Clone, Debug)]
struct Cont {
    d2: u8,
    kind: PKind,
    other: Option<u8>,
    variants: Vec<Layout>,
}

const SBOX_P: u32 = 45;
const SBOX_NOP: u32 = 54;
const MAXD: usize = 18;
const NSWAP: usize = 18;

#[derive(Clone, Copy, Debug)]
struct Stack {
    s: [u8; MAXD],
    len: u8,
}

impl Stack {
    fn from(v: &[u8]) -> Stack {
        let mut s = Stack {
            s: [0; MAXD],
            len: v.len() as u8,
        };
        s.s[..v.len()].copy_from_slice(v);
        s
    }
    fn as_slice(&self) -> &[u8] {
        &self.s[..self.len as usize]
    }
    fn len(&self) -> usize {
        self.len as usize
    }
    fn push_top(&mut self, c: u8) {
        let n = self.len as usize;
        self.s.copy_within(0..n, 1);
        self.s[0] = c;
        self.len += 1;
    }
    /// pops `k` slots and pushes `c`
    fn replace_top(&mut self, k: usize, c: u8) {
        let n = self.len as usize;
        self.s.copy_within(k..n, 1);
        self.s[0] = c;
        self.len = (n - k + 1) as u8;
    }
    fn pop_top(&mut self) {
        let n = self.len as usize;
        self.s.copy_within(1..n, 0);
        self.len -= 1;
    }
    fn swap(&mut self, k: usize) {
        self.s.swap(0, k);
    }
    fn count(&self, c: u8) -> usize {
        self.as_slice().iter().filter(|&&x| x == c).count()
    }
    fn position(&self, c: u8) -> Option<usize> {
        self.as_slice().iter().position(|&x| x == c)
    }
    fn mask(&self) -> u32 {
        self.as_slice().iter().fold(0, |m, &c| m | (1 << c))
    }
}

#[derive(Clone, Copy, Debug)]
struct Prims {
    p: [Prim; 24],
    len: u8,
}

impl Prims {
    fn new() -> Prims {
        Prims {
            p: [Prim::Pop; 24],
            len: 0,
        }
    }
    fn push(&mut self, prim: Prim) {
        self.p[self.len as usize] = prim;
        self.len += 1;
    }
    fn as_slice(&self) -> &[Prim] {
        &self.p[..self.len as usize]
    }
}

#[derive(Clone, Copy, Debug)]
struct Child {
    stack: Stack,
    computed: u32,
    cost: u32,
    prims: Prims,
}

/// what depends on the computed mask alone
#[derive(Clone, Debug)]
struct CompInfo {
    needed: u32,
    h: u32,
    binary: i32,
    p_needed: i32,
    four_needed: i32,
    uses: [i32; 32],
}

#[derive(Default)]
struct FxHasher(u64);

impl Hasher for FxHasher {
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = (self.0.rotate_left(5) ^ b as u64).wrapping_mul(0x517cc1b727220a95);
        }
    }
    fn write_u32(&mut self, i: u32) {
        self.0 = (self.0.rotate_left(5) ^ i as u64).wrapping_mul(0x517cc1b727220a95);
    }
    fn write_u64(&mut self, i: u64) {
        self.0 = (self.0.rotate_left(5) ^ i).wrapping_mul(0x517cc1b727220a95);
    }
    fn finish(&self) -> u64 {
        self.0
    }
}

type FxMap<K, V> = HashMap<K, V, BuildHasherDefault<FxHasher>>;

/// the memoized parts of the heuristic and the validity check, and the
/// scratch of the chain recursion
struct Ctx {
    comp: FxMap<u32, u32>,
    infos: Vec<CompInfo>,
    avail: FxMap<u64, bool>,
    scratch: Vec<Vec<Child>>,
}

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
    no_swap: bool,
    clean_goal: bool,
    /// the classes of kind Val or Input
    values: u32,
    groups: Vec<(Vec<u8>, u32)>,
    consumers: Vec<Vec<u8>>,
    productions: Vec<Vec<Production>>,
    conts: Vec<Vec<Cont>>,
    /// swap sequences by the positions (top-first, 1-based, 0 absent) of
    /// up to 3 items: [len, swaps...], len 255 when out of reach
    swaps: Vec<[u8; 4]>,
}

fn key(stack: &[u8], computed: u32) -> (u64, u64) {
    let mut k: u128 = 0;
    for &c in stack {
        k = (k << 5) | (c as u128 + 1);
    }
    let k = (k << 32) | computed as u128;
    (k as u64, (k >> 64) as u64)
}

fn decode(lo: u64, hi: u64) -> (Stack, u32) {
    let key = (lo as u128) | ((hi as u128) << 64);
    let computed = (key & 0xffff_ffff) as u32;
    let mut k = key >> 32;
    let mut stack = Stack {
        s: [0; MAXD],
        len: 0,
    };
    while k != 0 {
        stack.s[stack.len as usize] = (k & 31) as u8 - 1;
        stack.len += 1;
        k >>= 5;
    }
    stack.s[..stack.len as usize].reverse();
    (stack, computed)
}

fn swap_index(pos: &[u8]) -> usize {
    let mut i = 0;
    for (j, &p) in pos.iter().enumerate() {
        i += p as usize * NSWAP.pow(j as u32);
    }
    i
}

/// Backward BFS over swap sequences: for m marked items, every position
/// tuple reachable from (1..m) within `depth` swaps.
fn swap_table(reach: usize, depth: usize) -> Vec<[u8; 4]> {
    let mut table = vec![[255, 0, 0, 0]; NSWAP * NSWAP * NSWAP];
    for m in 1..=3 {
        let goal: Vec<u8> = (1..=m as u8).collect();
        let mut seqs: HashMap<Vec<u8>, Vec<u8>> = HashMap::new();
        seqs.insert(goal.clone(), Vec::new());
        let mut queue = std::collections::VecDeque::new();
        queue.push_back(goal);
        while let Some(pos) = queue.pop_front() {
            let seq = seqs[&pos].clone();
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
                if !seqs.contains_key(&next) {
                    // the swaps to reach `next` from the goal reversed are the
                    // swaps from `next` to the goal (a swap is its own inverse)
                    let mut s = vec![n];
                    s.extend_from_slice(&seq);
                    seqs.insert(next.clone(), s);
                    queue.push_back(next);
                }
            }
        }
        for (pos, seq) in seqs {
            let mut e = [seq.len() as u8, 0, 0, 0];
            e[1..1 + seq.len()].copy_from_slice(&seq);
            table[swap_index(&pos)] = e;
        }
    }
    table
}

impl Problem {
    fn assert_supported(&self) {
        assert!(
            self.init.iter().all(|c| {
                self.classes[*c as usize].kind != Kind::Val || self.sbox_out.contains(c)
            }),
            "initial values must be raw inputs or S-box outputs"
        );
        let outputs: Vec<u8> = self
            .classes
            .iter()
            .enumerate()
            .filter(|(_, c)| {
                c.name.starts_with('o') || ["t4", "t5", "t6", "t7"].contains(&c.name.as_str())
            })
            .map(|(i, _)| i as u8)
            .collect();
        let mut fixed = 0u32;
        let mut count = 0;
        for &g in self.goal.iter().flatten() {
            if g == 255 {
                count += 1;
            } else if outputs.contains(&g) {
                assert!(fixed & (1 << g) == 0, "goal outputs must be distinct");
                fixed |= 1 << g;
                count += 1;
            } else {
                assert!(
                    g == self.prime || g == self.four,
                    "goal must contain outputs or constants"
                );
            }
        }
        assert_eq!(
            count,
            outputs.len(),
            "goal must require every output exactly once"
        );
    }

    fn needed_mask(&self, computed: u32) -> u32 {
        let n = self.classes.len();
        let mut memo = vec![0u8; n];
        fn rec(
            p: &Problem,
            c: usize,
            computed: u32,
            memo: &mut Vec<u8>,
            visiting: &mut Vec<bool>,
        ) -> bool {
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

    /// the needed mask and the stack-independent part of the heuristic
    #[cfg_attr(feature = "profile", hotpath::measure)]
    fn comp_info(&self, computed: u32) -> CompInfo {
        let needed = self.needed_mask(computed);
        let n = self.classes.len();
        let mut h = 0;
        let mut binary = 0;
        let mut p_needed = self.goal.iter().filter(|&&g| g == Some(self.prime)).count() as i32;
        let mut four_needed = self.goal.iter().filter(|&&g| g == Some(self.four)).count() as i32;
        let mut uses = [0i32; 32];
        let twos = self
            .classes
            .iter()
            .enumerate()
            .filter(|(c, class)| computed & (1 << c) != 0 && class.coeffs.iter().sum::<i32>() == 2)
            .count();
        for (group, (members, cost)) in self.groups.iter().enumerate() {
            // A t3 output can use two degree-two forms instead of a
            // degree-three form. The second group counts either route.
            if self.sbox_out.len() == 3 && group == 1 && twos >= 2 {
                continue;
            }
            let any_computed = members.iter().any(|&m| computed & (1 << m) != 0);
            let any_needed = members.iter().any(|&m| needed & (1 << m) != 0);
            if any_computed || !any_needed {
                continue;
            }
            h += cost;
            let mut needs_p = true;
            let mut needs_4 = true;
            let mut needs_binary = true;
            let mut min_use = [i32::MAX; 32];
            for &m in members {
                for prod in &self.productions[m as usize] {
                    if prod.kind == PKind::Add {
                        needs_p = false;
                    }
                    if prod.kind != PKind::Mulmod {
                        needs_4 = false;
                    }
                    if !matches!(prod.kind, PKind::Add | PKind::Addmod) {
                        needs_binary = false;
                    }
                    let mut mult = [0i32; 32];
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
            if needs_binary {
                binary += 1;
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
        for c in 0..n {
            if self.goal_set & (1 << c) != 0 {
                uses[c] += 1;
            }
        }
        CompInfo {
            needed,
            h,
            binary,
            p_needed,
            four_needed,
            uses,
        }
    }

    fn info<'a>(&self, ctx: &'a mut Ctx, computed: u32) -> &'a CompInfo {
        let idx = match ctx.comp.get(&computed) {
            Some(&i) => i as usize,
            None => {
                let info = self.comp_info(computed);
                ctx.infos.push(info);
                let i = ctx.infos.len() - 1;
                ctx.comp.insert(computed, i as u32);
                i
            }
        };
        &ctx.infos[idx]
    }

    #[cfg_attr(feature = "profile", hotpath::measure)]
    fn heuristic(&self, stack: &Stack, computed: u32, info: &CompInfo) -> u32 {
        let mut copies = [0i32; 32];
        for &c in stack.as_slice() {
            copies[c as usize] += 1;
        }
        let mut h = info.h;
        h += 3 * (info.p_needed - copies[self.prime as usize]).max(0) as u32;
        h += 3 * (info.four_needed - copies[self.four as usize]).max(0) as u32;
        let mut duplicates = 0;
        let mut m = computed;
        while m != 0 {
            let c = m.trailing_zeros() as usize;
            m &= m - 1;
            if self.classes[c].kind == Kind::Val {
                duplicates += (info.uses[c] - copies[c]).max(0);
            }
        }
        // Every remaining binary op consumes one value slot; S-boxes and
        // multiplication by four preserve it. Only DUP can restore it;
        // dead values cannot supply any remaining operand or output.
        // An input supplies one slot: its only consumer is its S-box, so a
        // second copy is dead once the S-box ran.
        let mut values = 0;
        let mut inputs = 0u32;
        for &c in stack.as_slice() {
            if self.values & info.needed & (1 << c) == 0 {
                continue;
            }
            if self.classes[c as usize].kind == Kind::Val {
                values += 1;
            } else if inputs & (1 << c) == 0 {
                inputs |= 1 << c;
                values += 1;
            }
        }
        let deficit = info.binary + self.goal_set.count_ones() as i32 - values;
        // An S-box takes its input on top. Only a DUP or SWAP of that input
        // or a POP right above it brings it there (an op leaves its result
        // on top), at least 2 gas for each lane left but the one on top.
        let mut lanes = 0;
        let mut on_top = false;
        for (i, &x) in self.sbox_out.iter().enumerate() {
            if computed & (1 << x) == 0 && info.needed & (1 << x) != 0 {
                lanes += 1;
                on_top |= stack.len() > 0 && stack.s[0] == self.sbox_in[i];
            }
        }
        let lanes = lanes - on_top as u32;
        h + 3 * duplicates.max(deficit).max(0) as u32 + 2 * lanes
    }

    fn is_goal(&self, stack: &[u8]) -> bool {
        if stack.len() < self.goal.len() || (self.clean_goal && stack.len() != self.goal.len()) {
            return false;
        }
        let mut seen = self
            .goal
            .iter()
            .flatten()
            .filter(|&&g| g != 255)
            .fold(0u32, |mask, &g| mask | (1 << g));
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

    /// the values (not constants) that are dead under `needed`
    fn dead_mask(&self, needed: u32) -> u32 {
        self.values & !needed
    }

    fn garbage(&self, stack: &Stack, needed: u32) -> usize {
        let mut dead = 0;
        for &c in stack.as_slice() {
            if match self.classes[c as usize].kind {
                Kind::Val | Kind::Input(_) => needed & (1 << c) == 0,
                _ => false,
            } {
                dead += 1;
            }
        }
        if !self.strict {
            return dead;
        }
        // strict: constants left over count as well, beyond the copies the
        // goal keeps
        let extra = |c: u8| {
            let on_stack = stack.count(c);
            let kept = self.goal.iter().filter(|&&g| g == Some(c)).count();
            on_stack.saturating_sub(kept)
        };
        dead + extra(self.prime) + extra(self.four)
    }

    /// Brings the in-place items (top-first required order) to the top and
    /// pushes the copies (top-first order) above them. Returns the stack
    /// and the cost, or None when out of reach.
    #[cfg_attr(feature = "profile", hotpath::measure)]
    fn realize(
        &self,
        stack: &Stack,
        inplace: &[u8],
        copies: &[Item],
        prims: &mut Prims,
    ) -> Option<(Stack, u32)> {
        let mut s = *stack;
        let mut cost = 0;
        if !inplace.is_empty() {
            // positions: the shallowest copy of each, distinct slots
            let mut pos = [0u8; 3];
            for (j, &c) in inplace.iter().enumerate() {
                let mut found = None;
                for (i, &x) in s.as_slice().iter().enumerate() {
                    if x == c && !pos[..j].contains(&(i as u8 + 1)) {
                        found = Some(i as u8 + 1);
                        break;
                    }
                }
                pos[j] = found?;
            }
            let seq = self.swaps[swap_index(&pos[..inplace.len()])];
            if seq[0] == 255 {
                return None;
            }
            for &n in &seq[1..1 + seq[0] as usize] {
                if n as usize >= s.len() {
                    return None;
                }
                s.swap(n as usize);
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
                    let k = s.position(c)? + 1;
                    if k > self.reach {
                        return None;
                    }
                    s.push_top(c);
                    prims.push(Prim::Dup(k as u8));
                }
                Item::P => {
                    s.push_top(self.prime);
                    prims.push(Prim::PushP);
                }
                Item::Four => {
                    s.push_top(self.four);
                    prims.push(Prim::Push4);
                }
            }
            cost += 3;
        }
        Some((s, cost))
    }

    /// The operand layouts of a production: (in-place top-first, copies
    /// top-first, the op prim, its arity) for every in-place choice.
    fn layouts(&self, operands: &[u8], kind: PKind) -> Vec<Layout> {
        let mut out = Vec::new();
        let p = self.prime;
        match kind {
            PKind::Sbox => {
                let s = operands[0];
                let lane = match self.classes[s as usize].kind {
                    Kind::Input(i) => i,
                    _ => unreachable!(),
                };
                out.push(Layout::new(&[s], &[], Prim::SboxNoP(lane), 1));
                out.push(Layout::new(&[s, p], &[], Prim::SboxP(lane), 2));
                out.push(Layout::new(&[], &[Item::Copy(s)], Prim::SboxNoP(lane), 1));
                out.push(Layout::new(
                    &[],
                    &[Item::Copy(s), Item::P],
                    Prim::SboxP(lane),
                    2,
                ));
                out.push(Layout::new(&[p], &[Item::Copy(s)], Prim::SboxP(lane), 2));
            }
            PKind::Add => {
                let (a, b) = (operands[0], operands[1]);
                out.push(Layout::new(
                    &[],
                    &[Item::Copy(a), Item::Copy(b)],
                    Prim::Add,
                    2,
                ));
                if a != b {
                    out.push(Layout::new(
                        &[],
                        &[Item::Copy(b), Item::Copy(a)],
                        Prim::Add,
                        2,
                    ));
                }
                out.push(Layout::new(&[a], &[Item::Copy(b)], Prim::Add, 2));
                if a != b {
                    out.push(Layout::new(&[b], &[Item::Copy(a)], Prim::Add, 2));
                }
                out.push(Layout::new(&[a, b], &[], Prim::Add, 2));
                if a != b {
                    out.push(Layout::new(&[b, a], &[], Prim::Add, 2));
                }
            }
            PKind::Addmod => {
                let (a, b) = (operands[0], operands[1]);
                out.push(Layout::new(
                    &[],
                    &[Item::Copy(a), Item::Copy(b), Item::P],
                    Prim::Addmod,
                    3,
                ));
                if a != b {
                    out.push(Layout::new(
                        &[],
                        &[Item::Copy(b), Item::Copy(a), Item::P],
                        Prim::Addmod,
                        3,
                    ));
                }
                out.push(Layout::new(
                    &[p],
                    &[Item::Copy(a), Item::Copy(b)],
                    Prim::Addmod,
                    3,
                ));
                if a != b {
                    out.push(Layout::new(
                        &[p],
                        &[Item::Copy(b), Item::Copy(a)],
                        Prim::Addmod,
                        3,
                    ));
                }
                out.push(Layout::new(&[a, p], &[Item::Copy(b)], Prim::Addmod, 3));
                if a != b {
                    out.push(Layout::new(&[b, p], &[Item::Copy(a)], Prim::Addmod, 3));
                }
                out.push(Layout::new(&[a, b, p], &[], Prim::Addmod, 3));
                if a != b {
                    out.push(Layout::new(&[b, a, p], &[], Prim::Addmod, 3));
                }
            }
            PKind::Mulmod => {
                let v = operands[0];
                out.push(Layout::new(
                    &[],
                    &[Item::Four, Item::Copy(v), Item::P],
                    Prim::Mulmod,
                    3,
                ));
                out.push(Layout::new(
                    &[],
                    &[Item::Copy(v), Item::Four, Item::P],
                    Prim::Mulmod,
                    3,
                ));
                out.push(Layout::new(
                    &[p],
                    &[Item::Four, Item::Copy(v)],
                    Prim::Mulmod,
                    3,
                ));
                out.push(Layout::new(
                    &[p],
                    &[Item::Copy(v), Item::Four],
                    Prim::Mulmod,
                    3,
                ));
                out.push(Layout::new(&[v, p], &[Item::Four], Prim::Mulmod, 3));
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

    /// Every macro from a state into `out`.
    #[cfg_attr(feature = "profile", hotpath::measure)]
    fn expand(
        &self,
        ctx: &mut Ctx,
        stack: &Stack,
        computed: u32,
        needed: u32,
        out: &mut Vec<Child>,
    ) {
        out.clear();
        let n = self.classes.len();
        // standalone moves
        if stack.len() < self.max_depth && stack.count(self.prime) < 3 {
            let mut s = *stack;
            s.push_top(self.prime);
            let mut prims = Prims::new();
            prims.push(Prim::PushP);
            out.push(Child {
                stack: s,
                computed,
                cost: 3,
                prims,
            });
        }
        if stack.len() > 0 {
            let top = stack.s[0];
            let dead = match self.classes[top as usize].kind {
                Kind::Val | Kind::Input(_) => needed & (1 << top) == 0,
                _ => true,
            };
            if dead {
                let mut s = *stack;
                s.pop_top();
                let mut prims = Prims::new();
                prims.push(Prim::Pop);
                out.push(Child {
                    stack: s,
                    computed,
                    cost: 2,
                    prims,
                });
            }
        }
        if !self.no_swap {
            for k in 1..=4usize.min(stack.len().saturating_sub(1)) {
                if stack.s[0] != stack.s[k] {
                    let mut s = *stack;
                    s.swap(k);
                    let mut prims = Prims::new();
                    prims.push(Prim::Swap(k as u8));
                    out.push(Child {
                        stack: s,
                        computed,
                        cost: 3,
                        prims,
                    });
                }
            }
        }
        // arithmetic macros with chains
        let smask = stack.mask();
        for d in 0..n {
            if computed & (1 << d) != 0 || needed & (1 << d) == 0 {
                continue;
            }
            for pi in 0..self.productions[d].len() {
                let prod = &self.productions[d][pi];
                // operands must exist
                if prod
                    .operands
                    .iter()
                    .any(|&o| match self.classes[o as usize].kind {
                        Kind::Val => computed & (1 << o) == 0,
                        Kind::Input(_) => smask & (1 << o) == 0,
                        _ => false,
                    })
                {
                    continue;
                }
                self.chain(
                    ctx,
                    computed,
                    needed,
                    d as u8,
                    prod,
                    &Prims::new(),
                    stack,
                    0,
                    0,
                    out,
                );
            }
        }
    }

    /// Macro of d via prod after `pre` prims (the pre-placements of the
    /// chain so far, giving `stack`), then recursively the ops the chain
    /// continues with.
    #[allow(clippy::too_many_arguments)]
    #[cfg_attr(feature = "profile", hotpath::measure)]
    fn chain(
        &self,
        ctx: &mut Ctx,
        computed: u32,
        needed: u32,
        d: u8,
        prod: &Production,
        pre: &Prims,
        stack: &Stack,
        pre_cost: u32,
        depth: usize,
        out: &mut Vec<Child>,
    ) {
        // chain continuation: an op consuming d in place with its other
        // operands pre-placed now
        // A nested continuation leaves d2 on top, not the d the outer
        // continuation requires, so only the recursive base case survives.
        if depth == 0 && self.chain != 0 {
            for ci in 0..self.conts[d as usize].len() {
                let cont = &self.conts[d as usize][ci];
                let d2 = cont.d2;
                if computed & (1 << d2) != 0 || needed & (1 << d2) == 0 {
                    continue;
                }
                // the other operand must be computed
                if let Some(o) = cont.other {
                    if computed & (1 << o) == 0 {
                        continue;
                    }
                }
                // a lower bound on the garbage after op2: what is dead
                // then and stays on the stack even if d's macro consumes
                // every operand it can in place
                let dead2 = self.dead_mask(self.info(ctx, computed | (1 << d) | (1 << d2)).needed);
                for vi in 0..cont.variants.len() {
                    let v = &cont.variants[vi];
                    let mut lb = 0usize;
                    for &c in stack.as_slice() {
                        if dead2 & (1 << c) != 0 {
                            lb += 1;
                        }
                    }
                    for &c in v.inplace() {
                        if dead2 & (1 << c) != 0 {
                            lb = lb.saturating_sub(1);
                        }
                    }
                    for &c in &prod.operands {
                        if dead2 & (1 << c) != 0
                            && stack.count(c) > v.inplace().iter().filter(|&&x| x == c).count()
                        {
                            lb = lb.saturating_sub(1);
                        }
                    }
                    if lb > self.max_garbage {
                        continue;
                    }
                    let mut prims = *pre;
                    let Some((s2, c2)) = self.realize(stack, v.inplace(), v.copies(), &mut prims)
                    else {
                        continue;
                    };
                    // continue the chain with d's macro on top of the pre-placement, then op2
                    let mut sub = std::mem::take(&mut ctx.scratch[depth]);
                    sub.clear();
                    self.chain(
                        ctx,
                        computed,
                        needed,
                        d,
                        prod,
                        &prims,
                        &s2,
                        pre_cost + c2,
                        depth + 1,
                        &mut sub,
                    );
                    for ch in sub.iter() {
                        // apply op2: d on top, operands below
                        let arity = match cont.kind {
                            PKind::Add => 2,
                            _ => 3,
                        };
                        let mut s3 = ch.stack;
                        if s3.len() < arity || s3.s[0] != d {
                            continue;
                        }
                        let mut p3 = ch.prims;
                        let prim = match cont.kind {
                            PKind::Add => Prim::Add,
                            PKind::Addmod => Prim::Addmod,
                            PKind::Mulmod => {
                                // push 4 on top of d
                                if s3.len() >= self.max_depth {
                                    continue;
                                }
                                s3.push_top(self.four);
                                p3.push(Prim::Push4);
                                Prim::Mulmod
                            }
                            PKind::Sbox => unreachable!(),
                        };
                        let extra = if cont.kind == PKind::Mulmod { 3 } else { 0 };
                        // check operand layout
                        let ok = match cont.kind {
                            PKind::Add => s3.s[1] == cont.other.unwrap(),
                            PKind::Addmod => {
                                s3.s[1] == cont.other.unwrap() && s3.s[2] == self.prime
                            }
                            PKind::Mulmod => s3.s[1] == d && s3.s[2] == self.prime,
                            PKind::Sbox => false,
                        };
                        if !ok {
                            continue;
                        }
                        s3.replace_top(arity, d2);
                        p3.push(prim);
                        let computed4 = ch.computed | (1 << d2);
                        if self.valid(ctx, &s3, computed4) {
                            out.push(Child {
                                stack: s3,
                                computed: computed4,
                                cost: ch.cost + extra + Self::op_cost(prim),
                                prims: p3,
                            });
                        }
                    }
                    ctx.scratch[depth] = sub;
                }
            }
        }
        // d itself; the garbage after it is what is dead then minus the
        // operands consumed in place, so a layout over the limit is skipped
        // before it is realized
        let dead = self.dead_mask(self.info(ctx, computed | (1 << d)).needed);
        let mut base = 0usize;
        for &c in stack.as_slice() {
            if dead & (1 << c) != 0 {
                base += 1;
            }
        }
        for li in 0..prod.layouts.len() {
            let l = &prod.layouts[li];
            let garbage = base.saturating_sub(
                l.inplace()
                    .iter()
                    .filter(|&&c| dead & (1 << c) != 0)
                    .count(),
            );
            if garbage > self.max_garbage {
                continue;
            }
            let mut prims = *pre;
            let Some((mut s2, c2)) = self.realize(stack, l.inplace(), l.copies(), &mut prims)
            else {
                continue;
            };
            // the in-place operands and the copies now sit on top; apply
            s2.replace_top(l.arity as usize, d);
            prims.push(l.prim);
            let computed3 = computed | (1 << d);
            if self.valid(ctx, &s2, computed3) {
                out.push(Child {
                    stack: s2,
                    computed: computed3,
                    cost: pre_cost + c2 + Self::op_cost(l.prim),
                    prims,
                });
            }
        }
    }

    /// every goal value can still be produced from what is on the stack
    /// (a computed value that left the stack is lost), garbage within the
    /// limit
    #[cfg_attr(feature = "profile", hotpath::measure)]
    fn valid(&self, ctx: &mut Ctx, stack: &Stack, computed: u32) -> bool {
        let needed = self.info(ctx, computed).needed;
        if self.garbage(stack, needed) > self.max_garbage {
            return false;
        }
        let smask = stack.mask();
        let k = ((computed as u64) << 32) | smask as u64;
        if let Some(&v) = ctx.avail.get(&k) {
            return v;
        }
        let n = self.classes.len();
        let mut avail = smask | (1 << self.prime) | (1 << self.four);
        loop {
            let mut changed = false;
            for d in 0..n {
                if avail & (1 << d) != 0
                    || computed & (1 << d) != 0
                    || self.classes[d].kind != Kind::Val
                {
                    continue;
                }
                if self.productions[d]
                    .iter()
                    .any(|prod| prod.operands.iter().all(|&o| avail & (1 << o) != 0))
                {
                    avail |= 1 << d;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        let v = self.goal_set & !avail == 0;
        ctx.avail.insert(k, v);
        v
    }
}

const CLOSED: u16 = u16::MAX;

#[derive(Clone, Copy)]
struct Node {
    lo: u64,
    hi: u64,
    parent: u32,
    g: u16,
    /// the f threshold of the next expansion (the f of the cheapest child
    /// dropped so far), CLOSED when none is left
    f: u16,
}

/// open-addressing table of node indices keyed by the node's key
struct Table {
    slots: Vec<u32>,
    count: usize,
}

impl Table {
    fn new() -> Table {
        Table {
            slots: vec![u32::MAX; 1 << 16],
            count: 0,
        }
    }
    fn hash(lo: u64, hi: u64) -> u64 {
        (lo ^ hi.rotate_left(29))
            .wrapping_mul(0x9E3779B97F4A7C15)
            .rotate_left(23)
            .wrapping_mul(0xD6E8FEB86659FD93)
    }
    fn find(&self, nodes: &[Node], lo: u64, hi: u64) -> Result<u32, usize> {
        let mask = self.slots.len() - 1;
        let mut i = Self::hash(lo, hi) as usize & mask;
        loop {
            let idx = self.slots[i];
            if idx == u32::MAX {
                return Err(i);
            }
            let n = &nodes[idx as usize];
            if n.lo == lo && n.hi == hi {
                return Ok(idx);
            }
            i = (i + 1) & mask;
        }
    }
    fn insert_at(&mut self, nodes: &[Node], slot: usize, idx: u32) {
        self.slots[slot] = idx;
        self.count += 1;
        if self.count * 10 > self.slots.len() * 6 {
            let cap = self.slots.len() * 2;
            let old = std::mem::replace(&mut self.slots, vec![u32::MAX; cap]);
            let mask = self.slots.len() - 1;
            for idx in old.into_iter().filter(|&i| i != u32::MAX) {
                let n = &nodes[idx as usize];
                let mut i = Self::hash(n.lo, n.hi) as usize & mask;
                while self.slots[i] != u32::MAX {
                    i = (i + 1) & mask;
                }
                self.slots[i] = idx;
            }
        }
    }
}

#[derive(Default)]
struct Bucket {
    levels: Vec<Vec<u32>>,
    max: usize,
}

impl Bucket {
    fn push(&mut self, g: u16, idx: u32) {
        let g = g as usize;
        if g >= self.levels.len() {
            self.levels.resize_with(g + 1, Vec::new);
        }
        self.levels[g].push(idx);
        self.max = self.max.max(g);
    }

    fn pop(&mut self) -> Option<u32> {
        loop {
            if let Some(level) = self.levels.get_mut(self.max) {
                if let Some(idx) = level.pop() {
                    return Some(idx);
                }
                *level = Vec::new();
            }
            if self.max == 0 {
                return None;
            }
            self.max -= 1;
        }
    }
}

struct Open {
    buckets: Vec<Bucket>,
    min: usize,
    len: usize,
}

impl Open {
    fn push(&mut self, f: u16, g: u16, idx: u32) {
        let f = f as usize;
        if f >= self.buckets.len() {
            self.buckets.resize_with(f + 1, Bucket::default);
        }
        self.buckets[f].push(g, idx);
        self.len += 1;
        if f < self.min {
            self.min = f;
        }
    }
    fn pop(&mut self) -> Option<(u16, u32)> {
        while self.min < self.buckets.len() {
            if let Some(idx) = self.buckets[self.min].pop() {
                self.len -= 1;
                return Some((self.min as u16, idx));
            }
            self.buckets[self.min] = Bucket::default();
            self.min += 1;
        }
        None
    }
}

fn mem_estimate(nodes: &Vec<Node>, table: &Table, open: &Open) -> usize {
    nodes.capacity() * std::mem::size_of::<Node>()
        + table.slots.len() * 4
        + open
            .buckets
            .iter()
            .map(|b| {
                b.levels.capacity() * std::mem::size_of::<Vec<u32>>()
                    + b.levels
                        .iter()
                        .map(|level| level.capacity() * 4)
                        .sum::<usize>()
            })
            .sum::<usize>()
}

#[cfg_attr(feature = "profile", hotpath::measure)]
fn search(p: &Problem, ctx: &mut Ctx) -> Option<(u32, Vec<(Prim, Vec<u8>)>)> {
    let mut nodes: Vec<Node> = Vec::new();
    let mut table = Table::new();
    let mut open = Open {
        buckets: Vec::new(),
        min: 0,
        len: 0,
    };
    let init = Stack::from(&p.init);
    let (lo, hi) = key(init.as_slice(), p.init_computed);
    let h0 = {
        let info = p.info(ctx, p.init_computed).clone();
        p.heuristic(&init, p.init_computed, &info)
    };
    nodes.push(Node {
        lo,
        hi,
        parent: u32::MAX,
        g: 0,
        f: h0 as u16,
    });
    let slot = table.find(&nodes, lo, hi).unwrap_err();
    table.insert_at(&nodes, slot, 0);
    open.push(h0 as u16, 0, 0);
    let mut expanded = 0usize;
    let mut children = Vec::new();
    let dbg = std::env::var("DBG").is_ok();
    // UB=<cost>: only programs strictly cheaper than cost
    let ub: u32 = std::env::var("UB").map_or(u32::MAX, |v| v.parse().unwrap());
    eprintln!("h0 {h0}");
    while let Some((f, idx)) = measure_block!("open_pop", { open.pop() }) {
        let node = nodes[idx as usize];
        if node.f != f {
            continue;
        }
        let (stack, computed) = decode(node.lo, node.hi);
        let g = node.g as u32;
        if p.is_goal(stack.as_slice()) {
            eprintln!(
                "expanded {expanded} nodes, {} states, open {}, ~{} MB",
                nodes.len(),
                open.len,
                mem_estimate(&nodes, &table, &open) >> 20
            );
            return Some((g, reconstruct(p, ctx, &nodes, idx)));
        }
        expanded += 1;
        if expanded % 1_000_000 == 0 {
            eprintln!(
                "expanded {expanded}, states {}, open {}, ~{} MB, g {g} f {f}",
                nodes.len(),
                open.len,
                mem_estimate(&nodes, &table, &open) >> 20
            );
        }
        let needed = p.info(ctx, computed).needed;
        p.expand(ctx, &stack, computed, needed, &mut children);
        let mut next_f = u32::MAX;
        for ch in children.iter() {
            let g2 = g + ch.cost;
            let h = {
                let info = p.info(ctx, ch.computed);
                p.heuristic(&ch.stack, ch.computed, info)
            };
            if dbg {
                let names: Vec<&str> = ch
                    .stack
                    .as_slice()
                    .iter()
                    .map(|&c| p.classes[c as usize].name.as_str())
                    .collect();
                eprintln!(
                    "  from g={g} {:?} -> g={} [{}] h={}",
                    ch.prims.as_slice(),
                    g2,
                    names.join(","),
                    h
                );
            }
            let f2 = g2 + h;
            if f2 >= ub {
                continue;
            }
            if f2 > f as u32 {
                if f2 < next_f {
                    next_f = f2;
                }
                continue;
            }
            let (lo, hi) = key(ch.stack.as_slice(), ch.computed);
            match measure_block!("closed_lookup", { table.find(&nodes, lo, hi) }) {
                Ok(j) => {
                    let m = &mut nodes[j as usize];
                    if m.g as u32 <= g2 {
                        continue;
                    }
                    m.g = g2 as u16;
                    m.parent = idx;
                    m.f = f2 as u16;
                    open.push(f2 as u16, g2 as u16, j);
                }
                Err(slot) => {
                    measure_block!("closed_insert", {
                        nodes.push(Node {
                            lo,
                            hi,
                            parent: idx,
                            g: g2 as u16,
                            f: f2 as u16,
                        });
                        let j = (nodes.len() - 1) as u32;
                        table.insert_at(&nodes, slot, j);
                        open.push(f2 as u16, g2 as u16, j);
                    });
                }
            }
        }
        if next_f != u32::MAX {
            nodes[idx as usize].f = next_f as u16;
            open.push(next_f as u16, node.g, idx);
        } else {
            nodes[idx as usize].f = CLOSED;
        }
    }
    None
}

/// the macros from the root to `idx`, by expanding each parent again
fn reconstruct(p: &Problem, ctx: &mut Ctx, nodes: &[Node], idx: u32) -> Vec<(Prim, Vec<u8>)> {
    let mut chain = vec![idx];
    while nodes[*chain.last().unwrap() as usize].parent != u32::MAX {
        chain.push(nodes[*chain.last().unwrap() as usize].parent);
    }
    chain.reverse();
    let mut path = Vec::new();
    let mut s = p.init.clone();
    let mut children = Vec::new();
    for w in chain.windows(2) {
        let (a, b) = (nodes[w[0] as usize], nodes[w[1] as usize]);
        let (stack, computed) = decode(a.lo, a.hi);
        let needed = p.info(ctx, computed).needed;
        p.expand(ctx, &stack, computed, needed, &mut children);
        let cost = b.g as u32 - a.g as u32;
        let found = children
            .iter()
            .filter(|ch| key(ch.stack.as_slice(), ch.computed) == (b.lo, b.hi))
            .min_by_key(|ch| if ch.cost == cost { 0 } else { 1 })
            .expect("no macro from the parent to the child");
        assert_eq!(found.cost, cost, "macro cost differs from the path");
        for &prim in found.prims.as_slice() {
            apply_prim(p, &mut s, prim);
            path.push((prim, s.clone()));
        }
        assert_eq!(
            s,
            decode(b.lo, b.hi).0.as_slice(),
            "macro replay differs from the child"
        );
    }
    assert!(p.is_goal(&s), "replay does not reach the goal");
    path
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
            let r = p
                .classes
                .iter()
                .position(|c| c.kind == Kind::Val && c.coeffs == coeffs && c.bound == bound)
                .unwrap();
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
            let r = p
                .classes
                .iter()
                .position(|c| c.kind == Kind::Val && c.coeffs == coeffs && c.bound == 1)
                .unwrap();
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
            let r = p
                .classes
                .iter()
                .position(|c| c.kind == Kind::Val && c.coeffs == coeffs && c.bound == 1)
                .unwrap();
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
        classes.push(Class {
            coeffs,
            bound,
            name: name.to_string(),
            kind,
        });
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

fn problem(args: &[String], no_swap: bool) -> Problem {
    let t: usize = args[1].parse().unwrap();
    let init_names: Vec<&str> = args[2].split(',').collect();
    let goal_names: Vec<&str> = args[3].split(',').collect();
    let reach: usize = args.get(4).map_or(16, |s| s.parse().unwrap());
    let max_garbage: usize = args.get(5).map_or(2, |s| s.parse().unwrap());
    let extra_depth: usize = args.get(6).map_or(8, |s| s.parse().unwrap());
    let final_round = args.get(7).map_or(false, |s| s == "final");
    let chain: usize = args.get(8).map_or(2, |s| s.parse().unwrap());
    let lazy = args.get(9).map_or(false, |s| s.contains("lazy"));
    assert!(!lazy || t == 4, "lazy inputs are supported only for t4");
    assert!((1..=16).contains(&reach), "reach must be between 1 and 16");
    let strict = args.get(9).map_or(false, |s| s.contains("strict"));
    let (classes, groups) = build(t, final_round, lazy);
    assert!(classes.len() <= 31, "too many classes for the key");
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
        .map(|n| {
            if *n == "_" {
                None
            } else if *n == "O" {
                Some(255)
            } else {
                Some(idx(n))
            }
        })
        .collect();
    let mut goal_set = 0u32;
    for g in goal.iter().flatten() {
        if *g == 255 {
            for (i, c) in classes.iter().enumerate() {
                if c.kind == Kind::Val
                    && (c.name.starts_with('o')
                        || ["t4", "t5", "t6", "t7"].contains(&c.name.as_str()))
                {
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
                productions[d].push(Production {
                    operands: vec![sbox_in[i]],
                    kind: PKind::Sbox,
                    layouts: Vec::new(),
                });
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
                    productions[d].push(Production {
                        operands: vec![c as u8, e as u8],
                        kind: PKind::Add,
                        layouts: Vec::new(),
                    });
                } else if dc.bound == 1 {
                    productions[d].push(Production {
                        operands: vec![c as u8, e as u8],
                        kind: PKind::Addmod,
                        layouts: Vec::new(),
                    });
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
            if dc.bound == 1
                && cc.coeffs != [0; 4]
                && (0..4).all(|i| dc.coeffs[i] == 4 * cc.coeffs[i])
            {
                productions[d].push(Production {
                    operands: vec![c as u8],
                    kind: PKind::Mulmod,
                    layouts: Vec::new(),
                });
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
    let swaps = swap_table(reach, 3);
    let values = classes
        .iter()
        .enumerate()
        .filter(|(_, c)| matches!(c.kind, Kind::Val | Kind::Input(_)))
        .fold(0, |m, (i, _)| m | (1 << i));
    let mut p = Problem {
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
        no_swap,
        clean_goal: false,
        values,
        groups,
        consumers,
        productions,
        conts: vec![Vec::new(); n],
        swaps,
    };
    // the operand layouts of every production and the chain continuations
    // of every class
    for d in 0..n {
        for pi in 0..p.productions[d].len() {
            let (operands, kind) = (
                p.productions[d][pi].operands.clone(),
                p.productions[d][pi].kind,
            );
            p.productions[d][pi].layouts = p.layouts(&operands, kind);
        }
    }
    for d in 0..n {
        let mut conts = Vec::new();
        for &d2 in &p.consumers[d] {
            for prod2 in &p.productions[d2 as usize] {
                if !prod2.operands.contains(&(d as u8)) || prod2.kind == PKind::Sbox {
                    continue;
                }
                let mut others = prod2.operands.clone();
                let i = others.iter().position(|&o| o == d as u8).unwrap();
                others.remove(i);
                // pre-placements: for add [b]; addmod [b, P]; mulmod [P] (4 after)
                let variants: Vec<Layout> = match prod2.kind {
                    PKind::Add => {
                        let b = others[0];
                        vec![
                            Layout::new(&[], &[Item::Copy(b)], Prim::Add, 2),
                            Layout::new(&[b], &[], Prim::Add, 2),
                        ]
                    }
                    PKind::Addmod => {
                        let b = others[0];
                        vec![
                            Layout::new(&[], &[Item::Copy(b), Item::P], Prim::Addmod, 3),
                            Layout::new(&[prime], &[Item::Copy(b)], Prim::Addmod, 3),
                            Layout::new(&[b, prime], &[], Prim::Addmod, 3),
                        ]
                    }
                    PKind::Mulmod => vec![
                        Layout::new(&[], &[Item::P], Prim::Mulmod, 3),
                        Layout::new(&[prime], &[], Prim::Mulmod, 3),
                    ],
                    PKind::Sbox => unreachable!(),
                };
                conts.push(Cont {
                    d2,
                    kind: prod2.kind,
                    other: others.first().copied(),
                    variants,
                });
            }
        }
        p.conts[d] = conts;
    }
    p
}

impl Ctx {
    fn new() -> Self {
        Self {
            comp: FxMap::default(),
            infos: Vec::new(),
            avail: FxMap::default(),
            scratch: vec![Vec::new(); 2],
        }
    }
}

#[cfg_attr(feature = "profile", hotpath::main)]
fn main() {
    #[cfg(feature = "dhat-heap")]
    let _profiler = dhat::Profiler::new_heap();
    let all: Vec<String> = std::env::args().collect();
    let no_swap = all.iter().any(|a| a == "--no-swap");
    let clean_goal = all.iter().any(|a| a == "--clean-goal");
    let args: Vec<String> = all.into_iter().filter(|a| !a.starts_with("--")).collect();
    let mut p = problem(&args, no_swap);
    p.clean_goal = clean_goal;
    p.assert_supported();
    let mut ctx = Ctx::new();
    match search(&p, &mut ctx) {
        Some((cost, path)) => {
            println!("cost {cost}");
            if let Some((_, stack)) = path.last() {
                let names: Vec<&str> = stack
                    .iter()
                    .map(|&c| p.classes[c as usize].name.as_str())
                    .collect();
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
                let names: Vec<&str> = stack
                    .iter()
                    .map(|&c| p.classes[c as usize].name.as_str())
                    .collect();
                println!(
                    "{:<12} {:>4}  [{}]",
                    format!("{prim:?}"),
                    g,
                    names.join(", ")
                );
            }
        }
        None => println!("no solution"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture(args: &str) -> Problem {
        problem(
            &args
                .split_whitespace()
                .map(str::to_string)
                .collect::<Vec<_>>(),
            false,
        )
    }

    fn class(p: &Problem, name: &str) -> u8 {
        p.classes.iter().position(|c| c.name == name).unwrap() as u8
    }

    #[test]
    fn t3_two_plus_two_needs_no_degree_three_form() {
        let mut p = fixture("macro 3 110,101,P,o1,o2 o0,o1,o2 16 2 8 final 1");
        for &x in &p.sbox_out {
            p.init_computed |= 1 << x;
        }
        let info = p.comp_info(p.init_computed);
        assert_eq!(
            p.heuristic(&Stack::from(&p.init), p.init_computed, &info),
            8
        );
        assert_eq!(search(&p, &mut Ctx::new()).unwrap().0, 8);
    }

    #[test]
    fn resource_bounds_count_future_duplicates_and_goal_prime() {
        let p = fixture("macro 3 s0,P,s1,s2 o0,o1,o2,P 16 2 8 final 1");
        let info = p.comp_info(0);
        assert_eq!(info.binary, 5);
        // 2 gas for each of s1 and s2, not on top
        assert_eq!(p.heuristic(&Stack::from(&p.init), 0, &info), 202);
        let p = fixture("macro 4 s0,s1,s2,s3 O,P,O,O,O 16 3 8 x 1");
        let info = p.comp_info(0);
        assert_eq!(info.binary, 10);
        assert_eq!(p.heuristic(&Stack::from(&p.init), 0, &info), 305);
    }

    #[test]
    fn wildcard_outputs_exclude_fixed_outputs() {
        let p = fixture("macro 3 x0,x1,x2 o0,P,O,O 16 2 8 x 1");
        let stack = |names: &str| names.split(',').map(|n| class(&p, n)).collect::<Vec<_>>();
        assert!(p.is_goal(&stack("o0,P,o1,o2")));
        assert!(!p.is_goal(&stack("o0,P,o0,o1")));
    }

    #[test]
    fn heuristic_is_bounded_by_a_complete_t2_program() {
        let p = fixture("macro 2 s0,P,s1 o0,o1,P 16 1 8 final 1");
        let (cost, path) = search(&p, &mut Ctx::new()).unwrap();
        let mut computed = p.init_computed;
        let mut remaining = cost;
        assert!(p.heuristic(&Stack::from(&p.init), computed, &p.comp_info(computed)) <= remaining);
        for (prim, stack) in path {
            remaining -= match prim {
                Prim::Pop => 2,
                Prim::Dup(_) | Prim::Swap(_) | Prim::PushP | Prim::Push4 => 3,
                _ => Problem::op_cost(prim),
            };
            for &c in &stack {
                if p.classes[c as usize].kind == Kind::Val {
                    computed |= 1 << c;
                }
            }
            assert!(
                p.heuristic(&Stack::from(&stack), computed, &p.comp_info(computed)) <= remaining
            );
        }
    }

    #[test]
    #[should_panic(expected = "initial values must be raw inputs or S-box outputs")]
    fn composite_initial_values_need_computation_history() {
        fixture("macro 3 sum,x0,P,o1,o2,x1,x2 o0,o1,o2 16 2 8 final 1").assert_supported();
    }

    #[test]
    #[should_panic(expected = "goal must require every output exactly once")]
    fn partial_output_goals_are_not_supported() {
        fixture("macro 4 s0,s1,s2,s3 t6 16 3 8 x 1").assert_supported();
    }

    #[test]
    #[should_panic(expected = "goal must require every output exactly once")]
    fn partial_wildcard_goals_are_not_supported() {
        fixture("macro 3 s0,s1,s2 O 16 2 8 x 1").assert_supported();
    }

    #[test]
    fn wildcard_before_a_fixed_output_cannot_reuse_it() {
        let p = fixture("macro 3 x0,x1,x2 O,o0,O 16 2 8 x 1");
        p.assert_supported();
        let stack = |names: &str| names.split(',').map(|n| class(&p, n)).collect::<Vec<_>>();
        assert!(p.is_goal(&stack("o1,o0,o2")));
        assert!(!p.is_goal(&stack("o0,o0,o1")));
    }

    #[test]
    fn packed_keys_roundtrip() {
        assert_eq!(std::mem::size_of::<Node>(), 24);
        for len in 0..=MAXD {
            let values: Vec<u8> = (0..len).map(|i| (i * 17 % 31) as u8).collect();
            for computed in [0, 1, u32::MAX] {
                let (lo, hi) = key(&values, computed);
                let (stack, mask) = decode(lo, hi);
                assert_eq!(stack.as_slice(), values);
                assert_eq!(mask, computed);
            }
        }
    }

    #[test]
    fn buckets_release_storage_and_allow_reopening() {
        let mut open = Open {
            buckets: Vec::new(),
            min: 0,
            len: 0,
        };
        open.push(10, 1, 1);
        open.push(10, 2, 2);
        open.push(20, 3, 3);
        assert_eq!(open.pop(), Some((10, 2)));
        assert_eq!(open.pop(), Some((10, 1)));
        assert_eq!(open.pop(), Some((20, 3)));
        assert_eq!(open.buckets[10].levels.capacity(), 0);
        open.push(5, 4, 4);
        assert_eq!(open.pop(), Some((5, 4)));
        assert_eq!(open.pop(), None);
        assert_eq!(open.len, 0);
        assert!(open.buckets.iter().all(|b| b.levels.capacity() == 0));
    }

    #[test]
    fn dead_inputs_do_not_reduce_the_copy_bound() {
        let p = fixture("macro 3 x0,P,x1,x2 o0,o1,o2,P 16 2 8 final 1");
        let info = p.comp_info(p.init_computed);
        let h = p.heuristic(&Stack::from(&p.init), p.init_computed, &info);
        let mut stack = p.init.clone();
        stack.push(class(&p, "s0"));
        assert_eq!(p.heuristic(&Stack::from(&stack), p.init_computed, &info), h);
    }

    #[test]
    fn clean_goal_rejects_trailing_constants() {
        let mut p = fixture("macro 2 x0,x1 o0,o1 16 0 8 x 1");
        let stack = vec![class(&p, "o0"), class(&p, "o1"), p.prime];
        assert!(p.is_goal(&stack));
        p.clean_goal = true;
        assert!(!p.is_goal(&stack));
        assert!(p.is_goal(&stack[..2]));
    }

    #[test]
    fn bucket_prefers_larger_g_then_lifo() {
        let mut bucket = Bucket::default();
        bucket.push(5, 1);
        bucket.push(10, 2);
        bucket.push(5, 3);
        assert_eq!(bucket.pop(), Some(2));
        assert_eq!(bucket.pop(), Some(3));
        assert_eq!(bucket.pop(), Some(1));
        assert_eq!(bucket.pop(), None);
        bucket.push(0, 4);
        assert_eq!(bucket.pop(), Some(4));
        assert_eq!(bucket.pop(), None);
    }

    #[test]
    fn table_rehash_preserves_exact_keys() {
        let mut nodes = Vec::new();
        let mut table = Table::new();
        for i in 0..50_000u64 {
            let lo = i.wrapping_mul(0x9E3779B97F4A7C15);
            let hi = i.rotate_left(29);
            let slot = table.find(&nodes, lo, hi).unwrap_err();
            nodes.push(Node {
                lo,
                hi,
                parent: u32::MAX,
                g: 0,
                f: 0,
            });
            table.insert_at(&nodes, slot, i as u32);
        }
        for (i, node) in nodes.iter().enumerate() {
            assert_eq!(table.find(&nodes, node.lo, node.hi), Ok(i as u32));
        }
    }
}
