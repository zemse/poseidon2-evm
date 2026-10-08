// Poseidon2 parameter derivation for BN254, ported from the HorizenLabs
// reference script poseidon2_rust_params.sage (FIELD = 1, SBOX = 0, n = 254)
// by way of round-constants/round-constants.ts. Everything the script
// computes with Python floats is computed with f64 in the same operation
// order, so the round-number search makes exactly the same choices.

use std::collections::HashMap;
use std::sync::{Arc, Mutex, OnceLock};

use rayon::prelude::*;

use crate::field::{self, PRIME, U256, U512, add, inv, mul, neg, reduce, sub, u256};

const FIELD: u64 = 1;
const SBOX: u64 = 0;
const FIELD_SIZE: usize = 254;
const SECURITY_LEVEL: f64 = 128.0;

#[derive(Debug, Clone)]
pub struct Params {
    pub t: usize,
    pub alpha: u64,
    pub rounds_f: usize,
    pub rounds_p: usize,
    /// round_constants[round][i], internal rounds carry t - 1 trailing zeros
    pub round_constants: Vec<Vec<U256>>,
    /// diag(M_internal) - 1, the form the permutation multiplies by
    pub internal_diag_minus_one: Vec<U256>,
}

pub fn get_alpha() -> u64 {
    let p1 = PRIME - u256(1);
    (3u64..)
        .find(|&alpha| p1.gcd(u256(alpha)) == u256(1))
        .expect("an alpha exists")
}

// ---------------------------------------------------------------------------
// Round numbers (poseidon_calc_final_numbers_fixed / find_FD_round_numbers)
// ---------------------------------------------------------------------------

fn binomial(n: u64, k: u64) -> u128 {
    if k > n {
        return 0;
    }
    let mut r: u128 = 1;
    for i in 1..=k {
        r = r
            .checked_mul(u128::from(n - k + i))
            .expect("binomial near 2^63.5 fits u128")
            / u128::from(i);
    }
    r
}

fn log2_big(x: u128) -> f64 {
    if x == 0 {
        return f64::NEG_INFINITY;
    }
    let bits = 128 - x.leading_zeros();
    if bits <= 53 {
        return (x as f64).log2();
    }
    let top = (x >> (bits - 53)) as f64;
    top.log2() + f64::from(bits - 53)
}

/// Lanczos approximation of ln(gamma(x)), accurate to ~1e-13 relative
fn lgamma(x: f64) -> f64 {
    let g = 7.0;
    #[allow(clippy::excessive_precision)]
    let c = [
        0.99999999999980993,
        676.5203681218851,
        -1259.1392167224028,
        771.32342877765313,
        -176.61502916214059,
        12.507343278686905,
        -0.13857109526572012,
        9.9843695780195716e-6,
        1.5056327351493116e-7,
    ];
    let x = x - 1.0;
    let mut a = c[0];
    let t = x + g + 0.5;
    for (i, ci) in c.iter().enumerate().take(9).skip(1) {
        a += ci / (x + i as f64);
    }
    0.5 * (2.0 * std::f64::consts::PI).ln() + (x + 0.5) * t.ln() - t + a.ln()
}

/// log2(binomial(n, k)). The float estimate decides unless it lands within
/// 0.01 bits of the threshold the caller tests (2^63.5), in which case the
/// exact value is used so float error can never flip the decision.
fn log2_binomial(n: f64, k: f64) -> f64 {
    if k < 0.0 || k > n {
        return f64::NEG_INFINITY;
    }
    let est = (lgamma(n + 1.0) - lgamma(k + 1.0) - lgamma(n - k + 1.0)) / std::f64::consts::LN_2;
    if (est - 63.5).abs() < 0.01 {
        return log2_big(binomial(n as u64, k as u64));
    }
    est
}

fn log(x: f64, base: f64) -> f64 {
    x.ln() / base.ln()
}

fn sat_inequiv_alpha(t: f64, r_f: f64, r_p: f64, alpha: f64, m: f64) -> bool {
    let field_size = FIELD_SIZE as f64;
    let log2p = log(field::to_f64(PRIME), 2.0);
    let r_f_1 = if m <= (log2p - (alpha - 1.0) / 2.0).floor() * (t + 1.0) {
        6.0
    } else {
        10.0
    };
    let r_f_2 = 1.0 + (log(2.0, alpha) * m.min(field_size)).ceil() + log(t, alpha).ceil() - r_p;
    let r_f_3 = log(2.0, alpha) * m.min(log2p) - r_p;
    let r_f_4 = t - 1.0 + log(2.0, alpha) * (m / (t + 1.0)).min(log2p / 2.0) - r_p;
    let r_f_5 = (t - 2.0 + m / (2.0 * log(alpha, 2.0)) - r_p) / (t - 1.0);
    let r_f_max = [r_f_1, r_f_2, r_f_3, r_f_4, r_f_5]
        .iter()
        .map(|x| x.ceil())
        .fold(f64::NEG_INFINITY, f64::max);

    // Addition due to https://eprint.iacr.org/2023/537.pdf
    let r_temp = (t / 3.0).floor();
    let over = (r_f - 1.0) * t + r_p + r_temp + r_temp * (r_f / 2.0) + r_p + alpha;
    let under = r_temp * (r_f / 2.0) + r_p + alpha;
    let mut binom_log = log2_binomial(over, under);
    if binom_log == f64::INFINITY {
        binom_log = m + 1.0;
    }
    let cost_gb4 = (2.0 * binom_log).ceil();

    r_f >= r_f_max && cost_gb4 >= m
}

pub fn calc_round_numbers(t: usize, alpha: u64) -> (usize, usize) {
    calc_round_numbers_with(t, alpha, SECURITY_LEVEL, true)
}

fn calc_round_numbers_with(t: usize, alpha: u64, m: f64, security_margin: bool) -> (usize, usize) {
    let t = t as f64;
    let alpha = alpha as f64;
    let mut r_p = 0.0;
    let mut r_f = 0.0;
    let mut min_cost = f64::INFINITY;
    let mut max_cost_rf = 0.0;
    for r_p_outer in 1..500 {
        // The sage script rebinds the loop variable inside the inner loop, so
        // later R_F candidates of the same outer iteration see the inflated
        // value.
        let mut r_p_t = f64::from(r_p_outer);
        for r_f_loop in 4..100 {
            let mut r_f_t = f64::from(r_f_loop);
            if r_f_loop % 2 != 0 {
                continue;
            }
            if sat_inequiv_alpha(t, r_f_t, r_p_t, alpha, m) {
                if security_margin {
                    r_f_t += 2.0;
                    r_p_t = (r_p_t * 1.075).ceil();
                }
                let cost = t * r_f_t + r_p_t;
                if cost < min_cost || (cost == min_cost && r_f_t < max_cost_rf) {
                    r_p = r_p_t;
                    r_f = r_f_t;
                    min_cost = cost;
                    max_cost_rf = r_f;
                }
            }
        }
    }
    (r_f as usize, r_p as usize)
}

// ---------------------------------------------------------------------------
// Grain LFSR
// ---------------------------------------------------------------------------

pub struct Grain {
    // 80 bits, state[0] first
    state: std::collections::VecDeque<u8>,
}

impl Grain {
    pub fn new(t: usize, rounds_f: usize, rounds_p: usize) -> Grain {
        let mut state = std::collections::VecDeque::with_capacity(81);
        let mut bits = |value: u64, width: u32| {
            for k in (0..width).rev() {
                state.push_back(((value >> k) & 1) as u8);
            }
        };
        bits(FIELD, 2);
        bits(SBOX, 4);
        bits(FIELD_SIZE as u64, 12);
        bits(t as u64, 12);
        bits(rounds_f as u64, 10);
        bits(rounds_p as u64, 10);
        state.extend(std::iter::repeat_n(1, 30));
        assert_eq!(state.len(), 80, "bad grain init");
        let mut grain = Grain { state };
        for _ in 0..160 {
            grain.step();
        }
        grain
    }

    fn step(&mut self) -> u8 {
        let s = &self.state;
        let bit = s[62] ^ s[51] ^ s[38] ^ s[23] ^ s[13] ^ s[0];
        self.state.pop_front();
        self.state.push_back(bit);
        bit
    }

    /// Self-shrinking output, same control flow as the sage generator.
    pub fn next_bit(&mut self) -> u8 {
        let mut bit = self.step();
        while bit == 0 {
            self.step();
            bit = self.step();
        }
        self.step()
    }

    pub fn next_bits(&mut self, count: usize) -> U256 {
        let mut value = U256::ZERO;
        for _ in 0..count {
            value = (value << 1) | U256::from(self.next_bit());
        }
        value
    }
}

pub fn generate_round_constants(
    grain: &mut Grain,
    t: usize,
    rounds_f: usize,
    rounds_p: usize,
) -> Vec<Vec<U256>> {
    let num = rounds_f * t + rounds_p;
    let mut flat = Vec::new();
    let p_start = (rounds_f / 2) * t;
    for i in 0..num {
        let mut value = grain.next_bits(FIELD_SIZE);
        while value >= PRIME {
            value = grain.next_bits(FIELD_SIZE);
        }
        flat.push(value);
        if i >= p_start && i < p_start + rounds_p {
            flat.extend(std::iter::repeat_n(U256::ZERO, t - 1));
        }
    }
    let rounds: Vec<Vec<U256>> = flat.chunks(t).map(|c| c.to_vec()).collect();
    assert_eq!(rounds.len(), rounds_f + rounds_p, "bad rc count");
    rounds
}

// ---------------------------------------------------------------------------
// Matrices
// ---------------------------------------------------------------------------

type Matrix = Vec<Vec<U256>>;

fn mat_mul(a: &Matrix, b: &Matrix) -> Matrix {
    let n = a.len();
    let p = U512::from(PRIME);
    (0..n)
        .map(|i| {
            (0..n)
                .map(|j| {
                    let mut s = U512::ZERO;
                    for k in 0..n {
                        s += a[i][k].widening_mul::<256, 4, 512, 8>(b[k][j]);
                    }
                    U256::from(s.reduce_mod(p))
                })
                .collect()
        })
        .collect()
}

fn zero_matrix(n: usize) -> Matrix {
    vec![vec![U256::ZERO; n]; n]
}

fn trace(a: &Matrix) -> U256 {
    (0..a.len()).fold(U256::ZERO, |s, i| add(s, a[i][i]))
}

/// Characteristic polynomial via Faddeev-LeVerrier, coefficients low to
/// high, monic of degree n. Valid because p > n so every k <= n is
/// invertible.
pub fn charpoly(a: &Matrix) -> Vec<U256> {
    let n = a.len();
    let mut c = vec![U256::ZERO; n + 1];
    c[n] = u256(1);
    // am holds A * M_{k-1}, with M_0 = 0
    let mut am = zero_matrix(n);
    for k in 1..=n {
        // M_k = A * M_{k-1} + c_{n-k+1} I
        let mut mk = am;
        for (i, row) in mk.iter_mut().enumerate() {
            row[i] = add(row[i], c[n - k + 1]);
        }
        am = mat_mul(a, &mk);
        c[n - k] = neg(mul(trace(&am), inv(u256(k as u64))));
    }
    c
}

// Polynomials over F_p, coefficients low to high, trailing zeros trimmed.
type Poly = Vec<U256>;

fn trim(mut p: Poly) -> Poly {
    while p.last().is_some_and(|c| c.is_zero()) {
        p.pop();
    }
    p
}

fn poly_mod(a: &[U256], f: &[U256]) -> Poly {
    // f monic
    let mut r = a.to_vec();
    let df = f.len() - 1;
    if r.len() > df {
        for i in (df..r.len()).rev() {
            let coef = r[i];
            if coef.is_zero() {
                continue;
            }
            for j in 0..=df {
                r[i - df + j] = sub(r[i - df + j], mul(coef, f[j]));
            }
        }
    }
    r.truncate(df);
    trim(r)
}

/// acc += x for a product x < p^2, reducing acc first when the sum would
/// not fit
fn add_wide(acc: &mut U512, x: U512) {
    *acc = match acc.checked_add(x) {
        Some(sum) => sum,
        None => acc.reduce_mod(U512::from(PRIME)) + x,
    };
}

fn reduce_wide(x: U512) -> U256 {
    U256::from(x.reduce_mod(U512::from(PRIME)))
}

fn wide_mul(a: U256, b: U256) -> U512 {
    a.widening_mul::<256, 4, 512, 8>(b)
}

/// A monic modulus f of degree n with x^n .. x^(2n - 2) reduced mod f, so
/// that the product of two reduced polynomials is reduced with one modular
/// reduction per coefficient. The remainder is unique, so this equals the
/// TS long division.
struct Modulus<'a> {
    f: &'a [U256],
    n: usize,
    /// table[k] = x^(n + k) mod f, n coefficients
    table: Vec<Vec<U256>>,
}

impl<'a> Modulus<'a> {
    fn new(f: &'a [U256]) -> Modulus<'a> {
        let n = f.len() - 1;
        let mut table: Vec<Vec<U256>> = Vec::with_capacity(n);
        let mut power = vec![U256::ZERO; n + 1];
        power[n] = u256(1);
        for _ in 0..n.saturating_sub(1) {
            let mut reduced = poly_mod(&power, f);
            reduced.resize(n, U256::ZERO);
            // x times it, for the next power
            power = std::iter::once(U256::ZERO)
                .chain(reduced.iter().copied())
                .collect();
            table.push(reduced);
        }
        Modulus { f, n, table }
    }

    fn mul(&self, a: &[U256], b: &[U256]) -> Poly {
        if a.is_empty() || b.is_empty() {
            return Vec::new();
        }
        let len = a.len() + b.len() - 1;
        let n = self.n;
        if len > 2 * n - 1 {
            return poly_mul_mod(a, b, self.f);
        }
        let mut acc = vec![U512::ZERO; len];
        for (i, ai) in a.iter().enumerate() {
            if ai.is_zero() {
                continue;
            }
            for (j, bj) in b.iter().enumerate() {
                add_wide(&mut acc[i + j], wide_mul(*ai, *bj));
            }
        }
        if len <= n {
            return trim(acc.into_iter().map(reduce_wide).collect());
        }
        let high: Vec<U256> = acc[n..].iter().map(|c| reduce_wide(*c)).collect();
        let mut out: Vec<U512> = acc[..n]
            .iter()
            .map(|c| U512::from(reduce_wide(*c)))
            .collect();
        for (k, ck) in high.iter().enumerate() {
            if ck.is_zero() {
                continue;
            }
            for (o, tj) in out.iter_mut().zip(&self.table[k]) {
                add_wide(o, wide_mul(*ck, *tj));
            }
        }
        trim(out.into_iter().map(reduce_wide).collect())
    }
}

fn poly_mul_mod(a: &[U256], b: &[U256], f: &[U256]) -> Poly {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut out = vec![U256::ZERO; a.len() + b.len() - 1];
    for (i, ai) in a.iter().enumerate() {
        if ai.is_zero() {
            continue;
        }
        for (j, bj) in b.iter().enumerate() {
            out[i + j] = add(out[i + j], mul(*ai, *bj));
        }
    }
    poly_mod(&out, f)
}

fn poly_sub(a: &[U256], b: &[U256]) -> Poly {
    let n = a.len().max(b.len());
    let at = |p: &[U256], i: usize| p.get(i).copied().unwrap_or(U256::ZERO);
    trim((0..n).map(|i| sub(at(a, i), at(b, i))).collect())
}

fn poly_gcd(a: &[U256], b: &[U256]) -> Poly {
    let mut a = trim(a.to_vec());
    let mut b = trim(b.to_vec());
    while let Some(&last) = b.last() {
        // reduce a mod b with b made monic
        let lead = inv(last);
        let bm: Poly = b.iter().map(|v| mul(*v, lead)).collect();
        let r = poly_mod(&a, &bm);
        a = bm;
        b = r;
    }
    a
}

/// g(h) mod f by Horner
fn poly_compose(g: &[U256], h: &[U256], f: &Modulus) -> Poly {
    let mut acc: Poly = Vec::new();
    for gi in g.iter().rev() {
        acc = f.mul(&acc, h);
        if !gi.is_zero() {
            if acc.is_empty() {
                acc = trim(vec![*gi]);
            } else {
                acc[0] = add(acc[0], *gi);
                acc = trim(acc);
            }
        }
    }
    acc
}

fn prime_factors(mut n: usize) -> Vec<usize> {
    let mut out = Vec::new();
    let mut q = 2;
    while q * q <= n {
        if n.is_multiple_of(q) {
            out.push(q);
            while n.is_multiple_of(q) {
                n /= q;
            }
        }
        q += 1;
    }
    if n > 1 {
        out.push(n);
    }
    out
}

/// Rabin's test: monic f of degree n is irreducible over F_p iff
/// x^(p^n) = x mod f and gcd(x^(p^(n/q)) - x, f) = 1 for every prime q | n.
pub fn is_irreducible(f: &[U256]) -> bool {
    if f.len() < 2 {
        return false;
    }
    let n = f.len() - 1;
    if n == 1 {
        return true;
    }
    let modulus = Modulus::new(f);
    let x: Poly = vec![U256::ZERO, u256(1)];
    // h1 = x^p mod f by square and multiply
    let mut h1: Poly = vec![u256(1)];
    for k in (0..PRIME.bit_len()).rev() {
        h1 = modulus.mul(&h1, &h1);
        if PRIME.bit(k) {
            h1 = modulus.mul(&h1, &x);
        }
    }
    // hk = x^(p^k) mod f via Frobenius composition
    let mut h: Vec<Poly> = vec![x.clone(), h1.clone()];
    for k in 2..=n {
        let next = poly_compose(&h[k - 1], &h1, &modulus);
        h.push(next);
    }
    if !poly_sub(&h[n], &x).is_empty() {
        return false;
    }
    for q in prime_factors(n) {
        let g = poly_gcd(f, &poly_sub(&h[n / q], &x));
        if g.len() != 1 {
            return false;
        }
    }
    true
}

/// check_minpoly_condition: for i in 1..2t, minpoly(M^i) has degree t and is
/// irreducible. Both together are equivalent to charpoly(M^i) irreducible.
/// The powers are tested in parallel; the answer is the same as the TS
/// loop that stops at the first failure.
pub fn check_minpoly_condition(m: &Matrix) -> bool {
    let t = m.len();
    let mut powers = vec![m.clone()];
    for _ in 1..2 * t {
        let next = mat_mul(m, powers.last().expect("a power"));
        powers.push(next);
    }
    powers.par_iter().all(|mi| is_irreducible(&charpoly(mi)))
}

pub fn generate_internal_diag_minus_one(grain: &mut Grain, t: usize) -> Vec<U256> {
    if t == 2 {
        return vec![u256(1), u256(2)];
    }
    if t == 3 {
        return vec![u256(1), u256(1), u256(2)];
    }
    let mut draw = || -> Vec<U256> {
        (0..t)
            .map(|_| reduce(grain.next_bits(FIELD_SIZE)))
            .collect()
    };
    let build = |d: &[U256]| -> Matrix {
        (0..t)
            .map(|i| {
                (0..t)
                    .map(|j| if i == j { d[i] } else { u256(1) })
                    .collect()
            })
            .collect()
    };
    let mut diag = draw();
    let mut attempts = 1;
    while !check_minpoly_condition(&build(&diag)) {
        diag = draw();
        attempts += 1;
    }
    if std::env::var_os("POSEIDON2_VERBOSE").is_some() {
        eprintln!("internal diag accepted after {attempts} attempt(s)");
    }
    diag.iter().map(|d| sub(*d, u256(1))).collect()
}

pub fn generate_params_uncached(t: usize) -> Params {
    assert!(
        t == 2 || t == 3 || (t.is_multiple_of(4) && t >= 4),
        "unsupported t = {t}: Poseidon2 defines t = 2, 3 or 4k"
    );
    let alpha = get_alpha();
    let (rounds_f, rounds_p) = calc_round_numbers(t, alpha);
    let mut grain = Grain::new(t, rounds_f, rounds_p);
    let round_constants = generate_round_constants(&mut grain, t, rounds_f, rounds_p);
    let internal_diag_minus_one = generate_internal_diag_minus_one(&mut grain, t);
    Params {
        t,
        alpha,
        rounds_f,
        rounds_p,
        round_constants,
        internal_diag_minus_one,
    }
}

type Cache = Mutex<HashMap<usize, Arc<OnceLock<Arc<Params>>>>>;

/// The parameters of width t, derived once per process.
pub fn generate_params(t: usize) -> Arc<Params> {
    static CACHE: OnceLock<Cache> = OnceLock::new();
    let cell = {
        let mut cache = CACHE
            .get_or_init(Default::default)
            .lock()
            .expect("params cache lock");
        Arc::clone(cache.entry(t).or_default())
    };
    Arc::clone(cell.get_or_init(|| Arc::new(generate_params_uncached(t))))
}
