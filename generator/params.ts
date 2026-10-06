// Poseidon2 parameter derivation for BN254, ported from the HorizenLabs
// reference script poseidon2_rust_params.sage (FIELD = 1, SBOX = 0, n = 254).
// Everything the script computes with Python floats is computed with doubles
// here so that the round-number search makes exactly the same choices.

import { PRIME, add, mul, inv, mod } from "./field.ts";

const FIELD = 1;
const SBOX = 0;
const FIELD_SIZE = PRIME.toString(2).length; // 254
const SECURITY_LEVEL = 128;

export type Params = {
  t: number;
  alpha: number;
  roundsF: number;
  roundsP: number;
  // roundConstants[round][i], internal rounds carry t - 1 trailing zeros
  roundConstants: bigint[][];
  // diag(M_internal) - 1, the form the permutation multiplies by
  internalDiagMinusOne: bigint[];
};

export function gcd(a: bigint, b: bigint): bigint {
  while (b !== 0n) [a, b] = [b, a % b];
  return a;
}

export function getAlpha(): number {
  for (let alpha = 3; ; alpha++) {
    if (gcd(BigInt(alpha), PRIME - 1n) === 1n) return alpha;
  }
}

// ---------------------------------------------------------------------------
// Round numbers (poseidon_calc_final_numbers_fixed / find_FD_round_numbers)
// ---------------------------------------------------------------------------

function binomial(n: number, k: number): bigint {
  if (k < 0 || k > n) return 0n;
  let r = 1n;
  for (let i = 1; i <= k; i++) {
    r = (r * BigInt(n - k + i)) / BigInt(i);
  }
  return r;
}

function log2Big(x: bigint): number {
  if (x <= 0n) return -Infinity;
  const bits = x.toString(2).length;
  if (bits <= 53) return Math.log2(Number(x));
  const top = Number(x >> BigInt(bits - 53));
  return Math.log2(top) + (bits - 53);
}

// Lanczos approximation of ln(gamma(x)), accurate to ~1e-13 relative
function lgamma(x: number): number {
  const g = 7;
  const c = [
    0.99999999999980993, 676.5203681218851, -1259.1392167224028,
    771.32342877765313, -176.61502916214059, 12.507343278686905,
    -0.13857109526572012, 9.9843695780195716e-6, 1.5056327351493116e-7,
  ];
  x -= 1;
  let a = c[0];
  const t = x + g + 0.5;
  for (let i = 1; i < g + 2; i++) a += c[i] / (x + i);
  return (
    0.5 * Math.log(2 * Math.PI) + (x + 0.5) * Math.log(t) - t + Math.log(a)
  );
}

// log2(binomial(n, k)). The float estimate decides unless it lands within
// 0.01 bits of the threshold the caller tests (2^63.5), in which case the
// exact BigInt value is used so float error can never flip the decision.
function log2Binomial(n: number, k: number): number {
  if (k < 0 || k > n) return -Infinity;
  const est = (lgamma(n + 1) - lgamma(k + 1) - lgamma(n - k + 1)) / Math.LN2;
  if (Math.abs(est - 63.5) < 0.01) return log2Big(binomial(n, k));
  return est;
}

function log(x: number, base: number): number {
  return Math.log(x) / Math.log(base);
}

function satInequivAlpha(
  t: number,
  R_F: number,
  R_P: number,
  alpha: number,
  M: number,
): boolean {
  const log2p = log(Number(PRIME), 2);
  const R_F_1 = M <= Math.floor(log2p - (alpha - 1) / 2.0) * (t + 1) ? 6 : 10;
  const R_F_2 =
    1 +
    Math.ceil(log(2, alpha) * Math.min(M, FIELD_SIZE)) +
    Math.ceil(log(t, alpha)) -
    R_P;
  const R_F_3 = log(2, alpha) * Math.min(M, log2p) - R_P;
  const R_F_4 = t - 1 + log(2, alpha) * Math.min(M / (t + 1), log2p / 2) - R_P;
  const R_F_5 = (t - 2 + M / (2 * log(alpha, 2)) - R_P) / (t - 1);
  const R_F_max = Math.max(
    Math.ceil(R_F_1),
    Math.ceil(R_F_2),
    Math.ceil(R_F_3),
    Math.ceil(R_F_4),
    Math.ceil(R_F_5),
  );

  // Addition due to https://eprint.iacr.org/2023/537.pdf
  const r_temp = Math.floor(t / 3.0);
  const over =
    (R_F - 1) * t + R_P + r_temp + r_temp * (R_F / 2.0) + R_P + alpha;
  const under = r_temp * (R_F / 2.0) + R_P + alpha;
  let binom_log = log2Binomial(over, under);
  if (binom_log === Infinity) binom_log = M + 1;
  const cost_gb4 = Math.ceil(2 * binom_log);

  return R_F >= R_F_max && cost_gb4 >= M;
}

export function calcRoundNumbers(
  t: number,
  alpha: number,
  M = SECURITY_LEVEL,
  securityMargin = true,
): { roundsF: number; roundsP: number } {
  let R_P = 0;
  let R_F = 0;
  let min_cost = Infinity;
  let max_cost_rf = 0;
  for (let R_P_outer = 1; R_P_outer < 500; R_P_outer++) {
    // The sage script rebinds the loop variable inside the inner loop, so
    // later R_F candidates of the same outer iteration see the inflated value.
    let R_P_t = R_P_outer;
    for (let R_F_loop = 4; R_F_loop < 100; R_F_loop++) {
      let R_F_t = R_F_loop;
      if (R_F_t % 2 !== 0) continue;
      if (satInequivAlpha(t, R_F_t, R_P_t, alpha, M)) {
        if (securityMargin) {
          R_F_t += 2;
          R_P_t = Math.ceil(R_P_t * 1.075);
        }
        const cost = t * R_F_t + R_P_t;
        if (cost < min_cost || (cost === min_cost && R_F_t < max_cost_rf)) {
          R_P = R_P_t;
          R_F = R_F_t;
          min_cost = cost;
          max_cost_rf = R_F;
        }
      }
    }
  }
  return { roundsF: R_F, roundsP: R_P };
}

// ---------------------------------------------------------------------------
// Grain LFSR
// ---------------------------------------------------------------------------

export class Grain {
  private state: number[];

  constructor(t: number, roundsF: number, roundsP: number) {
    const bits = (value: number, width: number) =>
      value
        .toString(2)
        .padStart(width, "0")
        .split("")
        .map((c) => Number(c));
    this.state = [
      ...bits(FIELD, 2),
      ...bits(SBOX, 4),
      ...bits(FIELD_SIZE, 12),
      ...bits(t, 12),
      ...bits(roundsF, 10),
      ...bits(roundsP, 10),
      ...new Array(30).fill(1),
    ];
    if (this.state.length !== 80) throw new Error("bad grain init");
    for (let i = 0; i < 160; i++) this.step();
  }

  private step(): number {
    const s = this.state;
    const bit = s[62] ^ s[51] ^ s[38] ^ s[23] ^ s[13] ^ s[0];
    s.shift();
    s.push(bit);
    return bit;
  }

  // Self-shrinking output, same control flow as the sage generator.
  nextBit(): number {
    let bit = this.step();
    while (bit === 0) {
      this.step();
      bit = this.step();
    }
    return this.step();
  }

  nextBits(count: number): bigint {
    let value = 0n;
    for (let i = 0; i < count; i++) {
      value = (value << 1n) | BigInt(this.nextBit());
    }
    return value;
  }
}

export function generateRoundConstants(
  grain: Grain,
  t: number,
  roundsF: number,
  roundsP: number,
): bigint[][] {
  const num = roundsF * t + roundsP;
  const flat: bigint[] = [];
  const pStart = (roundsF / 2) * t;
  for (let i = 0; i < num; i++) {
    let value = grain.nextBits(FIELD_SIZE);
    while (value >= PRIME) value = grain.nextBits(FIELD_SIZE);
    flat.push(value);
    if (i >= pStart && i < pStart + roundsP) {
      for (let j = 0; j < t - 1; j++) flat.push(0n);
    }
  }
  const rounds: bigint[][] = [];
  for (let i = 0; i < flat.length; i += t) rounds.push(flat.slice(i, i + t));
  if (rounds.length !== roundsF + roundsP) throw new Error("bad rc count");
  return rounds;
}

// ---------------------------------------------------------------------------
// Matrices
// ---------------------------------------------------------------------------

export const M4: bigint[][] = [
  [5n, 7n, 1n, 3n],
  [4n, 6n, 1n, 1n],
  [1n, 3n, 5n, 7n],
  [1n, 1n, 4n, 6n],
];

export function externalMatrix(t: number): bigint[][] {
  if (t === 2)
    return [
      [2n, 1n],
      [1n, 2n],
    ];
  if (t === 3)
    return [
      [2n, 1n, 1n],
      [1n, 2n, 1n],
      [1n, 1n, 2n],
    ];
  if (t === 4) return M4;
  if (t % 4 === 0) {
    const M: bigint[][] = [];
    for (let i = 0; i < t; i++) {
      const row: bigint[] = [];
      for (let j = 0; j < t; j++) {
        const same = Math.floor(i / 4) === Math.floor(j / 4);
        row.push(M4[i % 4][j % 4] * (same ? 2n : 1n));
      }
      M.push(row);
    }
    return M;
  }
  throw new Error(`no external matrix for t = ${t} (need 2, 3 or 4k)`);
}

function matMul(A: bigint[][], B: bigint[][]): bigint[][] {
  const n = A.length;
  const C: bigint[][] = [];
  for (let i = 0; i < n; i++) {
    const row: bigint[] = [];
    for (let j = 0; j < n; j++) {
      let s = 0n;
      for (let k = 0; k < n; k++) s += A[i][k] * B[k][j];
      row.push(mod(s));
    }
    C.push(row);
  }
  return C;
}

function identity(n: number): bigint[][] {
  return Array.from({ length: n }, (_, i) =>
    Array.from({ length: n }, (_, j) => (i === j ? 1n : 0n)),
  );
}

function trace(A: bigint[][]): bigint {
  let s = 0n;
  for (let i = 0; i < A.length; i++) s += A[i][i];
  return mod(s);
}

// Characteristic polynomial via Faddeev-LeVerrier, coefficients low to high,
// monic of degree n. Valid because p > n so every k <= n is invertible.
export function charpoly(A: bigint[][]): bigint[] {
  const n = A.length;
  const c: bigint[] = new Array(n + 1).fill(0n);
  c[n] = 1n;
  // AM holds A * M_{k-1}, with M_0 = 0
  let AM = identity(n).map((row) => row.map(() => 0n));
  for (let k = 1; k <= n; k++) {
    // M_k = A * M_{k-1} + c_{n-k+1} I
    const Mk = AM.map((row, i) =>
      row.map((v, j) => (i === j ? add(v, c[n - k + 1]) : v)),
    );
    AM = matMul(A, Mk);
    c[n - k] = mod(-mul(trace(AM), inv(BigInt(k))));
  }
  return c;
}

// Polynomials over F_p, coefficients low to high, trailing zeros trimmed.
type Poly = bigint[];

function trim(p: Poly): Poly {
  let n = p.length;
  while (n > 0 && p[n - 1] === 0n) n--;
  return p.slice(0, n);
}

function polyMod(a: Poly, f: Poly): Poly {
  // f monic
  const r = a.slice();
  const df = f.length - 1;
  for (let i = r.length - 1; i >= df; i--) {
    const coef = r[i];
    if (coef === 0n) continue;
    for (let j = 0; j <= df; j++) {
      r[i - df + j] = mod(r[i - df + j] - coef * f[j]);
    }
  }
  return trim(r.slice(0, df));
}

function polyMulMod(a: Poly, b: Poly, f: Poly): Poly {
  if (a.length === 0 || b.length === 0) return [];
  const out: bigint[] = new Array(a.length + b.length - 1).fill(0n);
  for (let i = 0; i < a.length; i++) {
    if (a[i] === 0n) continue;
    for (let j = 0; j < b.length; j++) {
      out[i + j] = (out[i + j] + a[i] * b[j]) % PRIME;
    }
  }
  return polyMod(out, f);
}

function polySub(a: Poly, b: Poly): Poly {
  const n = Math.max(a.length, b.length);
  const out: bigint[] = [];
  for (let i = 0; i < n; i++) out.push(mod((a[i] ?? 0n) - (b[i] ?? 0n)));
  return trim(out);
}

function polyGcd(a: Poly, b: Poly): Poly {
  a = trim(a);
  b = trim(b);
  while (b.length > 0) {
    // reduce a mod b with b made monic
    const lead = inv(b[b.length - 1]);
    const bm = b.map((v) => mul(v, lead));
    const r = polyMod(a, bm);
    a = bm;
    b = r;
  }
  return a;
}

// g(h) mod f by Horner
function polyCompose(g: Poly, h: Poly, f: Poly): Poly {
  let acc: Poly = [];
  for (let i = g.length - 1; i >= 0; i--) {
    acc = polyMulMod(acc, h, f);
    if (g[i] !== 0n) {
      acc = acc.slice();
      acc[0] = mod((acc[0] ?? 0n) + g[i]);
      acc = trim(acc.length ? acc : [g[i]]);
    }
  }
  return acc;
}

function primeFactors(n: number): number[] {
  const out: number[] = [];
  for (let q = 2; q * q <= n; q++) {
    if (n % q === 0) {
      out.push(q);
      while (n % q === 0) n /= q;
    }
  }
  if (n > 1) out.push(n);
  return out;
}

// Rabin's test: monic f of degree n is irreducible over F_p iff
// x^(p^n) = x mod f and gcd(x^(p^(n/q)) - x, f) = 1 for every prime q | n.
export function isIrreducible(f: Poly): boolean {
  const n = f.length - 1;
  if (n < 1) return false;
  if (n === 1) return true;
  const x: Poly = [0n, 1n];
  // h1 = x^p mod f by square and multiply
  let h1: Poly = [1n];
  const bits = PRIME.toString(2);
  for (const bit of bits) {
    h1 = polyMulMod(h1, h1, f);
    if (bit === "1") h1 = polyMulMod(h1, x, f);
  }
  // hk = x^(p^k) mod f via Frobenius composition
  const h: Poly[] = [x, h1];
  for (let k = 2; k <= n; k++) h.push(polyCompose(h[k - 1], h1, f));
  if (polySub(h[n], x).length !== 0) return false;
  for (const q of primeFactors(n)) {
    const g = polyGcd(f, polySub(h[n / q], x));
    if (g.length !== 1) return false;
  }
  return true;
}

// check_minpoly_condition: for i in 1..2t, minpoly(M^i) has degree t and is
// irreducible. Both together are equivalent to charpoly(M^i) irreducible.
export function checkMinpolyCondition(M: bigint[][]): boolean {
  const t = M.length;
  let Mi = M;
  for (let i = 1; i <= 2 * t; i++) {
    if (!isIrreducible(charpoly(Mi))) return false;
    Mi = matMul(M, Mi);
  }
  return true;
}

export function generateInternalDiagMinusOne(
  grain: Grain,
  t: number,
): bigint[] {
  if (t === 2) return [1n, 2n];
  if (t === 3) return [1n, 1n, 2n];
  const draw = () =>
    Array.from({ length: t }, () => mod(grain.nextBits(FIELD_SIZE)));
  let diag = draw();
  let attempts = 1;
  const build = (d: bigint[]) =>
    Array.from({ length: t }, (_, i) =>
      Array.from({ length: t }, (_, j) => (i === j ? d[i] : 1n)),
    );
  while (!checkMinpolyCondition(build(diag))) {
    diag = draw();
    attempts++;
  }
  if (process.env.POSEIDON2_VERBOSE) {
    console.error(`internal diag accepted after ${attempts} attempt(s)`);
  }
  return diag.map((d) => mod(d - 1n));
}

export function generateParams(t: number): Params {
  if (!(t === 2 || t === 3 || (t % 4 === 0 && t >= 4))) {
    throw new Error(`unsupported t = ${t}: Poseidon2 defines t = 2, 3 or 4k`);
  }
  const alpha = getAlpha();
  const { roundsF, roundsP } = calcRoundNumbers(t, alpha);
  const grain = new Grain(t, roundsF, roundsP);
  const roundConstants = generateRoundConstants(grain, t, roundsF, roundsP);
  const internalDiagMinusOne = generateInternalDiagMinusOne(grain, t);
  return { t, alpha, roundsF, roundsP, roundConstants, internalDiagMinusOne };
}
