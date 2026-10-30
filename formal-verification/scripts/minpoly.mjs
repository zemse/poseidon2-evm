// Writes Poseidon2/Spec/MinpolyCheck/T<t>.lean: certificates that the internal diagonal is the
// first Grain draw whose matrix passes check_minpoly_condition of the HorizenLabs script
// (https://github.com/HorizenLabs/poseidon2/blob/bb476b9ca38198cf5092487283c8b8c5d4317c4e/poseidon2_rust_params.sage).
// For every draw before it: a factorization of the characteristic polynomial f of M (so the
// minimal polynomial of M = M^1 is not irreducible of degree t). For the passing draw: f, the
// square-and-multiply checkpoints of x^p mod f, x^(p^d) mod f, Bezout identities for
// gcd(f, x^(p^d) - x) = 1 (d <= t/2), and checkpoints of h^i, h = x^(p^m), m = t/q.
// The kernel checks all of it (Minpoly.lean); nothing here is trusted.
// Usage: node scripts/minpoly.mjs <outDir> [t ...]
import fs from "node:fs";

const P = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001n;
const N = 254;
const out = process.argv[2];
const only = process.argv.slice(3).map(Number);
const md = (a) => ((a % P) + P) % P;
const hex = (v) => "0x" + v.toString(16);
const powmod = (b, e) => { let r = 1n; b = md(b); while (e > 0n) { if (e & 1n) r = (r * b) % P; b = (b * b) % P; e >>= 1n; } return r; };
const inv = (a) => powmod(a, P - 2n);

// Grain LFSR of the script, BN254, alpha 5.
function grain(t, rf, rp) {
  const bitsOf = (v, w) => v.toString(2).padStart(w, "0").split("").map(Number);
  const seq = [...bitsOf(1, 2), ...bitsOf(0, 4), ...bitsOf(N, 12), ...bitsOf(t, 12), ...bitsOf(rf, 10), ...bitsOf(rp, 10), ...Array(30).fill(1)];
  const clk = () => { const b = seq[62] ^ seq[51] ^ seq[38] ^ seq[23] ^ seq[13] ^ seq[0]; seq.shift(); seq.push(b); return b; };
  for (let i = 0; i < 160; i++) clk();
  const next = () => { let b = clk(); while (b === 0) { clk(); b = clk(); } return clk(); };
  return (k) => { let v = 0n; for (let i = 0; i < k; i++) v = 2n * v + BigInt(next()); return v; };
}

// Polynomials: little-endian BigInt arrays, trimmed.
const trim = (a) => { a = a.slice(); while (a.length && a[a.length - 1] === 0n) a.pop(); return a; };
const pmul = (a, b) => { if (!a.length || !b.length) return []; const r = Array(a.length + b.length - 1).fill(0n); for (let i = 0; i < a.length; i++) for (let j = 0; j < b.length; j++) r[i + j] = (r[i + j] + a[i] * b[j]) % P; return trim(r); };
const padd = (a, b) => { const r = []; for (let i = 0; i < Math.max(a.length, b.length); i++) r.push(md((a[i] ?? 0n) + (b[i] ?? 0n))); return trim(r); };
const psub = (a, b) => padd(a, b.map((c) => md(-c)));
function pdivmod(a, b) {
  a = a.slice(); const q = Array(Math.max(a.length - b.length + 1, 0)).fill(0n); const li = inv(b[b.length - 1]);
  for (let i = a.length - b.length; i >= 0; i--) { const c = (a[i + b.length - 1] * li) % P; q[i] = c; for (let j = 0; j < b.length; j++) a[i + j] = md(a[i + j] - c * b[j]); }
  return [trim(q), trim(a)];
}
const pmod = (a, b) => pdivmod(a, b)[1];
const monic = (a) => { const li = inv(a[a.length - 1]); return a.map((c) => (c * li) % P); };
const mulmod = (a, b, f) => pmod(pmul(a, b), f);
function ppow(a, e, f) { let r = [1n]; a = pmod(a, f); while (e > 0n) { if (e & 1n) r = mulmod(r, a, f); a = mulmod(a, a, f); e >>= 1n; } return r; }
function compose(g, h, f) { let r = []; for (let i = g.length - 1; i >= 0; i--) r = pmod(padd(pmul(r, h), [g[i]]), f); return r; }
const deg = (a) => a.length - 1;
// extended gcd: returns [g, u, w] with u a + w b = g (g monic)
function xgcd(a, b) {
  let [r0, r1, s0, s1, t0, t1] = [trim(a), trim(b), [1n], [], [], [1n]];
  while (r1.length) { const [q, r] = pdivmod(r0, r1); [r0, r1] = [r1, r]; [s0, s1] = [s1, psub(s0, pmul(q, s1))]; [t0, t1] = [t1, psub(t0, pmul(q, t1))]; }
  const li = inv(r0[r0.length - 1]);
  return [r0.map((c) => (c * li) % P), s0.map((c) => (c * li) % P), t0.map((c) => (c * li) % P)];
}
const pgcd = (a, b) => xgcd(a, b)[0];
// fixed length t (Lean's reduced form)
const fit = (a, t) => { const r = a.slice(); while (r.length < t) r.push(0n); if (r.length > t) throw new Error("fit"); return r; };

// characteristic polynomial of J + diag(r - 1), monic: prod(x - d_i) - sum_i prod_{j != i}(x - d_j), d = r - 1
function charpoly(r) {
  const d = r.map((v) => md(v - 1n));
  const prodExcept = (skip) => d.reduce((acc, di, i) => (i === skip ? acc : pmul(acc, [md(-di), 1n])), [1n]);
  let f = prodExcept(-1);
  for (let i = 0; i < d.length; i++) f = psub(f, prodExcept(i));
  return f;
}
const frob = (f, d, h1) => { let h = [0n, 1n]; for (let i = 0; i < d; i++) h = compose(h, h1, f); return h; };
// a nontrivial monic factor of f (reducible, degree t), or null if f is irreducible
function factor(f) {
  const t = deg(f);
  const g0 = pgcd(f, (() => { const df = f.slice(1).map((c, i) => (c * BigInt(i + 1)) % P); return trim(df); })());
  if (deg(g0) > 0) return g0;
  const h1 = ppow([0n, 1n], P, f);
  let h = [0n, 1n];
  for (let d = 1; d <= Math.floor(t / 2); d++) {
    h = compose(h, h1, f);
    const g = pgcd(f, psub(h, [0n, 1n]));
    if (deg(g) === 0) continue;
    if (deg(g) < t) return g;
    // all irreducible factors have degree d: split (Cantor-Zassenhaus, deterministic choices)
    const e = (P ** BigInt(d) - 1n) / 2n;
    for (let s = 1n; ; s++) {
      const a = Array.from({ length: t }, (_, i) => md(s * 0x9e3779b97f4a7c15n * BigInt(i + 1) + s * s));
      const gg = pgcd(f, psub(ppow(a, e, f), [1n]));
      if (deg(gg) > 0 && deg(gg) < t) return gg;
    }
  }
  return null;
}

const fmt = (a) => `[${a.map(hex).join(", ")}]`;
const msOf = (t) => { const ps = []; for (let q = 2; q <= t; q++) if (t % q === 0 && ps.every((p) => q % p !== 0)) ps.push(q); return ps.map((q) => t / q); };
const segLen = (t) => (t <= 8 ? 256 : t <= 16 ? 64 : 32);
const wsegOf = (t) => (2 * t <= 8 ? 2 * t : 8);

// The fail certificate of a matrix with row `rowTerm`: f = g · h.
function failBlock(w, t, r, j, rowTerm, what) {
  const f = charpoly(r);
  const g = factor(f);
  if (!g) throw new Error(`t=${t} ${what} irreducible`);
  const [h, rem] = pdivmod(f, g);
  if (rem.length) throw new Error("division");
  w(`/-- ${what}: \`f = g · h\`, \`g\` of degree ${deg(g)}. -/`);
  w(`def g${j} : List Nat := ${fmt(fit(g.slice(0, -1), deg(g)))}\n`);
  w(`def h${j} : List Nat := ${fmt(fit(h.slice(0, -1), deg(h)))}\n`);
  w(`theorem fail${j} : ¬MinpolyCondition ${t} (partialMatrix ${t} ${rowTerm}) :=
  not_minpolyCondition ${t} _ (fOf g${j} h${j}) g${j} h${j} (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
`);
}

// The pass certificate of a matrix with row `rowTerm`, ending in `theorem pass`.
function passBlock(w, t, r, rowTerm, what) {
  const f = charpoly(r);
  if (factor(f)) throw new Error(`t=${t} ${what} reducible`);
  const fl = fit(f.slice(0, -1), t);
  w(`/-- The characteristic polynomial of ${what}, without its leading \`1\`. -/`);
  w(`def fl : List Nat := ${fmt(fl)}\n`);
  w(`theorem mat : matOk ${t} ${rowTerm} fl = true := by decide +kernel\n`);
  // x^P by square and multiply, checkpoints every segLen steps
  const bits = P.toString(2).slice(1).split("").map((c) => c === "1");
  const S = segLen(t);
  const segs = [];
  for (let i = 0; i < bits.length; i += S) segs.push(bits.slice(i, i + S));
  let acc = 1n;
  const states = [fit([0n, 1n], t)];
  for (const sg of segs) { for (const b of sg) acc = 2n * acc + (b ? 1n : 0n); states.push(fit(ppow([0n, 1n], acc, f), t)); }
  if (acc !== P) throw new Error("bits");
  w(`/-- The bits of \`P\` after its leading one, most significant first (${segs.length} ${segs.length === 1 ? "part" : "parts"}). -/`);
  segs.forEach((sg, i) => w(`def bits${i} : List Bool := [${sg.map(String).join(", ")}]\n`));
  w(`def bits : List Bool := ${segs.map((_, i) => `bits${i}`).reduceRight((a, x) => (a ? `${x} ++ (${a})` : x), "")}\n`);
  w(`/-- \`x ^ e mod f\` after each part of the square-and-multiply. -/`);
  states.forEach((s, i) => { if (i > 0) w(`def sq${i} : List Nat := ${fmt(s)}\n`); });
  segs.forEach((_, i) => w(`theorem run${i} : sqRun fl bits${i} ${i === 0 ? `(xL ${t})` : `sq${i}`} = sq${i + 1} := by decide +kernel\n`));
  const runProof = (i) => (i === segs.length - 1 ? `run${i}` : `(sqRun_append_of _ _ _ _ _ _ run${i}\n    ${runProof(i + 1)})`);
  w(`theorem run : sqRun fl bits (xL ${t}) = sq${segs.length} :=\n  ${runProof(0)}\n`);
  // x^(P^d), d = 1 .. t/2
  const D = Math.floor(t / 2);
  const h1 = ppow([0n, 1n], P, f);
  const hs = [h1];
  for (let d = 2; d <= D; d++) hs.push(compose(hs[hs.length - 1], h1, f));
  if (fit(hs[0], t).some((c, i) => c !== states[segs.length][i])) throw new Error("h1");
  w(`/-- \`x ^ (P ^ d) mod f\`, d = 1 .. ${D}. -/`);
  hs.forEach((h, i) => { if (i > 0) w(`def H${i + 1} : List Nat := ${fmt(fit(h, t))}\n`); });
  w(`def hs : List (List Nat) := [sq${segs.length}${hs.slice(1).map((_, i) => `, H${i + 2}`).join("")}]\n`);
  const hName = (d) => (d === 1 ? `sq${segs.length}` : `H${d}`);
  for (let d = 2; d <= D; d++) w(`theorem comp${d} : compMod fl ${hName(d - 1)} ${hName(1)} = ${hName(d)} := by decide +kernel\n`);
  const chainProof = (d) => (d > D ? "rfl" : `(frobChain_cons_of _ _ _ _ _ comp${d}\n    ${chainProof(d + 1)})`);
  w(`theorem frob : frobOk fl bits hs :=
  ⟨by decide +kernel, by decide +kernel, _, _, rfl, run,
    ${chainProof(2)}⟩
`);
  // Bezout: u f + w (h_d - x) = 1
  w(`/-- Bezout identities \`u · f + w · (x ^ (P ^ d) - x) = 1\`, d = 1 .. ${D}. -/`);
  const bez = [];
  for (let d = 1; d <= D; d++) {
    const [g, u, v] = xgcd(f, psub(hs[d - 1], [0n, 1n]));
    if (deg(g) !== 0) throw new Error("gcd");
    bez.push(`(${fmt(u)}, ${fmt(v)})`);
  }
  w(`def bez : List (List Nat × List Nat) :=\n  [${bez.join(",\n   ")}]\n`);
  w(`theorem bezout : bezOk fl hs bez = true := by decide +kernel\n`);
  // degree: for m in ms, h_m^i != x^i for i = 1 .. 2t, checkpoints every wseg
  const ms = msOf(t);
  const W = wsegOf(t);
  w(`/-- The maximal proper divisors of ${t}. -/\ndef ms : List Nat := [${ms.join(", ")}]\n`);
  const nseg = (2 * t) / W;
  if (!Number.isInteger(nseg)) throw new Error("wseg must divide 2t");
  for (const m of ms) {
    const hm = hs[m - 1];
    const ws = [];
    for (let s = 0; s <= nseg; s++) ws.push(fit(ppow(hm, BigInt(1 + s * W), f), t));
    for (let s = 1; s <= nseg; s++) w(`def W${m}_${s} : List Nat := ${fmt(ws[s])}\n`);
    for (let s = 0; s < nseg; s++)
      w(`theorem pw${m}_${s} : powsNe fl ${hName(m)} ${W} ${s === 0 ? hName(m) : `W${m}_${s}`} (mulXs fl ${s * W} (xL ${t})) W${m}_${s + 1} = true := by\n  decide +kernel\n`);
    const pw = (s) => (s === nseg - 1 ? `pw${m}_${s}` : `(powsNe_seg _ _ ${W} ${(nseg - 1 - s) * W} ${s * W} _ _ _ _ pw${m}_${s}\n    ${pw(s + 1)})`);
    w(`theorem pw${m} : powsNe fl ${hName(m)} ${2 * t} ${hName(m)} (xL ${t}) W${m}_${nseg} = true :=\n  ${pw(0)}\n`);
  }
  w(`theorem degs : degOk fl hs ms :=
  ⟨by decide +kernel, by
    intro m hm
    simp only [ms, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with ${ms.map(() => "rfl").join(" | ")}
${ms.map((m) => `    · exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, _, pw${m}⟩`).join("\n")}⟩
`);
  w(`theorem pass : MinpolyCondition ${t} (partialMatrix ${t} ${rowTerm}) :=
  minpolyCondition_of_cert ${t} _ fl bits hs bez ms (by decide +kernel) mat frob bezout degs
`);
  return segs.length;
}

const fOfDef = (t) => `/-- The monic product \`g · h\` without its leading \`1\`. -/
def fOf (g h : List Nat) : List Nat := (mulL (g ++ [1]) (h ++ [1])).take ${t}
`;

const write = (t, L) => { fs.mkdirSync(out, { recursive: true }); fs.writeFileSync(`${out}/T${t}.lean`, L.join("\n")); };

// t = 2, 3: the script's fixed internal matrices, which it does not check.
const FIXED = [[2, [2n, 3n]], [3, [2n, 2n, 3n]]];
for (const [t, r] of FIXED) {
  if (only.length && !only.includes(t)) continue;
  const L = [];
  const w = (s) => L.push(s);
  const passes = !factor(charpoly(r));
  w(`import Poseidon2.Spec.Minpoly
import Poseidon2.Spec.Constants.T${t}

/-!
# The fixed internal matrix for t = ${t} against the script's check

The script does not draw \`M_I\` for t = ${t}: it fixes \`[${r.map((v, a) => `[${r.map((_, b) => (a === b ? v : 1n)).join(", ")}]`).join(", ")}]\` (\`diagM1 = [${r.map((v) => v - 1n).join(", ")}]\`)
and runs no \`check_minpoly_condition\` on it. This file states what that check would say:
${passes ? "the matrix passes it." : "the matrix fails it: its characteristic polynomial has the root 1 (eigenvector\n`(1, -1, 0)`). The check is a sufficient condition against arbitrarily long subspace trails,\nnot a necessary one."}
Certificates written by \`scripts/minpoly.mjs\`, checked by kernel evaluation.
-/

namespace Poseidon2.Spec.MinpolyCheck.T${t}

open Minpoly

/-- \`r\` of the fixed matrix (\`diagM1 + 1\`). -/
def row : List Nat := [${r.join(", ")}]

theorem row_eq : Constants.T${t}.params.diagM1.map (· + 1) = row := by decide +kernel
`);
  if (passes) passBlock(w, t, r, "row", "the matrix");
  else { w(fOfDef(t)); failBlock(w, t, r, 0, "row", "The matrix"); }
  w(`end Poseidon2.Spec.MinpolyCheck.T${t}\n`);
  write(t, L);
  console.log(`t=${t}: fixed matrix ${passes ? "passes" : "fails"}`);
}

const WIDTHS = [[4, 8, 56, 4], [8, 8, 57, 30], [12, 8, 57, 6], [16, 8, 57, 6], [20, 8, 57, 42], [24, 8, 57, 2], [28, 8, 59, 34]];
for (const [t, rf, rp, k] of WIDTHS) {
  if (only.length && !only.includes(t)) continue;
  const rnd = grain(t, rf, rp);
  for (let i = 0; i < rf * t + rp; i++) { let v = rnd(N); while (v >= P) v = rnd(N); }
  const rows = Array.from({ length: k + 1 }, () => Array.from({ length: t }, () => rnd(N) % P));
  const L = [];
  const w = (s) => L.push(s);
  w(`import Poseidon2.Spec.Minpoly
import Poseidon2.Spec.DiagCheck

/-!
# The internal diagonal for t = ${t} is the first draw passing the script's check

Draws 0 .. ${k - 1} fail \`check_minpoly_condition\`: the characteristic polynomial \`f\` of
their matrix \`M\` factors (\`f = g · h\`, both monic of degree at least 1), so the minimal
polynomial of \`M ^ 1\` is not irreducible of degree ${t}. Draw ${k} passes it: \`f\` is
irreducible and \`x ^ i\` (\`1 ≤ i ≤ ${2 * t}\`) lies in no proper subfield of \`GF(P)[x] / f\`.
Certificates written by \`scripts/minpoly.mjs\`, checked by kernel evaluation.
-/

namespace Poseidon2.Spec.MinpolyCheck.T${t}

open Minpoly DiagCheck

/-- Draw \`j\` (\`j ≤ ${k}\`), as \`DiagCheck.drawRow_t${t}\` gives it. -/
abbrev rowOf (j : Nat) : List Nat := ((diagValsT${t}.drop (j * ${t})).take ${t}).map fun vs => vs.1 % P
`);
  w(fOfDef(t));
  for (let j = 0; j < k; j++) failBlock(w, t, rows[j], j, `(rowOf ${j})`, `Draw ${j}`);
  w(`/-! ### Draw ${k} -/\n`);
  const nsegs = passBlock(w, t, rows[k], `(rowOf ${k})`, `draw ${k}'s matrix`);
  w(`/-- Draw ${k} is the first draw whose matrix passes the script's check. -/
theorem firstPass : FirstPass ${t} 8 ${rp} ${k} :=
  ⟨fun j hj => ⟨_, drawRow_t${t} j (by omega), by
    match j, hj with
${Array.from({ length: k }, (_, j) => `    | ${j}, _ => exact fail${j}`).join("\n")}
    | _ + ${k}, h => omega⟩,
   ⟨_, drawRow_t${t} ${k} le_rfl, pass⟩⟩

end Poseidon2.Spec.MinpolyCheck.T${t}
`);
  write(t, L);
  console.log(`t=${t}: ${k} failing draws, draw ${k} passes; ${nsegs} square-and-multiply parts`);
}
