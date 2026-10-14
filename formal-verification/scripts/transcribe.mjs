// Transcribes the TaceoLabs Poseidon2 BN254 parameter files into Lean constant
// tables and cross-checks them against gnark-crypto and TaceoLabs noir-poseidon.
// Usage: node transcribe.mjs <outDir>
import fs from "node:fs";

const P = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001n;
const out = process.argv[2];
const norm = (h) => BigInt(h.startsWith("0x") ? h : "0x" + h);
const hex = (v) => "0x" + v.toString(16).padStart(64, "0");

const TACEO_COMMIT = "be49d09364089e3d81670d9574da0c286beb400b";
const LA_COMMIT = "2d5ff3589b497ede496dc1bc9acc259dd3397d50";
const sources = {
  2: { file: "taceo_t2.rs", url: `https://github.com/TaceoLabs/co-snarks/blob/${TACEO_COMMIT}/mpc-core/src/gadgets/poseidon2/poseidon2_bn254_t2.rs` },
  3: { file: "taceo_t3.rs", url: `https://github.com/TaceoLabs/co-snarks/blob/${TACEO_COMMIT}/mpc-core/src/gadgets/poseidon2/poseidon2_bn254_t3.rs` },
  4: { file: "taceo_t4.rs", url: `https://github.com/TaceoLabs/co-snarks/blob/${TACEO_COMMIT}/mpc-core/src/gadgets/poseidon2/poseidon2_bn254_t4.rs` },
  8: { file: "taceo_t8.rs", url: `https://github.com/TaceoLabs/co-snarks/blob/${TACEO_COMMIT}/mpc-core/src/gadgets/poseidon2/poseidon2_bn254_t8.rs` },
  12: { file: "la_t12.rs", url: `https://github.com/LeastAuthority/TaceoLabs-nullifier-oracle-service/blob/${LA_COMMIT}/poseidon2/src/params/bn254_t12.rs` },
  16: { file: "taceo_t16.rs", url: `https://github.com/TaceoLabs/co-snarks/blob/${TACEO_COMMIT}/mpc-core/src/gadgets/poseidon2/poseidon2_bn254_t16.rs` },
};

function section(src, start, end) {
  const a = src.indexOf(start);
  const b = end ? src.indexOf(end, a) : src.length;
  if (a < 0 || b < 0) throw new Error(`missing ${start}`);
  return [...src.slice(a, b).matchAll(/field_from_hex_string\(\s*"([^"]+)"/g)].map((m) => norm(m[1]));
}

function parseTaceo(t, src) {
  const num = (name) => Number(src.match(new RegExp(`const ${name}: usize = (\\d+);`))[1]);
  const rf = num("ROUNDS_F"), rp = num("ROUNDS_P");
  if (num("T") !== t) throw new Error("T mismatch");
  const diag = section(src, "static MAT_DIAG_M_1", "static EXTERNAL_RC");
  const ext = section(src, "static EXTERNAL_RC", "static INTERNAL_RC");
  const int = section(src, "static INTERNAL_RC", "Poseidon2Params<Scalar");
  if (diag.length !== t || ext.length !== rf * t || int.length !== rp) throw new Error(`t=${t} sizes ${diag.length} ${ext.length} ${int.length}`);
  for (const v of [...diag, ...ext, ...int]) if (v >= P) throw new Error("value >= P");
  const rows = [];
  for (let r = 0; r < rf; r++) rows.push(ext.slice(r * t, (r + 1) * t));
  return { rf, rp, diag, rows, int };
}

// Round-ordered flat sequence: first half full rows, partial constants, second half full rows.
const flat = (c) => [...c.rows.slice(0, c.rf / 2).flat(), ...c.int, ...c.rows.slice(c.rf / 2).flat()];

function gnark(t) {
  const src = fs.readFileSync("gnark_constants.go", "utf8");
  const a = src.indexOf(`\t${t}: {`);
  if (a < 0) return null;
  const b = src.indexOf("\n\t},", a);
  const body = src.slice(a, b);
  const vals = [...body.matchAll(/mustElement\("([^"]+)"\)/g)].map((m) => norm(m[1]));
  // sage layout: every round a row of t, partial rounds padded with t - 1 zeros
  const rows = [];
  for (let i = t; i < vals.length; i += t) rows.push(vals.slice(i, i + t));
  const rf = 8, rp = rows.length - rf;
  const seq = [];
  rows.forEach((r, i) => {
    if (i >= rf / 2 && i < rf / 2 + rp) {
      if (r.slice(1).some((v) => v !== 0n)) throw new Error("gnark partial row not padded");
      seq.push(r[0]);
    } else seq.push(...r);
  });
  return { diag: vals.slice(0, t), seq };
}

function noir(t) {
  const src = fs.readFileSync("noir_consts.nr", "utf8");
  const a = src.indexOf(`fn x5_${t}_config()`);
  const b = src.indexOf("\n}\n", a);
  const seq = [...src.slice(a, b).matchAll(/0x[0-9a-fA-F]+/g)].map((m) => norm(m[0]));
  let diag = null;
  const d = src.indexOf(`internal_diag${t}:`);
  if (d >= 0) diag = [...src.slice(d, src.indexOf("];", d)).matchAll(/0x[0-9a-fA-F]+/g)].map((m) => norm(m[0]));
  return { seq, diag };
}

const eq = (a, b) => a.length === b.length && a.every((v, i) => v === b[i]);

function lean(t, c, src) {
  const g = gnark(t), n = noir(t);
  const checks = [];
  if (g) {
    if (!eq(g.seq, flat(c)) || !eq(g.diag, c.diag)) throw new Error(`t=${t} gnark mismatch`);
    checks.push("gnark-crypto (round constants and diagonal)");
  }
  if (!eq(n.seq, flat(c))) throw new Error(`t=${t} noir mismatch`);
  if (n.diag && !eq(n.diag, c.diag)) throw new Error(`t=${t} noir diag mismatch`);
  checks.push(n.diag ? "TaceoLabs noir-poseidon (round constants and diagonal)" : "TaceoLabs noir-poseidon (round constants)");
  const rowsTxt = c.rows.map((r) => "    [" + r.map(hex).join(",\n     ") + "]").join(",\n");
  return `import Poseidon2.Spec.Permutation

/-!
# Poseidon2 BN254 constants, t = ${t}

Transcribed value for value from
${src.url}
(\`MAT_DIAG_M_1\`, \`EXTERNAL_RC\`, \`INTERNAL_RC\`, \`ROUNDS_F = ${c.rf}\`, \`ROUNDS_P = ${c.rp}\`).
That file states the parameters follow the HorizenLabs \`poseidon2_rust_params.sage\` script.
\`EXTERNAL_RC\` holds the ${c.rf} full rounds in order (the first ${c.rf / 2} run before the partial
rounds), \`INTERNAL_RC\` one constant per partial round.

Cross-checked at transcription (same values, same round order) against
${checks.join(" and ")}:
https://github.com/Consensys-Incorporated/gnark-crypto/blob/a3a3ae54638a1201fa818d7d722ee57b1e1631f2/ecc/bn254/fr/poseidon2/poseidon2_constants.go
https://github.com/TaceoLabs/noir-poseidon/blob/ecb23c8476baba7ab7a16800ca25dd60e4832895/poseidon2/src/bn254/consts.nr
${g ? "" : "(gnark-crypto has no t = " + t + " table.)\n"}-/

namespace Poseidon2.Spec.Constants.T${t}

/-- \`MAT_DIAG_M_1\`: the internal matrix is \`1 + diag(diagM1)\`. -/
def diagM1 : List Nat :=
  [${c.diag.map(hex).join(",\n   ")}]

/-- \`EXTERNAL_RC\`: one row of ${t} per full round. -/
def rcExternal : List (List Nat) :=
  [
${rowsTxt}]

/-- \`INTERNAL_RC\`: one constant per partial round, added to state element 0. -/
def rcInternal : List Nat :=
  [${c.int.map(hex).join(",\n   ")}]

def params : Params where
  t := ${t}
  roundsF := ${c.rf}
  roundsP := ${c.rp}
  rcExternal := rcExternal
  rcInternal := rcInternal
  diagM1 := diagM1

theorem params_wellFormed : params.WellFormed = true := by decide +kernel

theorem params_canonical : params.Canonical = true := by decide +kernel

end Poseidon2.Spec.Constants.T${t}
`;
}

for (const [t, s] of Object.entries(sources)) {
  const src = fs.readFileSync(s.file, "utf8");
  const c = parseTaceo(Number(t), src);
  fs.writeFileSync(`${out}/T${t}.lean`, lean(Number(t), c, s));
  console.log(`t=${t} rf=${c.rf} rp=${c.rp} ok`);
}
