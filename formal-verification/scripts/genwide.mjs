// Writes T20/T24/T28.lean from the repo generator's parameters (params.jsonl, dumped by
// generator-rs round_constants::generate_params_uncached) and checks that the generator
// agrees with the externally transcribed tables for t <= 16.
import fs from "node:fs";
const [jsonl, dir, commit] = process.argv.slice(2);
const P = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001n;
const h = (n) => "0x" + BigInt(n).toString(16).padStart(64, "0");
const leanNums = (file, name) => {
  const s = fs.readFileSync(file, "utf8");
  const a = s.indexOf(`def ${name}`);
  const b = s.indexOf("\n\n", a);
  return [...s.slice(a, b).matchAll(/0x[0-9a-f]{64}/g)].map((m) => BigInt(m[0]));
};
for (const line of fs.readFileSync(jsonl, "utf8").trim().split("\n")) {
  const p = JSON.parse(line);
  const t = p.t, rf = p.rf, rp = p.rp, half = rf / 2;
  const rows = p.rc.map((r) => r.map(BigInt));
  if (rows.length !== rf + rp) throw new Error("rows");
  const ext = [...rows.slice(0, half), ...rows.slice(half + rp)];
  const int = rows.slice(half, half + rp).map((r) => {
    if (r.slice(1).some((v) => v !== 0n)) throw new Error("partial row not padded");
    return r[0];
  });
  const diag = p.diag.map(BigInt);
  for (const v of [...ext.flat(), ...int, ...diag]) if (v >= P) throw new Error(">= P");
  if (t <= 16) {
    const f = `${dir}/T${t}.lean`;
    const ok =
      JSON.stringify(leanNums(f, "rcExternal").map(String)) === JSON.stringify(ext.flat().map(String)) &&
      JSON.stringify(leanNums(f, "rcInternal").map(String)) === JSON.stringify(int.map(String)) &&
      (JSON.stringify(leanNums(f, "diagM1").map(String)) === JSON.stringify(diag.map(String)));
    console.log(`t=${t} generator equals the external table: ${ok}`);
    if (!ok) process.exit(1);
    continue;
  }
  const rowsTxt = ext.map((r) => "    [" + r.map(h).join(",\n     ") + "]").join(",\n");
  fs.writeFileSync(`${dir}/T${t}.lean`, `import Poseidon2.Spec.Permutation

/-!
# Poseidon2 BN254 constants, t = ${t}: NOT externally referenced

No other implementation publishes BN254 Poseidon2 parameters for t = ${t}, so these tables
come from this repository's own generator: \`generator-rs/src/round_constants.rs\`
(\`generate_params_uncached(${t})\`, a port of the HorizenLabs \`poseidon2_rust_params.sage\`
script) at commit ${commit}, dumped and transcribed by a script.
The same generator reproduces the externally referenced tables for t = 2, 3, 4, 8, 12, 16
value for value (checked when this file was written). \`ROUNDS_F = ${rf}\`, \`ROUNDS_P = ${rp}\`.

The round constants are also derived independently: \`GrainCheck.lean\` proves they are the
output of the Grain LFSR generation of the HorizenLabs script (\`Grain.lean\`) for this t, R_F
and R_P. The internal diagonal \`diagM1\` and the round numbers have no independent check;
a claim about t = ${t} is a claim about the permutation with these constants.
-/

namespace Poseidon2.Spec.Constants.T${t}

/-- \`M_I = 1 + diag(diagM1)\` -/
def diagM1 : List Nat :=
  [${diag.map(h).join(",\n   ")}]

/-- One row of ${t} per full round, in round order. -/
def rcExternal : List (List Nat) :=
  [
${rowsTxt}]

/-- One constant per partial round, added to state element 0. -/
def rcInternal : List Nat :=
  [${int.map(h).join(",\n   ")}]

def params : Params where
  t := ${t}
  roundsF := ${rf}
  roundsP := ${rp}
  rcExternal := rcExternal
  rcInternal := rcInternal
  diagM1 := diagM1

theorem params_wellFormed : params.WellFormed = true := by decide +kernel

theorem params_canonical : params.Canonical = true := by decide +kernel

end Poseidon2.Spec.Constants.T${t}
`);
  console.log(`t=${t} rf=${rf} rp=${rp} written`);
}
