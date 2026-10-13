// Extracts the permutation test vectors of TaceoLabs noir-poseidon
// (poseidon2/src/bn254/permutation.nr) as JSON: [{t, input, output}].
import fs from "node:fs";
const src = fs.readFileSync("noir_perm.nr", "utf8");
const num = (s) => BigInt(s.trim());
const out = [];
for (const m of src.matchAll(/t(\d+)\(\s*\[([^\]]*)\]\s*\)\s*==\s*\[([^\]]*)\]/g)) {
  const t = Number(m[1]);
  const input = m[2].split(",").map((s) => s.trim()).filter(Boolean).map(num);
  const output = m[3].split(",").map((s) => s.trim()).filter(Boolean).map(num);
  if (input.length !== t || output.length !== t) throw new Error(`bad vector t=${t}`);
  // line number of the match, for the permalink
  const line = src.slice(0, m.index).split("\n").length;
  out.push({ t, line, input: input.map(String), output: output.map(String) });
}
fs.writeFileSync("noir_vectors.json", JSON.stringify(out));
const counts = {};
for (const v of out) counts[v.t] = (counts[v.t] || 0) + 1;
console.log(counts);
