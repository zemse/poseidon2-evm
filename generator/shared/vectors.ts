// Test inputs shared by both generators: the externally confirmed
// [0, 1, ..., t-1], all zeros, all p - 1, descending from p - 1 and four
// pseudo-random states. They drive the symbolic simulation and the vectors in
// the generated Foundry tests.

import { PRIME, mod } from "../params/field.ts";

// deterministic 256-bit values from a splitmix64 stream
export function prng(seed: bigint): () => bigint {
  let s = seed;
  const next64 = () => {
    s = (s + 0x9e3779b97f4a7c15n) & 0xffffffffffffffffn;
    let z = s;
    z = ((z ^ (z >> 30n)) * 0xbf58476d1ce4e5b9n) & 0xffffffffffffffffn;
    z = ((z ^ (z >> 27n)) * 0x94d049bb133111ebn) & 0xffffffffffffffffn;
    return z ^ (z >> 31n);
  };
  return () =>
    mod((next64() << 192n) | (next64() << 128n) | (next64() << 64n) | next64());
}

export function testInputs(t: number): bigint[][] {
  const rand = prng(BigInt(t));
  const inputs = [
    Array.from({ length: t }, (_, i) => BigInt(i)),
    new Array(t).fill(0n),
    new Array(t).fill(PRIME - 1n),
    Array.from({ length: t }, (_, i) => PRIME - 1n - BigInt(i)),
  ];
  for (let k = 0; k < 4; k++) inputs.push(Array.from({ length: t }, rand));
  return inputs;
}
