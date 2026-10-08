// Reference Poseidon2 permutation on BigInt, following the HorizenLabs
// reference implementation (matmul_m4 / matmul_external / matmul_internal).

import { add, mul, mod } from "./field.ts";
import type { Params } from "../params/params.ts";

function sbox(x: bigint): bigint {
  const x2 = mul(x, x);
  const x4 = mul(x2, x2);
  return mul(x4, x);
}

function matmulM4(state: bigint[]): void {
  for (let s = 0; s < state.length; s += 4) {
    const t0 = add(state[s], state[s + 1]);
    const t1 = add(state[s + 2], state[s + 3]);
    const t2 = add(add(state[s + 1], state[s + 1]), t1);
    const t3 = add(add(state[s + 3], state[s + 3]), t0);
    const t4 = add(mul(4n, t1), t3);
    const t5 = add(mul(4n, t0), t2);
    const t6 = add(t3, t5);
    const t7 = add(t2, t4);
    state[s] = t6;
    state[s + 1] = t5;
    state[s + 2] = t7;
    state[s + 3] = t4;
  }
}

export function matmulExternal(state: bigint[]): void {
  const t = state.length;
  if (t === 2 || t === 3) {
    let sum = 0n;
    for (const x of state) sum = add(sum, x);
    for (let i = 0; i < t; i++) state[i] = add(state[i], sum);
    return;
  }
  matmulM4(state);
  if (t === 4) return;
  const stored = [0n, 0n, 0n, 0n];
  for (let l = 0; l < 4; l++) {
    for (let j = 0; j < t / 4; j++)
      stored[l] = add(stored[l], state[4 * j + l]);
  }
  for (let i = 0; i < t; i++) state[i] = add(state[i], stored[i % 4]);
}

export function matmulInternal(state: bigint[], diagMinusOne: bigint[]): void {
  const t = state.length;
  let sum = 0n;
  for (const x of state) sum = add(sum, x);
  if (t === 2) {
    state[0] = add(state[0], sum);
    state[1] = add(add(state[1], state[1]), sum);
    return;
  }
  if (t === 3) {
    state[0] = add(state[0], sum);
    state[1] = add(state[1], sum);
    state[2] = add(add(state[2], state[2]), sum);
    return;
  }
  for (let i = 0; i < t; i++) {
    state[i] = add(mul(state[i], diagMinusOne[i]), sum);
  }
}

export function permutation(params: Params, input: bigint[]): bigint[] {
  const steps = 1 + params.roundsF + params.roundsP;
  return permutationSteps(params, input, 0, steps);
}

// Steps [from, to) of the permutation: step 0 is the initial linear layer,
// step r + 1 is round r. The Huff generator checks each part of a split
// permutation against this.
export function permutationSteps(
  params: Params,
  input: bigint[],
  from: number,
  to: number,
): bigint[] {
  const { t, roundsF, roundsP, roundConstants, internalDiagMinusOne } = params;
  if (input.length !== t) throw new Error(`expected ${t} inputs`);
  const state = input.map(mod);
  const rfHalf = roundsF / 2;
  const pEnd = rfHalf + roundsP;

  for (let step = from; step < to; step++) {
    if (step === 0) {
      matmulExternal(state);
      continue;
    }
    const r = step - 1;
    if (r >= rfHalf && r < pEnd) {
      state[0] = sbox(add(state[0], roundConstants[r][0]));
      matmulInternal(state, internalDiagMinusOne);
    } else {
      for (let i = 0; i < t; i++)
        state[i] = sbox(add(state[i], roundConstants[r][i]));
      matmulExternal(state);
    }
  }

  return state;
}

// Sponge used by the deployed t = 4 contract: state [x0, x1, x2, n << 64],
// output is state[0] after one permutation.
export function hashSponge(params: Params, inputs: bigint[]): bigint {
  const rate = params.t - 1;
  if (inputs.length > rate)
    throw new Error("too many inputs for one permutation");
  const state = new Array(params.t).fill(0n);
  for (let i = 0; i < inputs.length; i++) state[i] = mod(inputs[i]);
  state[params.t - 1] = BigInt(inputs.length) << 64n;
  return permutation(params, state)[0];
}
