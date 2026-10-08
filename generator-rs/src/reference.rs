// Reference Poseidon2 permutation (shared/reference.ts), following the
// HorizenLabs reference implementation (matmul_m4 / matmul_external /
// matmul_internal).

use crate::field::{U256, add, mul, reduce, u256};
use crate::round_constants::Params;

fn sbox(x: U256) -> U256 {
    let x2 = mul(x, x);
    let x4 = mul(x2, x2);
    mul(x4, x)
}

fn matmul_m4(state: &mut [U256]) {
    for s in state.chunks_mut(4) {
        let t0 = add(s[0], s[1]);
        let t1 = add(s[2], s[3]);
        let t2 = add(add(s[1], s[1]), t1);
        let t3 = add(add(s[3], s[3]), t0);
        let t4 = add(mul(u256(4), t1), t3);
        let t5 = add(mul(u256(4), t0), t2);
        let t6 = add(t3, t5);
        let t7 = add(t2, t4);
        s.copy_from_slice(&[t6, t5, t7, t4]);
    }
}

pub fn matmul_external(state: &mut [U256]) {
    let t = state.len();
    if t == 2 || t == 3 {
        let sum = state.iter().fold(U256::ZERO, |s, x| add(s, *x));
        for x in state.iter_mut() {
            *x = add(*x, sum);
        }
        return;
    }
    matmul_m4(state);
    if t == 4 {
        return;
    }
    let mut stored = [U256::ZERO; 4];
    for (l, st) in stored.iter_mut().enumerate() {
        for j in 0..t / 4 {
            *st = add(*st, state[4 * j + l]);
        }
    }
    for (i, x) in state.iter_mut().enumerate() {
        *x = add(*x, stored[i % 4]);
    }
}

pub fn matmul_internal(state: &mut [U256], diag_minus_one: &[U256]) {
    let t = state.len();
    let sum = state.iter().fold(U256::ZERO, |s, x| add(s, *x));
    if t == 2 {
        state[0] = add(state[0], sum);
        state[1] = add(add(state[1], state[1]), sum);
        return;
    }
    if t == 3 {
        state[0] = add(state[0], sum);
        state[1] = add(state[1], sum);
        state[2] = add(add(state[2], state[2]), sum);
        return;
    }
    for (x, d) in state.iter_mut().zip(diag_minus_one) {
        *x = add(mul(*x, *d), sum);
    }
}

pub fn permutation(params: &Params, input: &[U256]) -> Vec<U256> {
    let steps = 1 + params.rounds_f + params.rounds_p;
    permutation_steps(params, input, 0, steps)
}

/// Steps [from, to) of the permutation: step 0 is the initial linear layer,
/// step r + 1 is round r. The Huff generator checks each part of a split
/// permutation against this.
pub fn permutation_steps(params: &Params, input: &[U256], from: usize, to: usize) -> Vec<U256> {
    let t = params.t;
    assert_eq!(input.len(), t, "expected {t} inputs");
    let mut state: Vec<U256> = input.iter().map(|x| reduce(*x)).collect();
    let rf_half = params.rounds_f / 2;
    let p_end = rf_half + params.rounds_p;

    for step in from..to {
        if step == 0 {
            matmul_external(&mut state);
            continue;
        }
        let r = step - 1;
        let rc = &params.round_constants[r];
        if r >= rf_half && r < p_end {
            state[0] = sbox(add(state[0], rc[0]));
            matmul_internal(&mut state, &params.internal_diag_minus_one);
        } else {
            for (x, c) in state.iter_mut().zip(rc) {
                *x = sbox(add(*x, *c));
            }
            matmul_external(&mut state);
        }
    }
    state
}

/// Sponge used by the deployed t = 4 contract: state [x0, x1, x2, n << 64],
/// output is state[0] after one permutation.
pub fn hash_sponge(params: &Params, inputs: &[U256]) -> U256 {
    permutation(params, &sponge_state(params, inputs))[0]
}

/// The state the sponge permutes for n inputs: the inputs reduced, zeros,
/// and n << 64 as the capacity element.
pub fn sponge_state(params: &Params, inputs: &[U256]) -> Vec<U256> {
    let rate = params.t - 1;
    assert!(inputs.len() <= rate, "too many inputs for one permutation");
    let mut state = vec![U256::ZERO; params.t];
    for (s, x) in state.iter_mut().zip(inputs) {
        *s = reduce(*x);
    }
    state[params.t - 1] = u256(inputs.len() as u64) << 64;
    state
}
