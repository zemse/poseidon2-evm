import { round_constant, internal_matrix_diagonal } from "./constants";

console.log(yul_generate());

function yul_generate() {
  let t = 4;
  let rounds_f = 8;
  let rounds_p = 56;
  let RATE = 3;

  return `
  // SPDX-License-Identifier: MIT

    pragma solidity >=0.8.8;
    
    contract Poseidon2Yul {
        ${hash_codegen()}
    }
    `;

  function hash_codegen() {
    return `
    fallback() external {
        assembly {
            let PRIME := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001

            // Sponge state
            let state0 := 0
            let state1 := 0
            let state2 := 0
            let state3 := shl(64, shr(5, calldatasize())) // iv


            //
            // Absorb
            //
            state0 := addmod(state0, calldataload(0), PRIME)
            state1 := addmod(state1, calldataload(0x20), PRIME)
            state2 := addmod(state2, calldataload(0x40), PRIME)

            //
            // Squeeze
            //

            // Apply 1st linear layer
            ${matrix_multiplication_4x4()}

            
            // First set of external rounds
            // 1st for-loop
            ${(() => {
              let code: string[] = [];
              let rf_first = rounds_f / 2;
              for (let r = 0; r < rf_first; r++) {
                code.push(`
                    state0 := addmod(state0, ${round_constant[r][0]}, PRIME)
                    state1 := addmod(state1, ${round_constant[r][1]}, PRIME)
                    state2 := addmod(state2, ${round_constant[r][2]}, PRIME)
                    state3 := addmod(state3, ${round_constant[r][3]}, PRIME)
                    ${s_box()}
                    ${matrix_multiplication_4x4()}
                `);
              }
              return code.join("\n");
            })()}

            // Internal rounds
            // 2nd for-loop
            
            ${(() => {
              let code: string[] = [];
              let rf_first = rounds_f / 2;
              let p_end = rf_first + rounds_p;
              for (let r = rf_first; r < p_end; r++) {
                code.push(`
                    state0 := addmod(state0, ${round_constant[r][0]}, PRIME)
                    ${single_box("state0")}

                ${internal_m_multiplication(
                  internal_matrix_diagonal[0],
                  internal_matrix_diagonal[1],
                  internal_matrix_diagonal[2],
                  internal_matrix_diagonal[3]
                )}

                    `);
              }
              return code.join("\n");
            })()}

            // Remaining external rounds
            // 3rd for-loop
            
            ${(() => {
              let code: string[] = [];
              let rf_first = rounds_f / 2;
              let p_end = rf_first + rounds_p;
              let num_rounds = rounds_f + rounds_p;
              for (let r = p_end; r < num_rounds; r++) {
                code.push(`
                    state0 := addmod(state0, ${round_constant[r][0]}, PRIME)
                    state1 := addmod(state1, ${round_constant[r][1]}, PRIME)
                    state2 := addmod(state2, ${round_constant[r][2]}, PRIME)
                    state3 := addmod(state3, ${round_constant[r][3]}, PRIME)
                    ${s_box()}
                    ${matrix_multiplication_4x4()}
                `);
              }
              return code.join("\n");
            })()}

            mstore(0, state0)
            return (0, 32)

        }
    }
    `;
  }

  function s_box() {
    return `
        // full s_box
        ${single_box("state0")}
        ${single_box("state1")}
        ${single_box("state2")}
        ${single_box("state3")}
       `;
  }

  function single_box(var_name: string) {
    return `
        {
            // single_box
            let in := ${var_name}
            ${var_name} := mulmod(in, in, PRIME)
            ${var_name} := mulmod(${var_name}, ${var_name}, PRIME)
            ${var_name} := mulmod(${var_name}, in, PRIME)
        }
        `;
  }

  function internal_m_multiplication(
    d0: string,
    d1: string,
    d2: string,
    d3: string
  ): string {
    return `
        {
            // internal_m_multiplication
            let sum := addmod(state0, state1, PRIME)
            sum := addmod(sum, state2, PRIME)
            sum := addmod(sum, state3, PRIME)
            state0 := addmod(mulmod(state0, ${d0}, PRIME), sum, PRIME)
            state1 := addmod(mulmod(state1, ${d1}, PRIME), sum, PRIME)
            state2 := addmod(mulmod(state2, ${d2}, PRIME), sum, PRIME)
            state3 := addmod(mulmod(state3, ${d3}, PRIME), sum, PRIME)
        }
       `;
  }

  function matrix_multiplication_4x4() {
    return `
    {
        // matrix_multiplication_4x4
        let t0 := addmod(state0, state1, PRIME)
        let t1 := addmod(state2, state3, PRIME)
        let t2 := addmod(state1, state1, PRIME)
        t2 := addmod(t2, t1, PRIME)
        let t3 := addmod(state3, state3, PRIME)
        t3 := addmod(t3, t0, PRIME)
        let t4 := addmod(t1, t1, PRIME)
        t4 := addmod(t4, t4, PRIME)
        t4 := addmod(t4, t3, PRIME)
        let t5 := addmod(t0, t0, PRIME)
        t5 := addmod(t5, t5, PRIME)
        t5 := addmod(t5, t2, PRIME)
        let t6 := addmod(t3, t5, PRIME)
        let t7 := addmod(t2, t4, PRIME)
        state0 := t6
        state1 := t5
        state2 := t7
        state3 := t4
    }
   `;
  }
}
