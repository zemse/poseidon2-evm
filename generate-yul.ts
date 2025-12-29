import { round_constant, internal_matrix_diagonal } from "./constants";
// @ts-ignore import fs require type declarations
import { writeFileSync } from "fs";

const rounds_f = 8;
const rounds_p = 56;

writeFileSync("src/bn254/yul/Poseidon2Yul.sol", yul_generate_contract());
writeFileSync("src/bn254/yul/LibPoseidon2Yul.sol", yul_generate_library());
console.log(
  "Generated src/yul/Poseidon2Yul.sol and src/yul/Poseidon2YulLib.sol"
);

function yul_generate_contract() {
  return `
// SPDX-License-Identifier: MIT

pragma solidity >=0.6.0;

/// @notice Poseidon2 hash function optimized in Yul assembly
/// @dev ABI-compatible with IPoseidon2 interface
/// Supports hash_1(uint256), hash_2(uint256,uint256), hash_3(uint256,uint256,uint256)
contract Poseidon2Yul_BN254 {
    ${fallback_codegen()}
}
`;
}

function yul_generate_library() {
  return `
// SPDX-License-Identifier: MIT

pragma solidity >=0.6.0;

/// @notice Poseidon2 hash function library optimized in Yul assembly
/// @dev Internal functions can be inlined without deploying a contract
library LibPoseidon2Yul {
    function hash_1(uint256 x) internal pure returns (uint256) {
        return poseidon2_core(x, 0, 0, 1 << 64);
    }

    function hash_2(uint256 x, uint256 y) internal pure returns (uint256) {
        return poseidon2_core(x, y, 0, 2 << 64);
    }

    function hash_3(uint256 x, uint256 y, uint256 z) internal pure returns (uint256) {
        return poseidon2_core(x, y, z, 3 << 64);
    }

    function poseidon2_core(uint256 s0, uint256 s1, uint256 s2, uint256 s3) internal pure returns (uint256 result) {
        assembly {
            ${poseidon2_core("s0", "s1", "s2", "s3")}
            result := state0
        }
    }
}
`;
}

function fallback_codegen() {
  return `
    fallback() external {
        assembly {
            let PRIME := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001

            // Sponge state - arguments start after 4-byte selector
            let state0 := calldataload(0x04)
            let state1 := calldataload(0x24)
            let state2 := calldataload(0x44)

            // iv = number of arguments << 64
            let state3 :=
                shl(
                    64,
                    // Here, number of args = (calldatasize - 4) / 32
                    shr(
                        5,
                        // We ignore the selector and focus on how many abi encoded params available.
                        sub(calldatasize(), 4)
                    )
                )

            ${poseidon2_rounds()}

            mstore(0, state0)
            return (0, 32)
        }
    }
    `;
}

function poseidon2_core(s0: string, s1: string, s2: string, s3: string) {
  return `
            let PRIME := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001

            let state0 := ${s0}
            let state1 := ${s1}
            let state2 := ${s2}
            let state3 := ${s3}

            ${poseidon2_rounds()}
`;
}

function poseidon2_rounds() {
  return `
            // Apply 1st linear layer
            ${matrix_multiplication_4x4()}

            
            // First set of external rounds
            // 1st for-loop
            ${(() => {
              let code: string[] = [];
              let rf_first = rounds_f / 2;
              for (let r = 0; r < rf_first; r++) {
                code.push(`
                    state0 := add(state0, ${round_constant[r][0]})
                    state1 := add(state1, ${round_constant[r][1]})
                    state2 := add(state2, ${round_constant[r][2]})
                    state3 := add(state3, ${round_constant[r][3]})
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
                    state0 := add(state0, ${round_constant[r][0]})
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
                    state0 := add(state0, ${round_constant[r][0]})
                    state1 := add(state1, ${round_constant[r][1]})
                    state2 := add(state2, ${round_constant[r][2]})
                    state3 := add(state3, ${round_constant[r][3]})
                    ${s_box()}
                    ${matrix_multiplication_4x4()}
                `);
              }
              return code.join("\n");
            })()}
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
            let intr := ${var_name}
            ${var_name} := mulmod(intr, intr, PRIME)
            ${var_name} := mulmod(${var_name}, ${var_name}, PRIME)
            ${var_name} := mulmod(${var_name}, intr, PRIME)
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
            let sum := add(state0, state1)
            sum := add(sum, state2)
            sum := addmod(sum, state3, PRIME)
            state0 := add(mulmod(state0, ${d0}, PRIME), sum)
            state1 := add(mulmod(state1, ${d1}, PRIME), sum)
            state2 := add(mulmod(state2, ${d2}, PRIME), sum)
            state3 := add(mulmod(state3, ${d3}, PRIME), sum)
        }
       `;
}

function matrix_multiplication_4x4() {
  return `
    {
        // matrix_multiplication_4x4
        let t0 := add(state0, state1)
        let t1 := add(state2, state3)
        let t2 := add(state1, state1)
        t2 := add(t2, t1)
        let t3 := add(state3, state3)
        t3 := add(t3, t0)
        let t4 := mulmod(t1, 4, PRIME)
        t4 := add(t4, t3)
        let t5 := mulmod(t0, 4, PRIME)
        t5 := add(t5, t2)
        let t6 := addmod(t3, t5, PRIME)
        let t7 := addmod(t2, t4, PRIME)
        state0 := t6
        state1 := t5
        state2 := t7
        state3 := t4
    }
   `;
}
