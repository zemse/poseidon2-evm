import { round_constant, internal_matrix_diagonal } from "./constants";

console.log(huff_generate());

function huff_generate() {
  let t = 4;
  let rounds_f = 8;
  let rounds_p = 56;
  let RATE = 3;

  return hash_codegen();

  function hash_codegen() {
    return `#include "./Utils.huff"

// prepared using huff-generator.ts
#define macro POSEIDON2_PERMUTATION() = {
  // Apply 1st linear layer
  MATRIX_MULTIPLICATION_4X4_DIRTY()

  // First set of external rounds
  // 1st for-loop
  ${(() => {
    let code: string[] = [];
    let rf_first = rounds_f / 2;
    for (let r = 0; r < rf_first; r++) {
      let is_last = r === rf_first - 1;
      code.push(`
  ADD_CONSTANTS_DIRTY(
    ${round_constant[r][0]}, 
    ${round_constant[r][1]}, 
    ${round_constant[r][2]}, 
    ${round_constant[r][3]}
  )
  FULL_S_BOX_DIRTY()
  ${
    is_last
      ? "MATRIX_MULTIPLICATION_4X4_DIRTY_WITH_ADDITIONAL_PRIMES"
      : "MATRIX_MULTIPLICATION_4X4_DIRTY"
  }()
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
      let is_last = r === p_end - 1;
      code.push(`

  ${round_constant[r][0]} addmod
  
  SINGLE_BOX()

  ${
    is_last
      ? "INTERNAL_M_MULTIPLICATION_DIRTY"
      : "INTERNAL_M_MULTIPLICATION_DIRTY_WITH_ADDITIONAL_PRIMES"
  }(
    ${internal_matrix_diagonal[0]},
    ${internal_matrix_diagonal[1]},
    ${internal_matrix_diagonal[2]},
    ${internal_matrix_diagonal[3]}
  )
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
  ADD_CONSTANTS_DIRTY(
    ${round_constant[r][0]}, 
    ${round_constant[r][1]}, 
    ${round_constant[r][2]}, 
    ${round_constant[r][3]}
  )
  FULL_S_BOX_DIRTY()
  MATRIX_MULTIPLICATION_4X4_DIRTY()`);
    }
    return code.join("\n");
  })()}
}
`;
  }
}
