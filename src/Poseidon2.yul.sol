// SPDX-License-Identifier: MIT

pragma solidity >=0.8.8;

contract Poseidon2Yul {
    fallback() external {
        assembly {
            let num_words := shr(5, calldatasize())

            let iv := shl(64, num_words)


            // let state0 := 0
            // let state1 := 0
            // let state2 := iv
            // let state3 := 0


            function absorb(
                state0, 
                state1, 
                state2, 
                state3, 
                cache_size, 
                cache0, 
                cache1, 
                cache2, 
                squeeze_mode,
                input
            ) {
            }
        }
    }
}