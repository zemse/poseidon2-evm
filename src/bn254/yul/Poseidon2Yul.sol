// SPDX-License-Identifier: MIT

pragma solidity >=0.6.0;

import {LibPoseidon2Yul} from "./LibPoseidon2Yul.sol";

/// @notice Poseidon2 hash function optimized in Yul assembly
/// @dev ABI-compatible with IPoseidon2 interface
/// Supports hash_1(uint256), hash_2(uint256,uint256), hash_3(uint256,uint256,uint256)
/// Security: https://github.com/zemse/poseidon2-evm/blob/main/SECURITY.md
contract Poseidon2Yul_BN254 {
    fallback() external {
        uint256 state0;
        uint256 state1;
        uint256 state2;
        uint256 state3;

        assembly {
            // Sponge state - arguments start after 4-byte selector
            state0 := calldataload(0x04)
            state1 := calldataload(0x24)
            state2 := calldataload(0x44)

            // iv = number of arguments << 64
            state3 :=
                shl(
                    64,
                    // Here, number of args = (calldatasize - 4) / 32
                    shr(
                        5,
                        // We ignore the selector and focus on how many abi encoded params available.
                        sub(calldatasize(), 4)
                    )
                )
        }

        uint256 result = LibPoseidon2Yul.poseidon2_core(state0, state1, state2, state3);

        assembly {
            mstore(0, result)
            return(0, 32)
        }
    }
}
