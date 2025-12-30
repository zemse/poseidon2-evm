// SPDX-License-Identifier: MIT
pragma solidity >=0.8.8;

import {IPoseidon2} from "../IPoseidon2.sol";

/// @title Poseidon2 (BN254)
/// @notice Helper library for calling deployed Poseidon2 contracts on BN254 curve
/// @dev Default functions call Yul contract. Use `_huff` suffix for Huff contract.
///      Checked functions validate inputs. Use `_unchecked` when inputs are known valid.
library Poseidon2 {
    /// @notice BN254 scalar field prime
    uint256 internal constant PRIME = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001;

    /// @notice Deployed Yul contract address (same on all networks)
    address internal constant YUL = address(0); // TBD

    /// @notice Deployed Huff contract address (same on all networks)
    address internal constant HUFF = address(0); // TBD

    error ContractNotDeployed(address target);
    error InvalidFieldElement(uint256 value);

    // ============================================================
    // Default (Yul Contract)
    // ============================================================

    function hash_1(uint256 x) internal view returns (uint256) {
        _checkDeployed(YUL);
        _checkField(x);
        return IPoseidon2(YUL).hash_1(x);
    }

    function hash_1_unchecked(uint256 x) internal pure returns (uint256) {
        return IPoseidon2(YUL).hash_1(x);
    }

    function hash_2(uint256 x, uint256 y) internal view returns (uint256) {
        _checkDeployed(YUL);
        _checkField(x);
        _checkField(y);
        return IPoseidon2(YUL).hash_2(x, y);
    }

    function hash_2_unchecked(uint256 x, uint256 y) internal pure returns (uint256) {
        return IPoseidon2(YUL).hash_2(x, y);
    }

    function hash_3(uint256 x, uint256 y, uint256 z) internal view returns (uint256) {
        _checkDeployed(YUL);
        _checkField(x);
        _checkField(y);
        _checkField(z);
        return IPoseidon2(YUL).hash_3(x, y, z);
    }

    function hash_3_unchecked(uint256 x, uint256 y, uint256 z) internal pure returns (uint256) {
        return IPoseidon2(YUL).hash_3(x, y, z);
    }

    // ============================================================
    // Huff Contract (Lowest Gas, Unchecked)
    // ============================================================

    function hash_1_huff_unchecked(uint256 x) internal pure returns (uint256) {
        return IPoseidon2(HUFF).hash_1(x);
    }

    function hash_2_huff_unchecked(uint256 x, uint256 y) internal pure returns (uint256) {
        return IPoseidon2(HUFF).hash_2(x, y);
    }

    function hash_3_huff_unchecked(uint256 x, uint256 y, uint256 z) internal pure returns (uint256) {
        return IPoseidon2(HUFF).hash_3(x, y, z);
    }

    // ============================================================
    // Internal Helpers
    // ============================================================

    function _checkDeployed(address target) private view {
        if (target.code.length == 0) {
            revert ContractNotDeployed(target);
        }
    }

    function _checkField(uint256 value) private pure {
        if (value >= PRIME) {
            revert InvalidFieldElement(value);
        }
    }
}
