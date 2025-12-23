// SPDX-License-Identifier: MIT

pragma solidity >=0.5.0;

/// @title IPoseidon2
/// @notice Interface for Poseidon2 hashing of 1, 2, or 3 field elements
/// @dev This interface works with Solidity, Yul and Huff implementations
///     of Poseidon2 in this repository.
interface IPoseidon2 {
    function hash_1(uint256 x) external pure returns (uint256);
    function hash_2(uint256 x, uint256 y) external pure returns (uint256);
    function hash_3(uint256 x, uint256 y, uint256 z) external pure returns (uint256);
}
