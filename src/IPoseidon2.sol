// SPDX-License-Identifier: MIT

pragma solidity >=0.5.0;

/// @title IPoseidon2
/// @notice Interface for Poseidon2 hash function implementations
/// @dev This interface is curve-agnostic. The specific curve (BN254, Goldilocks, etc.)
///      is determined by the implementing contract. Inputs are reduced mod the curve's
///      scalar field PRIME on-chain, so any uint256 yields a correct, deterministic hash.
interface IPoseidon2 {
    /// @notice Hash a single field element
    /// @param x The input (reduced mod PRIME)
    /// @return The Poseidon2 hash output as a field element
    function hash_1(uint256 x) external pure returns (uint256);

    /// @notice Hash two field elements
    /// @param x The first input (reduced mod PRIME)
    /// @param y The second input (reduced mod PRIME)
    /// @return The Poseidon2 hash output as a field element
    function hash_2(uint256 x, uint256 y) external pure returns (uint256);

    /// @notice Hash three field elements
    /// @param x The first input (reduced mod PRIME)
    /// @param y The second input (reduced mod PRIME)
    /// @param z The third input (reduced mod PRIME)
    /// @return The Poseidon2 hash output as a field element
    function hash_3(uint256 x, uint256 y, uint256 z) external pure returns (uint256);
}
