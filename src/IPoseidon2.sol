// SPDX-License-Identifier: MIT

pragma solidity >=0.5.0;

/// @title IPoseidon2
/// @notice Interface for Poseidon2 hash function implementations
/// @dev This interface is curve-agnostic. The specific curve (BN254, Goldilocks, etc.)
///      is determined by the implementing contract. All inputs must be valid field
///      elements for the respective curve's scalar field.
interface IPoseidon2 {
    /// @notice Hash a single field element
    /// @param x The input field element (must be < curve's PRIME)
    /// @return The Poseidon2 hash output as a field element
    function hash_1(uint256 x) external pure returns (uint256);

    /// @notice Hash two field elements
    /// @param x The first input field element (must be < curve's PRIME)
    /// @param y The second input field element (must be < curve's PRIME)
    /// @return The Poseidon2 hash output as a field element
    function hash_2(uint256 x, uint256 y) external pure returns (uint256);

    /// @notice Hash three field elements
    /// @param x The first input field element (must be < curve's PRIME)
    /// @param y The second input field element (must be < curve's PRIME)
    /// @param z The third input field element (must be < curve's PRIME)
    /// @return The Poseidon2 hash output as a field element
    function hash_3(uint256 x, uint256 y, uint256 z) external pure returns (uint256);
}
