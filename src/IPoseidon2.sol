// SPDX-License-Identifier: MIT

pragma solidity >=0.5.0;

interface IPoseidon2 {
    function hash_1(uint256 x) external pure returns (uint256);
    function hash_2(uint256 x, uint256 y) external pure returns (uint256);
    function hash_3(uint256 x, uint256 y, uint256 z) external pure returns (uint256);
    function hash(uint256[] memory input) external pure returns (uint256);
    function hash(uint256[] memory input, uint256 std_input_length, bool is_variable_length)
        external
        pure
        returns (uint256);
}
