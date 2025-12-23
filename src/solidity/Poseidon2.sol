// SPDX-License-Identifier: MIT

pragma solidity >=0.8.8;

import {Field} from "./Field.sol";
import {LibPoseidon2} from "./LibPoseidon2.sol";

contract Poseidon2 {
    using Field for *;

    function hash_1(Field.Type x) public pure returns (Field.Type) {
        return LibPoseidon2.hash_1(x);
    }

    function hash_2(Field.Type x, Field.Type y) public pure returns (Field.Type) {
        return LibPoseidon2.hash_2(x, y);
    }

    function hash_3(Field.Type x, Field.Type y, Field.Type z) public pure returns (Field.Type) {
        return LibPoseidon2.hash_3(x, y, z);
    }

    function hash(Field.Type[] memory input) public pure returns (Field.Type) {
        return LibPoseidon2.hash(input, input.length, false);
    }

    function hash(Field.Type[] memory input, uint256 std_input_length, bool is_variable_length)
        public
        pure
        returns (Field.Type)
    {
        return LibPoseidon2.hash(input, std_input_length, is_variable_length);
    }
}
