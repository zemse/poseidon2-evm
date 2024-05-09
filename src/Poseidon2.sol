// SPDX-License-Identifier: MIT

pragma solidity >=0.8.8;

import {Field} from "./Field.sol";
import {Poseidon2Lib} from "./Poseidon2Lib.sol";

contract Poseidon2 {
    using Field for *;

    function hash_1(Field.Type x) public view returns (Field.Type) {
        return Poseidon2Lib.hash_1(x);
    }

    function hash_2(Field.Type x, Field.Type y) public view returns (Field.Type) {
        return Poseidon2Lib.hash_2(x, y);
    }

    function hash_3(Field.Type x, Field.Type y, Field.Type z) public view returns (Field.Type) {
        return Poseidon2Lib.hash_3(x, y, z);
    }

    function hash(Field.Type[] memory input) public view returns (Field.Type) {
        return Poseidon2Lib.hash(input, input.length, false);
    }

    function hash(Field.Type[] memory input, uint256 std_input_length, bool is_variable_length)
        public
        view
        returns (Field.Type)
    {
        return Poseidon2Lib.hash(input, std_input_length, is_variable_length);
    }
}
