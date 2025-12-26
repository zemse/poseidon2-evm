// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.8.8;

library Field {
    type Type is uint256;

    // BN256 scalar field
    uint256 constant PRIME = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001;
    uint256 constant PRIME_DIV_2 = 0x183227397098d014dc2822db40c0ac2e9419f4243cdcb848a1f0fac9f8000000;

    function checkField(Field.Type a) internal pure {
        require(Field.Type.unwrap(a) < PRIME, "Field: input is too large");
    }

    function toFieldUnchecked(uint256 a) internal pure returns (Field.Type b) {
        b = Field.Type.wrap(a);
    }

    function toField(uint256 a) internal pure returns (Field.Type b) {
        b = Field.Type.wrap(a);
        checkField(b);
    }

    function toFieldUnchecked(bytes32 a) internal pure returns (Field.Type b) {
        assembly {
            b := a
        }
    }

    function toField(bytes32 a) internal pure returns (Field.Type b) {
        assembly {
            b := a
        }
        checkField(b);
    }

    function toBytes32(Field.Type a) internal pure returns (bytes32 b) {
        assembly {
            b := a
        }
    }

    function toUint256(Field.Type a) internal pure returns (uint256 b) {
        assembly {
            b := a
        }
    }

    function toAddress(Field.Type a) internal pure returns (address b) {
        require(Field.Type.unwrap(a) < (1 << 160), "Field: input is too large");
        assembly {
            b := a
        }
    }

    function toArr(Field.Type a) internal pure returns (bytes32[] memory b) {
        b = new bytes32[](1);
        b[0] = toBytes32(a);
    }

    function toField(address a) internal pure returns (Field.Type b) {
        assembly {
            b := a
        }
    }

    function toField(int256 a) internal pure returns (Field.Type) {
        // return Field.Type.wrap(a);
        if (a < 0) {
            require(uint256(-a) < PRIME, "Field: input is too large");
            return Field.Type.wrap(PRIME - uint256(-a));
        } else {
            require(uint256(a) < PRIME, "Field: input is too large");
            return Field.Type.wrap(uint256(a));
        }
    }

    function into(Field.Type[] memory a) internal pure returns (bytes32[] memory b) {
        assembly {
            b := a
        }
    }

    function add(Field.Type a, Field.Type b) internal pure returns (Field.Type c) {
        assembly {
            c := addmod(a, b, PRIME)
        }
    }

    function mul(Field.Type a, Field.Type b) internal pure returns (Field.Type c) {
        assembly {
            c := mulmod(a, b, PRIME)
        }
    }

    function add(Field.Type a, uint256 b) internal pure returns (Field.Type c) {
        assembly {
            c := addmod(a, b, PRIME)
        }
    }

    function mul(Field.Type a, uint256 b) internal pure returns (Field.Type c) {
        assembly {
            c := mulmod(a, b, PRIME)
        }
    }

    function eq(Field.Type a, Field.Type b) internal pure returns (bool c) {
        assembly {
            c := eq(a, b)
        }
    }

    function isZero(Field.Type a) internal pure returns (bool c) {
        assembly {
            c := eq(a, 0)
        }
    }

    function signed(Field.Type a) internal pure returns (bool positive, uint256 scalar) {
        uint256 raw = Field.Type.unwrap(a);
        if (raw > PRIME_DIV_2) {
            return (false, PRIME - raw);
        } else {
            return (true, raw);
        }
    }
}
