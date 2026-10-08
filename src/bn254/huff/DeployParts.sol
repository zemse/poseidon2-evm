// SPDX-License-Identifier: MIT
pragma solidity ^0.8.13;

/// @notice Deploys the parts of a split Huff permutation (generator/huff/split.ts)
/// @dev Parts go up last to first: each initcode but the last gets the address
/// of the part after it appended as a 32-byte word, which that part's
/// constructor keeps behind its runtime code. The address returned is part 0,
/// the contract that takes the t input words and returns the t output words.
library DeployParts {
    function deploy(bytes[] memory initcodes) internal returns (address first) {
        address next;
        for (uint256 i = initcodes.length; i > 0; i--) {
            bytes memory code =
                i == initcodes.length ? initcodes[i - 1] : bytes.concat(initcodes[i - 1], abi.encode(next));
            assembly {
                next := create(0, add(code, 0x20), mload(code))
            }
            require(next != address(0), "part deployment failed");
        }
        return next;
    }
}
