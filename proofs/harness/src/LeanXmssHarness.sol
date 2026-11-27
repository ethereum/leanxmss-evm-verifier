// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;

import {LeanXmss} from "leanxmss/LeanXmss.sol";

/// @title LeanXmssHarness
/// @notice Calls `LeanXmss.verify` on its calldata, for the proofs in `proofs/` only. It is never
///         deployed.
/// @dev The calldata is public key (32) ‖ message (32) ‖ signature, the signature of any length.
///      The call returns `verify`'s answer as a 32-byte word, 1 or 0. It reverts with no data
///      for calldata shorter than 64 bytes and for a call with value.
contract LeanXmssHarness {
    fallback() external {
        bytes calldata input = msg.data;
        bytes32 publicKey = bytes32(input[0:32]);
        bytes32 message = bytes32(input[32:64]);
        bool ok = LeanXmss.verify(publicKey, message, input[64:]);
        assembly ("memory-safe") {
            mstore(0, ok)
            return(0, 0x20)
        }
    }
}
