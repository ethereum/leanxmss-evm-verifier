// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;

import {LeanXmss} from "./LeanXmss.sol";
import {RequestQueue} from "./RequestQueue.sol";

/// @title PQValidatorExit
/// @notice Voluntary exit requests signed by a validator's leanXMSS key. Anyone can submit one;
///         the signature, not the caller, authorizes the exit.
/// @dev The request calldata is 2444 bytes:
///        validator_index (u64 big-endian, 8) ‖ xmss_pubkey (32) ‖ signature (2404)
///      The contract rejects the request unless the signature is at leaf `EXIT_LEAF_INDEX` (1),
///      by `xmss_pubkey`, over
///        M = keccak256(EXIT_DOMAIN ‖ chain_id (32) ‖ validator_index (8) ‖ xmss_pubkey (32)).
///      The log and the system call output hold 60-byte records:
///        source_address (20) ‖ validator_index (8) ‖ xmss_pubkey (32)
///      The consensus layer honors a record only if the leanXMSS key registered for
///      `validator_index` equals `xmss_pubkey`; `source_address` grants nothing.
///
///      The queue is `RequestQueue`, EIP-8483's. Each request takes three slots. The target is 2
///      requests per block, with at most 16 added and 16 dequeued per block, EIP-7002's values.
contract PQValidatorExit is RequestQueue {
    uint256 internal constant VALIDATOR_INDEX_LENGTH = 8;
    uint256 internal constant XMSS_PUBKEY_LENGTH = 32;

    /// @notice The leaf index reserved for a key's exit signature, next to EIP-8450's
    ///         `PQ_POSSESSION_XMSS_INDEX` (0). Proposed as `PQ_EXIT_XMSS_INDEX`.
    uint32 internal constant EXIT_LEAF_INDEX = 1;
    bytes32 internal constant EXIT_DOMAIN = keccak256("leanXMSS voluntary exit v1");

    /// @notice The message `M` that an exit signs for the request `input`: the domain, the chain ID
    ///         as a 32-byte word, then the first 40 bytes of the input, which are the validator
    ///         index and the XMSS public key.
    function _exitMessage(bytes calldata input) internal view returns (bytes32 m) {
        bytes32 domain = EXIT_DOMAIN;
        // Writes the preimage at the free memory pointer without allocating it, since nothing
        // reads it after the hash.
        assembly ("memory-safe") {
            let p := mload(0x40)
            mstore(p, domain)
            mstore(add(p, 0x20), chainid())
            calldatacopy(
                add(p, 0x40),
                input.offset,
                add(VALIDATOR_INDEX_LENGTH, XMSS_PUBKEY_LENGTH)
            )
            m := keccak256(p, add(0x40, add(VALIDATOR_INDEX_LENGTH, XMSS_PUBKEY_LENGTH)))
        }
    }

    /// @dev Reverts unless the signature after the input is the key's exit signature.
    function _checkSignature(bytes calldata input) internal view override {
        bytes calldata signature = input[_inputLength():];
        bytes32 xmssPubkey =
            bytes32(input[VALIDATOR_INDEX_LENGTH:VALIDATOR_INDEX_LENGTH + XMSS_PUBKEY_LENGTH]);
        if (LeanXmss.signatureIndex(signature) != EXIT_LEAF_INDEX) revert();
        if (!LeanXmss.verify(xmssPubkey, _exitMessage(input), signature)) revert();
    }

    function _inputLength() internal pure override returns (uint256) {
        return 40;
    }

    function _slotsPerRequest() internal pure override returns (uint256) {
        return 3;
    }

    function _targetRequestsPerBlock() internal pure override returns (uint256) {
        return 2;
    }

    function _maxRequestsAddedPerBlock() internal pure override returns (uint256) {
        return 16;
    }

    function _maxRequestsPerBlock() internal pure override returns (uint256) {
        return 16;
    }
}
