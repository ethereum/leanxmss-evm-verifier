// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;

import {LeanXmss} from "./LeanXmss.sol";
import {RequestQueue} from "./RequestQueue.sol";

/// @notice EIP-8483's PQ registration request contract, which also checks a leanXMSS proof of
///         possession when a request is added.
/// @dev The contract behaves like the EIP's bytecode except for one thing: a request carries a
///      2404-byte leanXMSS signature after the EIP's input, and the contract rejects the request
///      unless that signature is a proof of possession. That is, a signature at leaf 0 by the
///      XMSS key in the first 32 bytes of `pq_data`, over
///        M = keccak256(POP_DOMAIN ‖ chain_id (32) ‖ bls_pubkey (48) ‖ xmss_public_key (32)).
///      The signature isn't stored or logged, so the queue, the log and the system call's output
///      are the same as the EIP's. The queue is `RequestQueue`.
abstract contract RegistrationQueue is RequestQueue {
    uint256 internal constant BLS_PUBKEY_LENGTH = 48;
    uint256 internal constant XMSS_PUBKEY_LENGTH = 32;
    uint32 internal constant POP_LEAF_INDEX = 0;
    bytes32 internal constant POP_DOMAIN =
        keccak256("leanXMSS registration proof of possession v1");

    /// @notice The message `M` that a proof of possession signs for the request `input`. It hashes
    ///         the domain, the chain ID as a 32-byte word, and the first 80 bytes of the input,
    ///         which are the BLS public key and the XMSS public key.
    function _popMessage(bytes calldata input) internal view returns (bytes32 m) {
        bytes32 domain = POP_DOMAIN;
        // Writes the preimage at the free memory pointer without allocating it, since nothing
        // reads it after the hash.
        assembly ("memory-safe") {
            let p := mload(0x40)
            mstore(p, domain)
            mstore(add(p, 0x20), chainid())
            calldatacopy(add(p, 0x40), input.offset, add(BLS_PUBKEY_LENGTH, XMSS_PUBKEY_LENGTH))
            m := keccak256(p, add(0x40, add(BLS_PUBKEY_LENGTH, XMSS_PUBKEY_LENGTH)))
        }
    }

    /// @dev Reverts unless the signature after the EIP's input is a proof of possession.
    function _checkSignature(bytes calldata input) internal view virtual override {
        bytes calldata signature = input[_inputLength():];
        bytes32 xmssPubkey =
            bytes32(input[BLS_PUBKEY_LENGTH:BLS_PUBKEY_LENGTH + XMSS_PUBKEY_LENGTH]);
        if (LeanXmss.signatureIndex(signature) != POP_LEAF_INDEX) revert();
        if (!LeanXmss.verify(xmssPubkey, _popMessage(input), signature)) revert();
    }
}
