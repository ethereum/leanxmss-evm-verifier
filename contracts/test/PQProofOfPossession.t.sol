// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;

import {Test} from "forge-std/Test.sol";
import {LeanXmssHarness} from "./LeanXmss.t.sol";
import {PQProofOfPossession} from "../src/PQProofOfPossession.sol";

/// Tests what a proof of possession binds. A proof is a signature at leaf 0, by the XMSS key, of
/// `M = keccak256(POP_DOMAIN ‖ chain_id ‖ bls_pubkey ‖ xmss_pubkey)`. The proofs come from the
/// generator in xmss/.
contract PQProofOfPossessionTest is Test {
    struct Proof {
        bytes blsPubkey;
        bytes32 xmssPubkey;
        bytes32 message;
        uint256 leafIndex;
        bytes signature;
    }

    bytes32 internal constant POP_DOMAIN =
        keccak256("leanXMSS registration proof of possession v1");

    address internal verifier;
    LeanXmssHarness internal harness;
    string internal vectors;

    function setUp() public {
        verifier = address(new PQProofOfPossession());
        harness = new LeanXmssHarness();
        vectors = vm.readFile("test/vectors/leanxmss_pop.json");
        assertEq(block.chainid, vm.parseJsonUint(vectors, ".chainId"));
    }

    /// Proof `i` of the generator's three valid proofs.
    function proof(uint256 i) internal view returns (Proof memory) {
        return proofAt(string.concat(".proofs[", vm.toString(i), "]"));
    }

    function proofAt(string memory key) internal view returns (Proof memory p) {
        p.blsPubkey = vm.parseJsonBytes(vectors, string.concat(key, ".blsPubkey"));
        p.xmssPubkey = vm.parseJsonBytes32(vectors, string.concat(key, ".xmssPubkey"));
        p.message = vm.parseJsonBytes32(vectors, string.concat(key, ".message"));
        p.leafIndex = vm.parseJsonUint(vectors, string.concat(key, ".leafIndex"));
        p.signature = vm.parseJsonBytes(vectors, string.concat(key, ".signature"));
    }

    /// The verifier's calldata for `p`: the two keys followed by the signature.
    function input(Proof memory p) internal pure returns (bytes memory) {
        return bytes.concat(p.blsPubkey, p.xmssPubkey, p.signature);
    }

    /// Calls the verifier as the geas contracts do, with a STATICCALL, and returns whether it
    /// accepted the proof. A call either returns the word 1 or reverts with no data.
    function accepts(bytes memory data) internal view returns (bool) {
        (bool ok, bytes memory out) = verifier.staticcall(data);
        if (ok) assertEq(out, abi.encode(uint256(1)));
        else assertEq(out.length, 0);
        return ok;
    }

    /// The generator signs, at leaf 0, the same `M` that the contract checks.
    function test_ProofsSignTheMessageAtLeafZero() public view {
        assertEq(vm.parseJsonBytes32(vectors, ".popDomain"), POP_DOMAIN);
        for (uint256 i; i < 3; i++) {
            Proof memory p = proof(i);
            assertEq(
                p.message,
                keccak256(abi.encodePacked(POP_DOMAIN, block.chainid, p.blsPubkey, p.xmssPubkey))
            );
            assertEq(p.leafIndex, 0);
            assertEq(harness.signatureIndex(p.signature), 0);
            assertTrue(harness.verify(p.xmssPubkey, p.message, p.signature));
        }
    }

    function test_AcceptsProofs() public view {
        for (uint256 i; i < 3; i++) {
            assertTrue(accepts(input(proof(i))));
        }
    }

    function test_RevertWhen_NotInputLength() public view {
        Proof memory p = proof(0);
        assertFalse(accepts(""));
        assertFalse(accepts(bytes.concat(p.blsPubkey, p.xmssPubkey)));
        assertFalse(accepts(p.signature));
        assertFalse(accepts(bytes.concat(input(p), hex"00")));
        // A validator request, which has 32 bytes of VRF data before the signature.
        assertFalse(accepts(bytes.concat(p.blsPubkey, p.xmssPubkey, bytes32(0), p.signature)));
        bytes memory short = input(p);
        assembly {
            mstore(short, sub(mload(short), 1))
        }
        assertFalse(accepts(short));
    }

    function test_RevertWhen_OtherChain() public {
        vm.chainId(1);
        assertFalse(accepts(input(proof(0))));
    }

    function test_RevertWhen_OtherBlsKey() public view {
        Proof memory p = proof(0);
        p.blsPubkey = proof(1).blsPubkey;
        assertFalse(accepts(input(p)));
    }

    /// A proof signed by one XMSS key doesn't pass for another one.
    function test_RevertWhen_OtherXmssKey() public view {
        Proof memory p = proof(0);
        p.xmssPubkey = proof(1).xmssPubkey;
        assertFalse(accepts(input(p)));
    }

    /// A valid signature at leaf 0 of the message without the domain.
    function test_RevertWhen_MessageWithoutDomain() public view {
        Proof memory p = proofAt(".noDomain");
        assertEq(p.message, keccak256(abi.encodePacked(block.chainid, p.blsPubkey, p.xmssPubkey)));
        assertEq(harness.signatureIndex(p.signature), 0);
        assertTrue(harness.verify(p.xmssPubkey, p.message, p.signature));
        assertFalse(accepts(input(p)));
    }

    /// A valid signature of `M` at leaf 1. A proof of possession must be at leaf 0.
    function test_RevertWhen_NotAtLeafZero() public view {
        Proof memory p = proofAt(".wrongLeaf");
        assertEq(p.message, proof(0).message);
        assertEq(harness.signatureIndex(p.signature), 1);
        assertTrue(harness.verify(p.xmssPubkey, p.message, p.signature));
        assertFalse(accepts(input(p)));
    }

    function test_RevertWhen_CallCarriesValue() public {
        (bool ok,) = verifier.call{value: 1}(input(proof(0)));
        assertFalse(ok);
    }

    /// One changed bit anywhere in the calldata, in a key or in the signature, is rejected.
    function testFuzz_RevertWhen_BitChanged(uint256 i, uint256 bit) public view {
        bytes memory data = input(proof(i % 3));
        bit = bound(bit, 0, 8 * data.length - 1);
        data[bit / 8] ^= bytes1(uint8(1 << (bit % 8)));
        assertFalse(accepts(data));
    }

    /// Calldata of any other length is rejected: the proof cut short, or with zeros after it.
    function testFuzz_RevertWhen_OtherLength(uint256 i, uint256 length) public view {
        bytes memory data = input(proof(i % 3));
        length = bound(length, 0, data.length + 32);
        vm.assume(length != data.length);
        if (length > data.length) data = bytes.concat(data, new bytes(length - data.length));
        assembly {
            mstore(data, length)
        }
        assertFalse(accepts(data));
    }
}
