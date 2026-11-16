// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;

import {Test} from "forge-std/Test.sol";
import {Vm} from "forge-std/Vm.sol";
import {LeanXmssHarness} from "./LeanXmss.t.sol";
import {feeAt} from "./helpers/Fee.sol";
import {PQValidatorExit} from "../src/PQValidatorExit.sol";

/// Tests the exit contract. An exit is a signature at leaf 1, by the XMSS key, of
/// `M = keccak256(EXIT_DOMAIN ‖ chain_id ‖ validator_index ‖ xmss_pubkey)`. The signatures come
/// from the generator in xmss/. The queue is the registration contracts' (`RequestQueue`), which
/// `RegistrationQueue.t.sol` checks against EIP-8483's bytecode; these tests check the exit
/// contract's own parameters and record.
contract ValidatorExitTest is Test {
    struct Exit {
        uint64 validatorIndex;
        bytes32 xmssPubkey;
        bytes32 message;
        uint256 leafIndex;
        bytes signature;
    }

    address internal constant SYSTEM_ADDRESS = 0xffffFFFfFFffffffffffffffFfFFFfffFFFfFFfE;
    uint256 internal constant SIGNATURE_LENGTH = 2404;
    uint256 internal constant INPUT_LENGTH = 40;
    uint256 internal constant RECORD_LENGTH = 60;
    uint256 internal constant QUEUE_OFFSET = 5;
    uint256 internal constant SLOTS_PER_REQUEST = 3;
    uint256 internal constant TARGET = 2;
    uint256 internal constant MAX_ADDED_PER_BLOCK = 16;
    uint256 internal constant MAX_PER_BLOCK = 16;
    bytes32 internal constant EXIT_DOMAIN = keccak256("leanXMSS voluntary exit v1");

    address internal exits;
    LeanXmssHarness internal harness;
    string internal vectors;

    function setUp() public {
        exits = address(new PQValidatorExit());
        harness = new LeanXmssHarness();
        vectors = vm.readFile("test/vectors/leanxmss_exit.json");
        assertEq(block.chainid, vm.parseJsonUint(vectors, ".chainId"));
    }

    // --- Vectors and calldata ------------------------------------------------------------------

    /// Exit `i` of the generator's two valid exits.
    function exit(uint256 i) internal view returns (Exit memory) {
        return exitAt(string.concat(".exits[", vm.toString(i), "]"));
    }

    function exitAt(string memory key) internal view returns (Exit memory e) {
        e.validatorIndex = uint64(vm.parseJsonUint(vectors, string.concat(key, ".validatorIndex")));
        e.xmssPubkey = vm.parseJsonBytes32(vectors, string.concat(key, ".xmssPubkey"));
        e.message = vm.parseJsonBytes32(vectors, string.concat(key, ".message"));
        e.leafIndex = vm.parseJsonUint(vectors, string.concat(key, ".leafIndex"));
        e.signature = vm.parseJsonBytes(vectors, string.concat(key, ".signature"));
    }

    function exitMessage(uint64 validatorIndex, bytes32 xmssPubkey)
        internal
        view
        returns (bytes32)
    {
        return keccak256(abi.encodePacked(EXIT_DOMAIN, block.chainid, validatorIndex, xmssPubkey));
    }

    /// The input that the contract stores and logs: the validator index and the XMSS key.
    function input(Exit memory e) internal pure returns (bytes memory out) {
        out = abi.encodePacked(e.validatorIndex, e.xmssPubkey);
        assertEq(out.length, INPUT_LENGTH);
    }

    function request(Exit memory e) internal pure returns (bytes memory) {
        return bytes.concat(input(e), e.signature);
    }

    function record(address sender, Exit memory e) internal pure returns (bytes memory) {
        return bytes.concat(bytes20(sender), input(e));
    }

    function feeOf() internal returns (uint256) {
        (bool ok, bytes memory out) = exits.call("");
        assertTrue(ok, "fee getter failed");
        return abi.decode(out, (uint256));
    }

    /// Sends a request from `sender` paying exactly the current fee; returns whether it was added.
    function submitFrom(address sender, bytes memory data) internal returns (bool ok) {
        uint256 fee = feeOf();
        vm.deal(sender, fee);
        vm.prank(sender);
        (ok,) = exits.call{value: fee}(data);
    }

    function submit(bytes memory data) internal returns (bool) {
        return submitFrom(address(this), data);
    }

    function systemCall() internal returns (bytes memory records) {
        vm.prank(SYSTEM_ADDRESS);
        bool ok;
        (ok, records) = exits.call("");
        assertTrue(ok, "system call failed");
    }

    function load(uint256 slot) internal view returns (uint256) {
        return uint256(vm.load(exits, bytes32(slot)));
    }

    function sender(uint256 j) internal pure returns (address) {
        return address(uint160(0xe817000 + j));
    }

    // --- What an exit binds --------------------------------------------------------------------

    /// The generator signs, at leaf 1, the same `M` that the contract checks.
    function test_ExitsSignTheMessageAtLeafOne() public view {
        assertEq(vm.parseJsonBytes32(vectors, ".exitDomain"), EXIT_DOMAIN);
        for (uint256 i; i < 2; i++) {
            Exit memory e = exit(i);
            assertEq(e.message, exitMessage(e.validatorIndex, e.xmssPubkey));
            assertEq(e.leafIndex, 1);
            assertEq(harness.signatureIndex(e.signature), 1);
            assertTrue(harness.verify(e.xmssPubkey, e.message, e.signature));
        }
        // The second index has eight distinct bytes, so the big-endian encoding is checked.
        assertEq(exit(1).validatorIndex, 0x0102030405060708);
    }

    function test_RevertWhen_OtherChain() public {
        vm.chainId(1);
        assertFalse(submit(request(exit(0))));
    }

    /// An exit signed for one validator index doesn't exit another one.
    function test_RevertWhen_OtherValidatorIndex() public {
        Exit memory e = exit(0);
        e.validatorIndex += 1;
        assertFalse(submit(request(e)));
        e = exit(1);
        e.validatorIndex = 0x0807060504030201;
        assertFalse(submit(request(e)));
    }

    /// An exit signed by one XMSS key doesn't exit with another one.
    function test_RevertWhen_OtherXmssKey() public {
        Exit memory e = exit(0);
        e.xmssPubkey = exit(1).xmssPubkey;
        assertFalse(submit(request(e)));
    }

    /// A valid signature of the exit message at leaf 2. An exit must be at leaf 1.
    function test_RevertWhen_NotAtLeafOne() public {
        Exit memory e = exitAt(".wrongLeaf");
        assertEq(e.message, exitMessage(e.validatorIndex, e.xmssPubkey));
        assertEq(harness.signatureIndex(e.signature), 2);
        assertTrue(harness.verify(e.xmssPubkey, e.message, e.signature));
        assertFalse(submit(request(e)));
    }

    /// A valid signature at leaf 1 of the exit message without the domain.
    function test_RevertWhen_MessageWithoutDomain() public {
        Exit memory e = exitAt(".noDomain");
        assertEq(
            e.message, keccak256(abi.encodePacked(block.chainid, e.validatorIndex, e.xmssPubkey))
        );
        assertEq(harness.signatureIndex(e.signature), 1);
        assertTrue(harness.verify(e.xmssPubkey, e.message, e.signature));
        assertFalse(submit(request(e)));
    }

    /// Signatures made for registration don't exit: a proof of possession (leaf 0), and a valid
    /// leaf-1 signature of a proof-of-possession message.
    function test_RevertWhen_RegistrationSignature() public {
        string memory pop = vm.readFile("test/vectors/leanxmss_pop.json");

        // Key B's proof of possession, offered as key B's exit.
        Exit memory e = exit(0);
        assertEq(vm.parseJsonBytes32(pop, ".proofs[1].xmssPubkey"), e.xmssPubkey);
        e.signature = vm.parseJsonBytes(pop, ".proofs[1].signature");
        assertEq(harness.signatureIndex(e.signature), 0);
        assertFalse(submit(request(e)));

        // Key A's leaf-1 signature of its proof-of-possession message.
        e.xmssPubkey = vm.parseJsonBytes32(pop, ".wrongLeaf.xmssPubkey");
        e.signature = vm.parseJsonBytes(pop, ".wrongLeaf.signature");
        assertEq(harness.signatureIndex(e.signature), 1);
        assertTrue(
            harness.verify(
                e.xmssPubkey, vm.parseJsonBytes32(pop, ".wrongLeaf.message"), e.signature
            )
        );
        assertFalse(submit(request(e)));
    }

    function test_RevertWhen_SignatureTampered() public {
        Exit memory e = exit(0);
        for (uint256 offset = 1; offset < SIGNATURE_LENGTH; offset += 401) {
            Exit memory tampered = exit(0);
            tampered.signature[offset] = e.signature[offset] ^ 0x01;
            assertFalse(submit(request(tampered)));
        }
        assertTrue(submit(request(e)));
    }

    /// Calldata of any length other than a request's is rejected, including the input alone.
    function test_RevertWhen_NotRequestLength() public {
        Exit memory e = exit(0);
        assertFalse(submit(input(e)));
        assertFalse(submit(bytes.concat(request(e), hex"00")));
        bytes memory short = request(e);
        assembly {
            mstore(short, sub(mload(short), 1))
        }
        assertFalse(submit(short));
    }

    // --- Queue and record ----------------------------------------------------------------------

    /// Anyone can submit an exit. The contract stores and logs the caller, the validator index and
    /// the XMSS key, not the signature, in three slots per request.
    function test_AnyCallerStoresAndLogsRecord() public {
        for (uint256 i; i < 2; i++) {
            Exit memory e = exit(i);
            vm.record();
            vm.recordLogs();
            assertTrue(submitFrom(sender(i), request(e)));

            // EIP-7708 also logs the fee's transfer, so only the contract's own logs are counted.
            Vm.Log[] memory logs = vm.getRecordedLogs();
            uint256 n;
            for (uint256 l; l < logs.length; l++) {
                if (logs[l].emitter != exits) continue;
                assertEq(logs[l].topics.length, 0);
                assertEq(logs[l].data, record(sender(i), e));
                n++;
            }
            assertEq(n, 1);

            uint256 first = QUEUE_OFFSET + i * SLOTS_PER_REQUEST;
            (, bytes32[] memory writes) = vm.accesses(exits);
            for (uint256 w; w < writes.length; w++) {
                uint256 slot = uint256(writes[w]);
                bool fee = slot == 0 || slot == 1 || slot == 3 || slot == 4;
                assertTrue(fee || (slot >= first && slot < first + SLOTS_PER_REQUEST));
            }

            // Source address, then the 40-byte input in two slots, the second zero-padded.
            bytes memory in_ = input(e);
            bytes32 high;
            bytes32 low;
            assembly {
                high := mload(add(in_, 0x20))
                low := mload(add(in_, 0x40))
            }
            low &= bytes32(uint256(type(uint64).max) << 192);
            assertEq(load(first), uint160(sender(i)));
            assertEq(bytes32(load(first + 1)), high);
            assertEq(bytes32(load(first + 2)), low);
        }
    }

    function test_SystemCallReturnsRecordsInOrder() public {
        assertEq(systemCall(), "");
        assertTrue(submitFrom(sender(0), request(exit(0))));
        assertTrue(submitFrom(sender(1), request(exit(1))));
        assertEq(systemCall(), bytes.concat(record(sender(0), exit(0)), record(sender(1), exit(1))));
        assertEq(load(2), 0);
        assertEq(load(3), 0);
    }

    /// EIP-7002's limits: the fee rises above 2 requests in a block, at most 16 are added per
    /// block, and the system call dequeues at most 16. A signed exit can be submitted again; the
    /// consensus layer ignores an exit it has already applied.
    function test_FeeAndPerBlockLimits() public {
        bytes memory data = request(exit(0));
        for (uint256 j; j < MAX_ADDED_PER_BLOCK; j++) {
            assertEq(feeOf(), feeAt(j > TARGET ? j - TARGET : 0));
            assertTrue(submitFrom(sender(j), data));
        }
        assertFalse(submitFrom(sender(0), data));

        vm.roll(block.number + 1);
        for (uint256 j; j < 4; j++) {
            assertTrue(submitFrom(sender(j), data));
        }

        assertEq(systemCall().length, MAX_PER_BLOCK * RECORD_LENGTH);
        assertEq(systemCall().length, 4 * RECORD_LENGTH);
        assertEq(systemCall().length, 0);
    }
}
