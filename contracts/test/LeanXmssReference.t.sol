// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;

import {Test} from "forge-std/Test.sol";
import {LeanXmssHarness, LeanXmssMemoryHarness, LeanXmssReferenceHarness} from "./LeanXmss.t.sol";
import {LeanXmssVectors} from "./helpers/LeanXmssVectors.sol";

/// Checks the unrolled verifier against the one written with loops, on signatures EthLib's cases
/// don't have: other leaf indices and other digits, digests that are almost codewords, and with
/// memory allocated by the caller.
///
/// The tests build their signatures without a secret key, since verifying only recomputes a root:
/// the chain values and the siblings are random, and the public key has the root the reference
/// reaches. What costs is the randomizers. A layer's digest has to be a codeword, about one
/// digest in a million is one, and so finding a randomizer takes about 150M gas. The tests on
/// fixed cases have the randomizers they found before, as the counters in `validCounters` and
/// `closeCounters`. The fuzz tests search for theirs, so they run twice by default and 250 times
/// with `FOUNDRY_PROFILE=deep`.
contract LeanXmssReferenceTest is Test {
    uint256 internal constant SIGNATURE_LENGTH = 2404;
    uint256 internal constant TOP_LAYER = 1204;
    bytes32 internal constant LOW_HALF = bytes32(uint256(type(uint128).max));
    /// For `Search.past`: any of the twelve bits past the 58th digit is set.
    uint256 internal constant ANY_BIT = 0x10000;
    /// The leaf index of the odd cases of `closeCase`.
    uint32 internal constant SOME_LEAF = 0x9e3779b9;

    /// How many randomizers a search tries. A try takes about 160 gas, so the two searches of a
    /// signature take at most 800M of the 1,073M a test has. One search in ten gives up.
    uint256 internal tries = 2_500_000;

    /// A digest to look for: the digest of `signed`, the first `len` bytes of a word, after the
    /// address word `first`, with the randomizers from `from` up to `to`. `past` is what it has
    /// in the twelve bits past its 58th digit, read as a big-endian number, or `ANY_BIT`. Its 64
    /// digits sum to `sum`, or to anything else when `equal` is false. With `past` zero and a sum
    /// of 106 it is a codeword.
    struct Search {
        bytes32 first;
        bytes32 signed;
        uint256 len;
        uint256 past;
        uint256 sum;
        bool equal;
        uint256 from;
        uint256 to;
    }

    /// A digest that isn't a codeword and is close to one, in the layer `bottom` says, of a
    /// signature at `leaf`. The other fields are `Search`'s.
    struct Close {
        uint32 leaf;
        bool bottom;
        uint256 past;
        uint256 sum;
        bool equal;
    }

    LeanXmssHarness internal harness;
    LeanXmssReferenceHarness internal referenceHarness;
    LeanXmssMemoryHarness internal memoryHarness;

    /// EthLib's valid cases.
    bytes32[] internal keys;
    bytes32[] internal messages;
    bytes[] internal signatures;

    function setUp() public {
        harness = new LeanXmssHarness();
        referenceHarness = new LeanXmssReferenceHarness();
        memoryHarness = new LeanXmssMemoryHarness();
        LeanXmssVectors.VerifyCase[] memory cases = LeanXmssVectors.loadVerify();
        for (uint256 i; i < cases.length; i++) {
            if (!cases[i].expected) continue;
            keys.push(bytes32(cases[i].publicKey));
            messages.push(bytes32(cases[i].message));
            signatures.push(cases[i].signature);
        }
        assertEq(keys.length, 4);
    }

    // --- Signatures that verify --------------------------------------------------------------

    /// Both verifiers accept a signature built at each of these leaf indices, and agree on copies
    /// of it. The indices have zero and nonzero bytes in every place, and between `0x5a5a5a5a` and
    /// `0xa5a5a5a5` every node of both paths is once a left child and once a right one.
    function test_VerifiesWhatTheReferenceDoes() public view {
        uint32[16] memory indices = leaves();
        uint32[2][16] memory counters = validCounters();
        for (uint256 i; i < indices.length; i++) {
            (uint32[2] memory used, bytes32 key, bytes32 message, bytes memory sig) =
                signatureAt(indices[i], indices[i], counters[i]);
            assertEq(used[1], counters[i][1]);
            check(key, message, sig, indices[i]);
        }
    }

    /// forge-config: default.fuzz.runs = 2
    /// forge-config: deep.fuzz.runs = 250
    /// The same at a random leaf index and with random contents, so with other digits in every
    /// run. A quarter of the runs are at leaf zero, where a proof of possession is, and a
    /// quarter in the first tree, where only the top path is at index zero.
    function testFuzz_VerifiesWhatTheReferenceDoes(uint32 leaf, uint8 shape, uint256 salt)
        public
        view
    {
        if (shape % 4 == 0) leaf = 0;
        if (shape % 4 == 1) leaf &= 0xffff;
        if (shape % 4 == 2) leaf &= 0xffff0000;
        (uint32[2] memory used, bytes32 key, bytes32 message, bytes memory sig) =
            signatureAt(leaf, salt, [uint32(0), 0]);
        vm.assume(used[1] != 0);
        check(key, message, sig, salt);
    }

    /// The top layer of a valid case gets other chain values and siblings. Its digest doesn't
    /// depend on them, so they reach another root, and the unrolled verifier accepts the case
    /// under the root the reference reaches.
    function testFuzz_ReachesTheReferenceRoot(uint256 which, bytes32 seed) public view {
        which = bound(which, 0, keys.length - 1);
        bytes memory sig = signatures[which];
        fill(sig, TOP_LAYER + 16, SIGNATURE_LENGTH, seed);
        (bool valid, bytes16 top) = referenceHarness.root(keys[which], messages[which], sig);
        assertTrue(valid);
        bytes32 key = bytes32(top) | (keys[which] & LOW_HALF);
        assertTrue(harness.verify(key, messages[which], sig));
        assertFalse(harness.verify(keys[which], messages[which], sig));
    }

    /// Checks that both verifiers accept a signature that verifies, and agree on copies of it.
    function check(bytes32 key, bytes32 message, bytes memory sig, uint256 salt) internal view {
        assertTrue(referenceHarness.verify(key, message, sig));
        assertTrue(harness.verify(key, message, sig));

        // Other chain values and siblings in the top layer, which keep its digest.
        for (uint256 round; round < 4; round++) {
            fill(sig, TOP_LAYER + 16, SIGNATURE_LENGTH, keccak256(abi.encode(salt, "top", round)));
            (bool valid, bytes16 top) = referenceHarness.root(key, message, sig);
            assertTrue(valid);
            assertFalse(harness.verify(key, message, sig));
            key = bytes32(top) | (key & LOW_HALF);
            assertTrue(harness.verify(key, message, sig));
        }

        // A changed bit in the first value of each field of each layer, and four anywhere.
        uint256[10] memory offsets = [uint256(0), 20, 948, 1204, 1220, 2148, 0, 0, 0, 0];
        for (uint256 k; k < offsets.length; k++) {
            uint256 random = uint256(keccak256(abi.encode(salt, "bit", k)));
            if (k >= 6) offsets[k] = random % SIGNATURE_LENGTH;
            bytes1 bit = bytes1(uint8(1 << (random >> 248) % 8));
            sig[offsets[k]] ^= bit;
            assertFalse(referenceHarness.verify(key, message, sig));
            assertFalse(harness.verify(key, message, sig));
            sig[offsets[k]] ^= bit;
        }
        assertFalse(harness.verify(key ^ bytes32(uint256(1) << 128), message, sig));
        assertFalse(harness.verify(key ^ bytes32(uint256(1)), message, sig));
        assertFalse(harness.verify(key, message ^ bytes32(uint256(1)), sig));
        assertTrue(harness.verify(key, message, sig));
    }

    // --- Digests that are almost codewords ---------------------------------------------------

    /// Both verifiers reject a signature that only the codeword check rejects. One layer's digest
    /// is a codeword and the other's is close to one, and the public key has the root that the
    /// chains and the paths reach anyway, so a verifier that let the digest through would accept.
    /// See `closeCase` for the 32 cases.
    function test_RejectsADigestThatIsNotACodeword() public view {
        uint32[2][32] memory counters = closeCounters();
        for (uint256 i; i < counters.length; i++) {
            uint32[2] memory used = checkClose(closeCase(i), i, counters[i]);
            assertEq(used[1], counters[i][1]);
        }
    }

    /// forge-config: default.fuzz.runs = 2
    /// forge-config: deep.fuzz.runs = 250
    /// The same with random contents and at a random leaf index, or at leaf zero. The digest is
    /// close to a codeword in one of five ways. Its digits past the 58th are zero and its sum is
    /// 105, 107, or anything but 106. Or its 64 digits sum to 106 with some bit past the 58th set,
    /// or with exactly one of the twelve.
    function testFuzz_RejectsADigestThatIsNotACodeword(uint8 kind, uint256 salt) public view {
        Close memory c = Close(kind & 4 == 0 ? 0 : uint32(salt), kind & 8 == 0, 0, 106, true);
        if (kind % 5 == 0) c.sum = 105;
        if (kind % 5 == 1) c.sum = 107;
        if (kind % 5 == 2) c.equal = false;
        if (kind % 5 == 3) c.past = ANY_BIT;
        if (kind % 5 == 4) c.past = pastBit((salt >> 32) % 12);
        uint32[2] memory used = checkClose(c, salt, [uint32(0), 0]);
        vm.assume(used[1] != 0);
    }

    /// The cases of `test_RejectsADigestThatIsNotACodeword`: sixteen digests, in the bottom layer
    /// and then in the top one, alternately at leaf zero and at another leaf. The first twelve
    /// have one of the twelve bits past the 58th digit set, and the 64 digits sum to 106. The
    /// thirteenth has any of those bits set. The last three have those bits zero and a sum of
    /// 105, of 107, and of anything but 106.
    function closeCase(uint256 i) internal pure returns (Close memory c) {
        c = Close(i % 2 == 0 ? 0 : SOME_LEAF, i < 16, 0, 106, true);
        uint256 kind = i % 16;
        if (kind < 12) c.past = pastBit(kind);
        if (kind == 12) c.past = ANY_BIT;
        if (kind == 13) c.sum = 105;
        if (kind == 14) c.sum = 107;
        if (kind == 15) c.equal = false;
    }

    /// One of the twelve bits past the 58th digit: of the last byte of the digest, then of the
    /// high half of the one before.
    function pastBit(uint256 bit) internal pure returns (uint256) {
        return bit < 8 ? 1 << bit : 1 << (bit + 4);
    }

    /// Builds the signature of case `c` from `salt` and checks that both verifiers reject it.
    /// `counters` has its two randomizers, or zeros to search for them. Returns the ones used,
    /// or zeros when a search gave up.
    function checkClose(Close memory c, uint256 salt, uint32[2] memory counters)
        internal
        view
        returns (uint32[2] memory used)
    {
        bytes memory sig = new bytes(SIGNATURE_LENGTH);
        fill(sig, 0, SIGNATURE_LENGTH, bytes32(salt));
        writeIndex(sig, c.leaf);
        bytes32 key = keccak256(abi.encode(salt, "key"));
        bytes32 message = keccak256(abi.encode(salt, "message"));

        Search memory s = digestOf(key, 0, c.leaf, message, 32);
        if (c.bottom) (s.past, s.sum, s.equal) = (c.past, c.sum, c.equal);
        used[0] = find(s, counters[0]);
        if (used[0] == 0) return [uint32(0), 0];
        write16(sig, 4, bytes16(uint128(used[0])));
        (, bytes16 bottom,,) = referenceHarness.roots(key, message, sig);
        s = digestOf(key, 1, c.leaf >> 16, bottom, 16);
        if (!c.bottom) (s.past, s.sum, s.equal) = (c.past, c.sum, c.equal);
        used[1] = find(s, counters[1]);
        if (used[1] == 0) return [uint32(0), 0];
        write16(sig, TOP_LAYER, bytes16(uint128(used[1])));

        (bool bottomValid,, bool topValid, bytes16 root) = referenceHarness.roots(key, message, sig);
        assertEq(bottomValid, !c.bottom);
        assertEq(topValid, c.bottom);
        key = bytes32(root) | (key & LOW_HALF);
        assertFalse(referenceHarness.verify(key, message, sig));
        assertFalse(harness.verify(key, message, sig));
    }

    // --- Changed bits and memory -------------------------------------------------------------

    /// One changed bit anywhere in a valid case makes both verifiers reject it.
    function testFuzz_RejectsWhatTheReferenceDoes(uint256 which, uint256 position, uint8 bit)
        public
        view
    {
        which = bound(which, 0, keys.length - 1);
        position = bound(position, 0, 64 + SIGNATURE_LENGTH - 1);
        bytes32 key = keys[which];
        bytes32 message = messages[which];
        bytes memory sig = signatures[which];
        bytes1 flip = bytes1(uint8(1 << (bit % 8)));
        if (position < 32) key ^= bytes32(flip) >> (8 * position);
        else if (position < 64) message ^= bytes32(flip) >> (8 * (position - 32));
        else sig[position - 64] ^= flip;
        assertFalse(referenceHarness.verify(key, message, sig));
        assertFalse(harness.verify(key, message, sig));
    }

    /// `verify` works at fixed memory addresses. With memory allocated up to before, at and past
    /// the end of what it uses, it gives the same result and leaves that memory as it was, which
    /// the harness checks.
    function test_LeavesAllocatedMemoryAsItWas() public view {
        uint16[7] memory sizes = [0, 1, 0x100, 0x530, 0x550, 0x551, 0x1000];
        for (uint256 i; i < keys.length; i++) {
            for (uint256 k; k < sizes.length; k++) {
                assertTrue(memoryHarness.verify(keys[i], messages[i], signatures[i], sizes[k]));
                bytes32 other = messages[i] ^ bytes32(uint256(1));
                assertFalse(memoryHarness.verify(keys[i], other, signatures[i], sizes[k]));
            }
        }
        // A signature that reaches the top layer and fails there.
        bytes memory sig = signatures[0];
        sig[TOP_LAYER + 16] ^= 0x01;
        assertFalse(memoryHarness.verify(keys[0], messages[0], sig, 0x100));
    }

    // --- Building signatures -----------------------------------------------------------------

    /// A public key, a message and a signature at `leaf` that verifies, from `salt`. `counters`
    /// has its two randomizers, or zeros to search for them. Returns the ones used, the second
    /// one zero when a search gave up.
    function signatureAt(uint32 leaf, uint256 salt, uint32[2] memory counters)
        internal
        view
        returns (uint32[2] memory used, bytes32 key, bytes32 message, bytes memory sig)
    {
        sig = new bytes(SIGNATURE_LENGTH);
        fill(sig, 0, SIGNATURE_LENGTH, bytes32(salt));
        writeIndex(sig, leaf);
        key = keccak256(abi.encode(salt, "key"));
        message = keccak256(abi.encode(salt, "message"));

        used[0] = find(digestOf(key, 0, leaf, message, 32), counters[0]);
        if (used[0] == 0) return (used, key, message, sig);
        write16(sig, 4, bytes16(uint128(used[0])));
        (bool valid, bytes16 bottom) = referenceHarness.bottomRoot(key, message, sig);
        assertTrue(valid);
        used[1] = find(digestOf(key, 1, leaf >> 16, bottom, 16), counters[1]);
        if (used[1] == 0) return (used, key, message, sig);
        write16(sig, TOP_LAYER, bytes16(uint128(used[1])));
        bytes16 top;
        (valid, top) = referenceHarness.root(key, message, sig);
        assertTrue(valid);
        key = bytes32(top) | (key & LOW_HALF);
    }

    /// The leaf index, little-endian.
    function writeIndex(bytes memory sig, uint32 leaf) internal pure {
        for (uint256 b; b < 4; b++) {
            sig[b] = bytes1(uint8(leaf >> (8 * b)));
        }
    }

    /// Writes random bytes from `seed` over `sig[from:to]`.
    function fill(bytes memory sig, uint256 from, uint256 to, bytes32 seed) internal pure {
        for (uint256 i = from; i < to; i += 32) {
            bytes32 word = keccak256(abi.encode(seed, i));
            for (uint256 b; b < 32 && i + b < to; b++) {
                sig[i + b] = word[b];
            }
        }
    }

    function write16(bytes memory sig, uint256 offset, bytes16 value) internal pure {
        for (uint256 b; b < 16; b++) {
            sig[offset + b] = value[b];
        }
    }

    /// The search for a codeword at key `index` of layer `layer`: the digest's address word has
    /// the type 12, the layer's flag and the index, little-endian.
    function digestOf(bytes32 key, uint256 layer, uint32 index, bytes32 signed, uint256 len)
        internal
        pure
        returns (Search memory s)
    {
        uint256 lo = index;
        lo = ((lo & 0xff) << 24) | ((lo & 0xff00) << 8) | ((lo >> 8) & 0xff00) | (lo >> 24);
        s.first = bytes32((uint256(key) << 128) | (lo << 96) | (layer << 79) | (12 << 64));
        (s.signed, s.len, s.sum, s.equal) = (signed, len, 106, true);
    }

    /// The counter of a randomizer that gives the digest `s` asks for. It is `known` when that
    /// isn't zero, after checking that it does. Otherwise it's the first one found, or zero.
    function find(Search memory s, uint32 known) internal view returns (uint32) {
        if (known != 0) {
            (s.from, s.to) = (known, uint256(known) + 1);
            assertEq(search(s), known);
            return known;
        }
        (s.from, s.to) = (1, tries);
        return search(s);
    }

    /// The first counter from `s.from` up to `s.to` that gives the digest `s` asks for, or zero.
    /// The randomizer is the counter as a 16-byte number.
    function search(Search memory s) internal pure returns (uint32 found) {
        assembly ("memory-safe") {
            let mem := mload(0x40)
            mstore(mem, mload(s))
            mstore(add(mem, 0x20), mload(add(s, 0x20)))
            let len := mload(add(s, 0x40))
            let slot := add(mem, add(0x20, len))
            let size := add(0x30, len)
            // The digits past the 58th are the last twelve bits of the digest as a little-endian
            // integer: the high half of its 15th byte and its 16th.
            let mask := 0xf0ff
            let past := mload(add(s, 0x60))
            let any := eq(past, ANY_BIT)
            if any {
                mask := 0
                past := 0
            }
            let to := mload(add(s, 0xe0))
            for { let i := mload(add(s, 0xc0)) } lt(i, to) { i := add(i, 1) } {
                mstore(slot, shl(128, i))
                let d := shr(128, keccak256(mem, size))
                if xor(and(d, mask), past) { continue }
                if any { if iszero(and(d, 0xf0ff)) { continue } }
                let total := 0
                for { let k := 0 } lt(k, 128) { k := add(k, 2) } {
                    total := add(total, and(shr(k, d), 3))
                }
                if eq(eq(total, mload(add(s, 0x80))), mload(add(s, 0xa0))) {
                    found := i
                    break
                }
            }
        }
    }

    // --- The randomizers of the fixed cases --------------------------------------------------

    /// The leaf indices of `test_VerifiesWhatTheReferenceDoes`.
    function leaves() internal pure returns (uint32[16] memory) {
        return [
            uint32(0),
            0x00000001,
            0x000000ff,
            0x00000100,
            0x00008000,
            0x0000ffff,
            0x00010000,
            0x0001ffff,
            0x00ff00ff,
            0x12345678,
            0x5a5a5a5a,
            0x80000000,
            0xa5a5a5a5,
            0xdeadbeef,
            0xfffeffff,
            0xfffffffe
        ];
    }

    /// Prints `validCounters` and `closeCounters`, after a change to how the signatures are
    /// built. It takes a minute and more gas than a test has:
    ///   LEANXMSS_COUNTERS=true FOUNDRY_GAS_LIMIT=100000000000 \
    ///     forge test --match-test test_PrintCounters -vv
    function test_PrintCounters() public {
        vm.skip(!vm.envOr("LEANXMSS_COUNTERS", false));
        tries = type(uint32).max;
        uint32[16] memory indices = leaves();
        for (uint256 i; i < indices.length; i++) {
            (uint32[2] memory used,,,) = signatureAt(indices[i], indices[i], [uint32(0), 0]);
            emit log_string(row("valid", used));
        }
        for (uint256 i; i < 32; i++) {
            emit log_string(row("close", checkClose(closeCase(i), i, [uint32(0), 0])));
        }
    }

    function row(string memory table, uint32[2] memory used) internal pure returns (string memory) {
        return
            string.concat(
                table, " [uint32(", vm.toString(used[0]), "), ", vm.toString(used[1]), "],"
            );
    }

    /// The counters of the bottom and of the top randomizer of each signature of
    /// `test_VerifiesWhatTheReferenceDoes`.
    function validCounters() internal pure returns (uint32[2][16] memory) {
        return [
            [uint32(2695084), 343541],
            [uint32(2138992), 401684],
            [uint32(64870), 2508557],
            [uint32(188091), 734103],
            [uint32(50834), 964293],
            [uint32(739169), 881888],
            [uint32(164878), 171988],
            [uint32(1034421), 308775],
            [uint32(455059), 775331],
            [uint32(147433), 758337],
            [uint32(122793), 373665],
            [uint32(682812), 1623417],
            [uint32(1500104), 1664988],
            [uint32(2570454), 114418],
            [uint32(985726), 910735],
            [uint32(6364663), 1011631]
        ];
    }

    /// The same for each case of `test_RejectsADigestThatIsNotACodeword`.
    function closeCounters() internal pure returns (uint32[2][32] memory) {
        return [
            [uint32(318398), 39862],
            [uint32(45923), 580490],
            [uint32(649142), 589598],
            [uint32(1099889), 2868395],
            [uint32(927472), 52672],
            [uint32(45687), 873106],
            [uint32(406716), 643643],
            [uint32(1699395), 307907],
            [uint32(772117), 384351],
            [uint32(146820), 504645],
            [uint32(2920698), 144838],
            [uint32(404962), 1262866],
            [uint32(2), 27272],
            [uint32(112785), 759947],
            [uint32(3564402), 143733],
            [uint32(7605), 360771],
            [uint32(664093), 928983],
            [uint32(112106), 622618],
            [uint32(571395), 2560129],
            [uint32(977420), 40737],
            [uint32(57598), 553465],
            [uint32(499987), 230183],
            [uint32(613127), 1956246],
            [uint32(429391), 1009179],
            [uint32(241727), 509998],
            [uint32(534441), 629527],
            [uint32(1626827), 1306032],
            [uint32(1084919), 1697129],
            [uint32(2447312), 105],
            [uint32(1140520), 720031],
            [uint32(2489208), 1172890],
            [uint32(3027151), 2069]
        ];
    }
}
