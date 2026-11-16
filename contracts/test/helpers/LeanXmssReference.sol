// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;

/// @title LeanXmssReference
/// @notice The leanXMSS verifier written with loops, one layer at a time. `src/LeanXmss.sol` does
///         the same with its loops unrolled, and the tests check that the two agree.
/// @dev It follows the spec's order: the digest, the chains, the leaf and the path. It costs about
///      twice the gas of `LeanXmss`.
library LeanXmssReference {
    uint256 internal constant SIGNATURE_LENGTH = 2404;
    /// A layer of the signature: randomizer (16) ‖ 58 chain values (928) ‖ 16 siblings (256).
    uint256 internal constant LAYER_LENGTH = 1200;

    function verify(bytes32 publicKey, bytes32 message, bytes calldata signature)
        internal
        pure
        returns (bool)
    {
        if (signature.length != SIGNATURE_LENGTH) return false;
        (bool valid, bytes16 top) = root(publicKey, message, signature);
        return valid && top == bytes16(publicKey);
    }

    /// @notice The root that `signature` reaches from `message`, under the public parameter in the
    ///         low half of `publicKey`, and whether both layers' digests are codewords.
    function root(bytes32 publicKey, bytes32 message, bytes calldata signature)
        internal
        pure
        returns (bool valid, bytes16 top)
    {
        bytes16 bottom;
        (valid, bottom) = bottomRoot(publicKey, message, signature);
        if (!valid) return (false, 0);
        // The top layer signs the bottom tree's root with the key of that tree's number.
        return layerRoot(
            publicKey, 1, leafIndex(signature) >> 16, bottom, 16, signature[4 + LAYER_LENGTH:]
        );
    }

    /// @notice The root of the bottom tree that `signature` reaches from `message`, and whether
    ///         the bottom layer's digest is a codeword.
    function bottomRoot(bytes32 publicKey, bytes32 message, bytes calldata signature)
        internal
        pure
        returns (bool valid, bytes16 bottom)
    {
        return layerRoot(publicKey, 0, leafIndex(signature), message, 32, signature[4:]);
    }

    /// @notice The root each layer reaches and whether its digest is a codeword, without stopping
    ///         at a digest that isn't one. A test uses it for signatures that only the codeword
    ///         check rejects.
    function roots(bytes32 publicKey, bytes32 message, bytes calldata signature)
        internal
        pure
        returns (bool bottomValid, bytes16 bottom, bool topValid, bytes16 top)
    {
        uint32 leaf = leafIndex(signature);
        (bottomValid, bottom) = layerRoot(publicKey, 0, leaf, message, 32, signature[4:]);
        (topValid, top) =
            layerRoot(publicKey, 1, leaf >> 16, bottom, 16, signature[4 + LAYER_LENGTH:]);
    }

    function leafIndex(bytes calldata signature) internal pure returns (uint32) {
        uint32 le = uint32(bytes4(signature[:4]));
        return (le >> 24) | ((le >> 8) & 0xff00) | ((le << 8) & 0xff0000) | (le << 24);
    }

    /// @notice The root that layer `layer`'s signature `sig`, by key `key`, reaches from `signed`,
    ///         the first `len` bytes of a word, and whether its digest is a codeword. The root is
    ///         computed either way, from the digest's first 58 digits.
    function layerRoot(
        bytes32 publicKey,
        uint256 layer,
        uint256 key,
        bytes32 signed,
        uint256 len,
        bytes calldata sig
    ) internal pure returns (bool valid, bytes16 root_) {
        assembly ("memory-safe") {
            // A hash input starts with the word `P | A`: the public parameter, then the address
            // `[lo:4 | hi:3 | t + 32 step:1 | zero:8]`, the fields little-endian. In that word,
            // `lo` sits at bit 96, the level (the low byte of `hi`) at bit 88, the top layer's
            // flag (bit 23 of `hi`) at bit 79, the type at bit 64 and the step at bit 69. A hash
            // value is 16 bytes, kept in the high half of a word.
            //
            // The 64-byte inputs of the chain steps and the nodes are built in the scratch space
            // at 0, the digest's and the leaf's at the free memory pointer.

            /// The low four bytes of `x`, reversed: a 32-bit little-endian field to or from a
            /// number.
            function swap32(x) -> y {
                y := or(
                    or(shl(24, and(x, 0xff)), shl(8, and(x, 0xff00))),
                    or(and(shr(8, x), 0xff00), and(shr(24, x), 0xff))
                )
            }

            /// A 16-byte string read as a little-endian integer.
            function le128(x) -> y {
                y := or(
                    shl(8, and(x, 0x00ff00ff00ff00ff00ff00ff00ff00ff)),
                    and(shr(8, x), 0x00ff00ff00ff00ff00ff00ff00ff00ff)
                )
                y := or(
                    shl(16, and(y, 0x0000ffff0000ffff0000ffff0000ffff)),
                    and(shr(16, y), 0x0000ffff0000ffff0000ffff0000ffff)
                )
                y := or(
                    shl(32, and(y, 0x00000000ffffffff00000000ffffffff)),
                    and(shr(32, y), 0x00000000ffffffff00000000ffffffff)
                )
                y := or(shl(64, and(y, 0x0000000000000000ffffffffffffffff)), shr(64, y))
            }

            /// Whether the digest `d`, a little-endian integer, is a codeword: its two-bit digits
            /// past the 58th are zero and the others sum to 106.
            function isCodeword(d) -> r {
                if iszero(shr(116, d)) {
                    let sum := 0
                    for { let i := 0 } lt(i, 116) { i := add(i, 2) } {
                        sum := add(sum, and(shr(i, d), 3))
                    }
                    r := eq(sum, 106)
                }
            }

            /// The leaf that the chain values at `values` reach from the digits of `d`, its input
            /// built at `mem`. `pa` is `P | A` with `lo` and `hi` set.
            function wotsLeaf(mem, pa, d, values) -> leaf {
                mstore(mem, or(pa, shl(64, 2)))
                let mask := not(0xffffffffffffffffffffffffffffffff)
                for { let i := 0 } lt(i, 58) { i := add(i, 1) } {
                    // The chain index, a 16-byte little-endian integer after the value.
                    let index := shl(120, i)
                    let w := and(calldataload(add(values, shl(4, i))), mask)
                    // A step's address carries the position it leaves, from the chain's digit
                    // to the last one.
                    for { let p := and(shr(shl(1, i), d), 3) } lt(p, 3) { p := add(p, 1) } {
                        mstore(0, or(pa, or(shl(64, 1), shl(69, p))))
                        mstore(0x20, or(w, index))
                        w := and(keccak256(0, 0x40), mask)
                    }
                    // The 16 bytes after an end are zero, and the next end overwrites them.
                    mstore(add(add(mem, 0x20), shl(4, i)), w)
                }
                leaf := and(keccak256(mem, 960), mask)
            }

            /// The root that `node`, at index `e`, and the path at `ptr` reach. `pa` is `P | A`
            /// with only the top layer's flag set.
            function pathRoot(pa, e, node, ptr) -> r {
                let mask := not(0xffffffffffffffffffffffffffffffff)
                for { let level := 1 } lt(level, 17) { level := add(level, 1) } {
                    let sibling := and(calldataload(ptr), mask)
                    ptr := add(ptr, 16)
                    // The low bit of `e` says whether the node is the right child.
                    let left := node
                    let right := sibling
                    if and(e, 1) {
                        left := sibling
                        right := node
                    }
                    e := shr(1, e)
                    mstore(0, or(pa, or(shl(64, 3), or(shl(88, level), shl(96, swap32(e))))))
                    mstore(0x20, or(left, shr(128, right)))
                    node := and(keccak256(0, 0x40), mask)
                }
                r := node
            }

            let mem := mload(0x40)
            let pa := or(shl(128, publicKey), shl(79, layer))
            let paKey := or(pa, shl(96, swap32(key)))
            mstore(mem, or(paKey, shl(64, 12)))
            mstore(add(mem, 0x20), signed)
            mstore(add(mem, add(0x20, len)), shl(128, shr(128, calldataload(sig.offset))))
            let d := le128(shr(128, keccak256(mem, add(0x30, len))))
            valid := isCodeword(d)
            let leaf := wotsLeaf(mem, paKey, d, add(sig.offset, 16))
            root_ := pathRoot(pa, key, leaf, add(sig.offset, 944))
        }
    }
}
