#!/usr/bin/env python3
"""Writes src/LeanXmss.sol, the leanXMSS verifier.

The verifier is generated because its hot code is unrolled: one block per chain and one per level of a Merkle path,
each with its own constants. A loop costs about 60 gas per chain in counters, shifts and computed offsets, which is
more than the hash it runs. The comments in the generated file explain the code, and this script only says how each
constant is derived.

Run it from anywhere: `python3 contracts/scripts/generate-verifier.py`. With `--check` it writes nothing and fails
if the file differs from what it would write, which is what CI runs.
"""

import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUTPUT = os.path.join(ROOT, "src/LeanXmss.sol")
TEMPLATE = os.path.join(ROOT, "scripts/LeanXmss.sol.template")

CHAINS = 58
LEVELS = 16
SIGNATURE_LENGTH = 2404
# A layer of the signature: the randomizer, the chain values and the siblings.
LAYER_LENGTH = 16 + 16 * CHAINS + 16 * LEVELS
BOTTOM, TOP = 4, 4 + LAYER_LENGTH

# The memory layout. X, Y and Z hold the 64-byte input of a chain step that leaves position 2, 1 and 0. A step
# writes 16 bytes past its input, so Y and Z take 0x50 bytes each, and X's go over the free memory pointer.
X, Y, Z = 0x00, 0x80, 0xD0
LEAF = 0x120
LAYER = LEAF + 0x20
VALUES = LAYER + 16
SIBLINGS = VALUES + 16 * CHAINS
END = LAYER + LAYER_LENGTH

# The types of an address, in the address word (the type byte is at bit 64). A chain step's also has the position
# it leaves, times 32.
STEP = [(1 + 32 * position) << 64 for position in range(3)]
LEAF_TYPE, TREE_TYPE, DIGEST_TYPE = 2 << 64, 3 << 64, 12 << 64
TOP_LAYER = 1 << 79
# In an address word `lo` is at bits 96 to 127 and the level at bits 88 to 95.
LO, LEVEL = 96, 88
# Ones below `lo`, which a shift left by 8 to 23 moves over the level, so that the mask that takes the bits of
# `lo` also writes the level.
LEVEL_ONES = (1 << LEVEL) - (1 << (LEVEL - 23))


def word(n):
    """A 16-byte constant, with its leading zeros."""
    return f"0x{n:032x}"


def at(address):
    """A memory address."""
    return "0" if address == 0 else hex(address)


def digit_bit(chain):
    """Where the low bit of a chain's digit is in the digest, read as a big-endian number.

    The digest is a little-endian integer and chain `i` has its bits 2i and 2i + 1, so byte `i // 4` of the digest,
    which the big-endian reading puts at bit `120 - 8 * (i // 4)`.
    """
    return 120 - 8 * (chain // 4) + 2 * (chain % 4)


def chain_block(i):
    low = 1 << digit_bit(i)
    index = "0" if i == 0 else f"shl(248, {i})"

    def step(buffer, result):
        return [f"mstore({at(buffer + 0x20)}, v)", f"mstore({at(buffer + 0x30)}, {index})", result]

    return [
        f"// Chain {i}.",
        "{",
        f"let v := mload({hex(VALUES + 16 * i)})",
        f"if iszero(and(threes, {word(low)})) {{",
        f"if iszero(and(digits, {word(2 * low)})) {{",
        f"if iszero(and(digits, {word(low)})) {{",
        *step(Z, f"v := keccak256({at(Z)}, 0x40)"),
        "}",
        *step(Y, f"v := keccak256({at(Y)}, 0x40)"),
        "}",
        *step(X, f"v := keccak256({at(X)}, 0x40)"),
        "}",
        f"mstore({hex(LAYER + 16 * i)}, v)",
        "}",
    ]


def lo_bytes(values):
    """Four bytes in the place of `lo`, the first one in the highest byte."""
    return sum(v << (LO + 24 - 8 * j) for j, v in enumerate(values))


def node_address(level):
    """The expression of the `lo` and the level of a node's address, from `index`, after the statements it needs.

    `index` is the layer's leaf index as its little-endian bytes b0 b1 b2 b3, and the node's is that index shifted
    right by `level = 8q + r` bits. Byte j of the result is `b[j+q] >> r` with the low r bits of `b[j+q+1]` on top.
    Read as a number, the first comes from shifting `index` right by r, or left by 8 - r when q is 1, and the second
    from shifting it left by `8q + 16 - r`. A mask on each keeps the bits that belong to the byte.
    """
    q, r = divmod(level, 8)
    tag = level << LEVEL
    if r == 0:
        mask = lo_bytes([0xFF] * (4 - q) + [0] * q)
        return [], f"and(shl({8 * q}, index), {word(mask | tag)})"
    high = lo_bytes([0xFF >> r] * (4 - q) + [0] * q)
    low = lo_bytes([(0xFF << (8 - r)) & 0xFF] * (3 - q) + [0] * (1 + q))
    first = f"shr({r}, index)" if q == 0 else f"shl({8 - r}, index)"
    statements = [
        f"let high := and({first}, {word(high)})",
        f"let low := and(shl({8 * q + 16 - r}, index), {word(low | tag)})",
    ]
    return statements, "or(high, low)"


def path_levels(at_zero):
    out = []
    for level in range(1, LEVELS + 1):
        sibling = f"mload({hex(SIBLINGS + 16 * (level - 1))})"
        # Odd levels are built in X and even ones in Y, so a node is hashed from one buffer into the other.
        here, there = (X, Y) if level % 2 else (Y, X)
        node = "node" if level == 1 else f"keccak256({at(there)}, 0x40)"
        left, right = at(here + 0x20), at(here + 0x30)
        out.append(f"// Level {level}.")
        if at_zero:
            out += [f"mstore8({at(here + 0x14)}, {level})", f"mstore({left}, {node})", f"mstore({right}, {sibling})"]
            continue
        bit = level - 1
        mask = 1 << (LO + 24 - 8 * (bit // 8) + bit % 8)
        statements, address = node_address(level)
        store = f"mstore({at(here)}, or(tree, {address}))"
        out += ["{", *statements, store, "}"] if statements else [store]
        out += [
            f"switch and(index, {word(mask)})",
            "case 0 {",
            f"mstore({left}, {node})",
            f"mstore({right}, {sibling})",
            "}",
            "default {",
            f"mstore({left}, {sibling})",
            f"mstore({right}, {node})",
            "}",
        ]
    return out


def indent(lines, depth):
    out = []
    for line in lines:
        if line.startswith("}"):
            depth -= 1
        out.append("    " * depth + line if line else "")
        if line.endswith("{"):
            depth += 1
    return "\n".join(out)


def render():
    values = {
        "CHAINS": indent(sum((chain_block(i) for i in range(CHAINS)), []), 4),
        "PATH": indent(path_levels(False), 4),
        "PATH_AT_ZERO": indent(path_levels(True), 4),
        "X": at(X),
        "Y": at(Y),
        "Z": at(Z),
        "LEAF": hex(LEAF),
        "LAYER": hex(LAYER),
        "VALUES": hex(VALUES),
        "SIBLINGS": hex(SIBLINGS),
        "END": hex(END),
        "SAVED_LENGTH": hex(END - 0x80),
        "LEAF_LENGTH": str(32 + 16 * CHAINS),
        "LAYER_LENGTH": str(LAYER_LENGTH),
        "BOTTOM": str(BOTTOM),
        "TOP": str(TOP),
        "SIGNATURE_LENGTH": str(SIGNATURE_LENGTH),
        "STEP0": hex(STEP[0]),
        "STEP1": hex(STEP[1]),
        "STEP2": hex(STEP[2]),
        "LEAF_TYPE": hex(LEAF_TYPE),
        "DIGEST_TYPE": hex(DIGEST_TYPE),
        "TREE": hex(TREE_TYPE),
        "TOP_LAYER": hex(TOP_LAYER),
        "TOP_TREE": hex(TOP_LAYER | TREE_TYPE),
        "LO_MASK": word(0xFFFFFFFF << LO),
        "LEVEL_ONES": word(LEVEL_ONES),
    }
    with open(TEMPLATE) as f:
        text = f.read()
    for name, value in values.items():
        text = text.replace("{{" + name + "}}", value)
    assert "{{" not in text, text[text.index("{{") :][:40]
    return text


def main():
    text = render()
    if sys.argv[1:] == ["--check"]:
        with open(OUTPUT) as f:
            if f.read() != text:
                sys.exit("src/LeanXmss.sol is out of date: run scripts/generate-verifier.py")
        return
    assert not sys.argv[1:], "usage: generate-verifier.py [--check]"
    with open(OUTPUT, "w") as f:
        f.write(text)


if __name__ == "__main__":
    main()
