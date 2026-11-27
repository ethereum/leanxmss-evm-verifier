"""Write Block.lean: the verifier as one block, with the masks of its relocated jump targets."""

import argparse
import sys

from disasm import ENTRY, MODULE, disassemble, read_code

# The first byte of the verifier in the harness, from the disassembly of its dispatcher.
HARNESS_ENTRY = 0x67

OUTPUT = MODULE / "Block.lean"

HEADER = """\
module

public import LeanXmssEvmVerifierProofs.Code
public import LeanXmssEvmVerifierProofs.HarnessCode
public import EthLib.Execution.Proofs.Evm.Logic.Relocated

/-!
# The verifier as one block of code, at any offset

`PQProofOfPossession` and the harness hold the same verifier, at different offsets.

The bytes of the two copies differ only in the PUSH2 data of its jump targets.

Each is the position of the target in the verifier plus the offset of the verifier.

`proofs/scripts/generate-block.py` writes this file from the two codes, and CI fails if it differs.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Execution.Evm.Logic

"""


def block_of(code: bytes, harness: bytes) -> tuple[bytes, int, int, int]:
    """The verifier with its targets as positions in it, and its masks: fixed, relocated, dest."""
    shift = ENTRY - HARNESS_ENTRY
    by_pc = {pc: (name, data) for pc, name, data in disassemble(harness)}
    block, fixed, reloc, dest = bytearray(), 0, 0, 0
    for pc, name, data in disassemble(code):
        if pc < ENTRY:
            continue
        other = by_pc.get(pc - shift)
        # The verifier ends at the first opcode where the two codes differ.
        if other is None or other[0] != name:
            break
        i = pc - ENTRY
        width = len(data) // 2 if data else 0
        piece = bytearray(code[pc : pc + 1 + width])
        fixed |= ((1 << (1 + width)) - 1) << i
        if name == "JUMPDEST":
            dest |= 1 << i
        if data != other[1]:
            # A relocated PUSH2: the same target, `shift` bytes later.
            target = int(data, 16)
            assert name == "PUSH2" and target - int(other[1], 16) == shift, (hex(pc), name)
            assert ENTRY <= target, hex(pc)
            piece[1:3] = (target - ENTRY).to_bytes(2, "big")
            fixed &= ~(3 << (i + 1))
            reloc |= 1 << i
        block += piece
    for i in range(len(block)):
        if reloc >> i & 1:
            # Each target is a JUMPDEST of the block.
            assert dest >> int.from_bytes(block[i + 1 : i + 3], "big") & 1, hex(ENTRY + i)
    return bytes(block), fixed, reloc, dest


def render() -> str:
    """The text of Block.lean."""
    block, fixed, reloc, dest = block_of(read_code(), read_code(MODULE / "HarnessCode.lean"))
    return (
        HEADER
        + f"/-- The size of the verifier: {len(block)} bytes. -/\n"
        + f"def BLOCK_SIZE : Nat := {len(block)}\n\n"
        + "/-- The verifier as one number, the first byte highest, each target a position in it. -/\n"
        + f"def BLOCK_NUMBER : Nat :=\n  0x{block.hex()}\n\n"
        + "/-- The verifier, with each jump target a position in it. -/\n"
        + f"def BLOCK : ByteArray := NatCode.ofNat BLOCK_NUMBER {len(block)}\n\n"
        + "/-- Bit `i` is set when byte `i` of the verifier is the same in every copy. -/\n"
        + f"def BLOCK_FIXED : Nat :=\n  0x{fixed:x}\n\n"
        + "/-- Bit `i` is set when byte `i` is a PUSH2 of a jump target. -/\n"
        + f"def BLOCK_RELOC : Nat :=\n  0x{reloc:x}\n\n"
        + "/-- Bit `i` is set when byte `i` is a JUMPDEST. -/\n"
        + f"def BLOCK_DEST : Nat :=\n  0x{dest:x}\n\n"
        + "/-- The code holds the verifier from `base`, its targets moved by `base`.\n\n"
        + "Each lemma about the verifier takes it as an instance, so a use finds it alone. -/\n"
        + "class VerifierCode (code : ByteArray) (base : Nat) : Prop where\n"
        + "  /-- The bytes of the code from `base`. -/\n"
        + "  relocated : Relocated code base BLOCK BLOCK_FIXED BLOCK_RELOC BLOCK_DEST\n\n"
        + f"/-- `PQProofOfPossession` holds the verifier from byte {ENTRY:#x}. -/\n"
        + f"instance verifierCode : VerifierCode CODE {ENTRY:#x} :=\n"
        + "  ⟨relocated_ofNat (by decide +kernel)⟩\n\n"
        + f"/-- The harness holds the verifier from byte {HARNESS_ENTRY:#x}. -/\n"
        + f"instance harnessVerifierCode : VerifierCode HARNESS_CODE {HARNESS_ENTRY:#x} :=\n"
        + "  ⟨relocated_ofNat (by decide +kernel)⟩\n\n"
        + "end LeanXmssEvmVerifierProofs\n"
    )


def main() -> int:
    """Write the file, or with --check fail if it differs from what would be written."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if the file is stale")
    args = parser.parse_args()
    text = render()
    if not args.check:
        OUTPUT.write_text(text)
        return 0
    if not OUTPUT.exists() or OUTPUT.read_text() != text:
        print(f"{OUTPUT} is not the verifier of the two codes", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
