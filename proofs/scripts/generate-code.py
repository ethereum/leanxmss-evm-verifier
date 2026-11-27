#!/usr/bin/env python3
"""Write the runtime bytecode of PQProofOfPossession as the Lean constant the proofs are about."""

import argparse
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ARTIFACT = ROOT / "contracts/out/PQProofOfPossession.sol/PQProofOfPossession.json"
OUTPUT = ROOT / "proofs/LeanXmssEvmVerifierProofs/Code.lean"

# Bytes per line of the number: 40 bytes are 80 hex digits, which fit in 100 columns.
CHUNK = 40

HEADER = """\
module

public import EthLib.Execution.Proofs.Evm.Logic.NatCode

/-!
# The runtime bytecode of `PQProofOfPossession`

The code that the proofs are about, as `forge build` compiles it with the settings of
`contracts/foundry.toml`.

`proofs/scripts/generate-code.py` writes this file, and CI fails if it differs from what the script
writes from a fresh build.

The code is stored as one number, the big-endian number of its bytes, so a fact about a byte
costs about the same at every position.
-/

@[expose] public section

namespace LeanXmssEvmVerifierProofs

open EthLib.Execution.Evm.Logic

"""


def runtime_bytes(artifact: Path) -> bytes:
    """The deployed bytecode of a forge artifact."""
    obj = json.loads(artifact.read_text())["deployedBytecode"]["object"]
    return bytes.fromhex(obj.removeprefix("0x"))


def render(code: bytes) -> str:
    """The Lean file of a runtime bytecode."""
    digest = hashlib.sha256(code).hexdigest()
    size = len(code)
    terms = []
    for start in range(0, size, CHUNK):
        chunk = code[start : start + CHUNK]
        shift = size - start - len(chunk)
        term = f"0x{chunk.hex()}"
        terms.append(f"{term} * 256 ^ {shift}" if shift else term)
    body = " +\n  ".join(terms)
    return (
        HEADER
        + f"/-- The size of the code: {size} bytes. -/\n"
        + f"def CODE_SIZE : Nat := {size}\n\n"
        + "/-- The code as one number, the first byte highest, in runs of 40 bytes.\n\n"
        + f"The SHA-256 of its bytes is `{digest}`. -/\n"
        + f"def CODE_NUMBER : Nat :=\n  {body}\n\n"
        + "/-- The runtime bytecode of `PQProofOfPossession`. -/\n"
        + "def CODE : ByteArray := NatCode.ofNat CODE_NUMBER CODE_SIZE\n\n"
        + "end LeanXmssEvmVerifierProofs\n"
    )


def main() -> int:
    """Write the file, or with --check fail if it differs from what would be written."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if the file is stale")
    parser.add_argument("--artifact", type=Path, default=ARTIFACT, help="forge artifact")
    args = parser.parse_args()
    text = render(runtime_bytes(args.artifact))
    if args.check:
        if OUTPUT.read_text() != text:
            print(f"{OUTPUT} is not the bytecode that forge builds", file=sys.stderr)
            return 1
        return 0
    OUTPUT.write_text(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
