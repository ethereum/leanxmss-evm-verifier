#!/usr/bin/env python3
"""Write the runtime bytecodes that the proofs are about as Lean constants."""

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MODULE = ROOT / "proofs/LeanXmssEvmVerifierProofs"


@dataclass(frozen=True)
class Target:
    """One contract: its forge artifact, its Lean file, and the names of its constants."""

    contract: str
    artifact: Path
    output: Path
    prefix: str
    origin: str


TARGETS = (
    Target(
        "PQProofOfPossession",
        ROOT / "contracts/out/PQProofOfPossession.sol/PQProofOfPossession.json",
        MODULE / "Code.lean",
        "",
        "`contracts/foundry.toml`",
    ),
    Target(
        "LeanXmssHarness",
        ROOT / "proofs/harness/out/LeanXmssHarness.sol/LeanXmssHarness.json",
        MODULE / "HarnessCode.lean",
        "HARNESS_",
        "`proofs/harness/foundry.toml`, which are those of `contracts/foundry.toml`",
    ),
)

HEADER = """\
module

public import EthLib.Execution.Proofs.Evm.Logic.NatCode

/-!
# The runtime bytecode of `{contract}`

The code that the proofs are about, as `forge build` compiles it with the settings of
{origin}.

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


def render(target: Target, code: bytes) -> str:
    """The Lean file of a runtime bytecode."""
    digest = hashlib.sha256(code).hexdigest()
    size = len(code)
    p = target.prefix
    return (
        HEADER.format(contract=target.contract, origin=target.origin)
        + f"/-- The size of the code: {size} bytes. -/\n"
        + f"def {p}CODE_SIZE : Nat := {size}\n\n"
        + "/-- The code as one number, the first byte highest.\n\n"
        + "It is one literal on one line, which Lean elaborates at once.\n\n"
        + f"The SHA-256 of its bytes is `{digest}`. -/\n"
        + f"def {p}CODE_NUMBER : Nat :=\n  0x{code.hex()}\n\n"
        + f"/-- The runtime bytecode of `{target.contract}`. -/\n"
        + f"def {p}CODE : ByteArray := NatCode.ofNat {p}CODE_NUMBER {p}CODE_SIZE\n\n"
        + "end LeanXmssEvmVerifierProofs\n"
    )


def main() -> int:
    """Write the files, or with --check fail if one differs from what would be written."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if a file is stale")
    args = parser.parse_args()
    stale = False
    for target in TARGETS:
        text = render(target, runtime_bytes(target.artifact))
        if not args.check:
            target.output.write_text(text)
        elif target.output.read_text() != text:
            print(f"{target.output} is not the bytecode that forge builds", file=sys.stderr)
            stale = True
    return 1 if stale else 0


if __name__ == "__main__":
    sys.exit(main())
