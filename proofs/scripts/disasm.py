"""Read the bytecode of the verifier from Code.lean, and disassemble it."""

import re
from pathlib import Path

MODULE = Path(__file__).resolve().parents[1] / "LeanXmssEvmVerifierProofs"

# The names of the opcodes other than PUSH, DUP and SWAP that the generated lemmas walk through.
NAMES = {
    0x00: "STOP", 0x01: "ADD", 0x02: "MUL", 0x03: "SUB", 0x04: "DIV", 0x06: "MOD",
    0x10: "LT", 0x11: "GT", 0x14: "EQ", 0x15: "ISZERO", 0x16: "AND", 0x17: "OR", 0x18: "XOR",
    0x19: "NOT", 0x1A: "BYTE", 0x1B: "SHL", 0x1C: "SHR", 0x20: "KECCAK256",
    0x33: "CALLER", 0x34: "CALLVALUE", 0x35: "CALLDATALOAD", 0x36: "CALLDATASIZE",
    0x37: "CALLDATACOPY", 0x46: "CHAINID", 0x50: "POP", 0x51: "MLOAD", 0x52: "MSTORE",
    0x53: "MSTORE8", 0x56: "JUMP", 0x57: "JUMPI", 0x5A: "GAS", 0x5B: "JUMPDEST", 0x5E: "MCOPY",
    0xF3: "RETURN", 0xFA: "STATICCALL", 0xFD: "REVERT", 0xFE: "INVALID",
}

Instruction = tuple[int, str, str | None]


def read_code(path: Path = MODULE / "Code.lean") -> bytes:
    """The bytes of the code that a Lean file of the code holds as one hex literal."""
    text = path.read_text()
    size = int(re.search(r"def \w*CODE_SIZE : Nat := (\d+)", text).group(1))
    number = int(re.search(r"def \w*CODE_NUMBER : Nat :=\n\s*0x([0-9a-f]+)", text).group(1), 16)
    return number.to_bytes(size, "big")


def opcode_name(byte: int) -> str:
    """The name of an opcode, or OP and its byte for one that the lemmas never walk through."""
    if byte == 0x5F:
        return "PUSH0"
    if 0x60 <= byte <= 0x7F:
        return f"PUSH{byte - 0x5F}"
    if 0x80 <= byte <= 0x8F:
        return f"DUP{byte - 0x7F}"
    if 0x90 <= byte <= 0x9F:
        return f"SWAP{byte - 0x8F}"
    return NAMES.get(byte, f"OP{byte:02x}")


def disassemble(code: bytes) -> list[Instruction]:
    """Each instruction: its offset, its name and its push data in hex."""
    out, pc = [], 0
    while pc < len(code):
        name = opcode_name(code[pc])
        width = int(name[4:]) if name.startswith("PUSH") and name != "PUSH0" else 0
        data = code[pc + 1 : pc + 1 + width].hex() if width else None
        out.append((pc, name, data))
        pc += 1 + width
    return out
