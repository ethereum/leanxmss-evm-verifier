import Lake
open Lake DSL

/-!
Lake build for the proofs that the bytecode of `PQProofOfPossession` does what its README says.

The EVM semantics, its program logic and leanXMSS come from EthLib, at the commit pinned below.
-/

package «LeanXmssEvmVerifierProofs»

-- EthLib, which fixes the Lean toolchain and Mathlib.
require «EthLib» from git "https://github.com/ethereum/EthLib" @ "d964c30789243c08f8bf1c43718b0c50056defaa"

@[default_target]
lean_lib «LeanXmssEvmVerifierProofs» where
  -- EthLib's modules use the module system, so the modules that import them do too.
  requiresModuleSystem := true
