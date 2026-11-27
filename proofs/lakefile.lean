import Lake
open Lake DSL

/-!
Lake build for the proofs that the bytecode of `PQProofOfPossession` does what its README says.

The EVM semantics, its program logic and leanXMSS come from EthLib, at the commit pinned below.
-/

package «LeanXmssEvmVerifierProofs»

-- EthLib, which fixes the Lean toolchain and Mathlib.
require «EthLib» from git "https://github.com/ethereum/EthLib" @ "6abbac2345411d13abffa60ff29b0a1320775151"

@[default_target]
lean_lib «LeanXmssEvmVerifierProofs» where
  -- EthLib's modules use the module system, so the modules that import them do too.
  requiresModuleSystem := true
