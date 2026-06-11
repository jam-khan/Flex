import Lake
open Lake DSL

package «LeanFixpoint» where
  version := v!"0.1.0"

-- Core dependency: aesop is used as a goal-closer fallback in the tactics.
-- `Std` ships with the Lean toolchain, so it needs no `require`.
-- Pinned to the rev mathlib uses, so it stays compatible with the toolchain.
require aesop from git
  "https://github.com/leanprover-community/aesop" @ "3426969888a264d3f69b6f30ab50aa11f28eb38d"

-- Mathlib is needed by the handful of Liquid-fixpoint benchmarks that use
-- `Set`/`Finset`. Run `lake exe cache get` after `lake update` to download
-- prebuilt oleans instead of compiling from scratch.
--require mathlib from git
--  "https://github.com/leanprover-community/mathlib4" @ "251d9c0ff4b58979698a7ec9f4ac58a92b95c01f"

@[default_target]
lean_lib «LeanFixpoint» where

lean_lib «Demo» where

lean_lib «Benchmarks» where

lean_exe «lean-fixpoint» where
  root := `Main
