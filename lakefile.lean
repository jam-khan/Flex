import Lake
open Lake DSL

package «LeanFixpoint» where
  version := v!"0.1.0"

-- Core dependency: aesop is used as a goal-closer fallback in the tactics.
-- `Std` ships with the Lean toolchain, so it needs no `require`.
-- Pinned to the rev mathlib uses, so it stays compatible with the toolchain.
require aesop from git
  "https://github.com/leanprover-community/aesop" @ "3426969888a264d3f69b6f30ab50aa11f28eb38d"

-- Mathlib is needed ONLY by the handful of Liquid-fixpoint benchmarks that use
-- `Set`/`Finset`. It is opt-in so that downstream users of the LeanFixpoint
-- solver never have to fetch or build mathlib.
--   Enable with:  lake -Kbench update     (once, to fetch + pin mathlib)
--   then build/check benchmarks, e.g.:
--                 lake -Kbench env lean Benchmarks/Liquid-fixpoint/maps00.lean
meta if get_config? bench |>.isSome then
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "251d9c0ff4b58979698a7ec9f4ac58a92b95c01f"

@[default_target]
lean_lib «LeanFixpoint» where

lean_lib «Demo» where

lean_lib «Benchmarks» where

lean_exe «lean-fixpoint» where
  root := `Main
