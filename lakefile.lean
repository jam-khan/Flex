import Lake
open Lake DSL

package «Flex» where
  version := v!"0.1.0"

-- The only dependency: aesop, a goal-closer fallback in the tactics.
-- `Std` ships with the Lean toolchain, so it needs no `require`.
-- Flex (solver, benchmarks, and demos) is mathlib-free.
require aesop from git
  "https://github.com/leanprover-community/aesop" @ "3426969888a264d3f69b6f30ab50aa11f28eb38d"

@[default_target]
lean_lib «Flex» where

lean_lib «Demo» where

lean_lib «Benchmarks» where

lean_exe «flex» where
  root := `Main
