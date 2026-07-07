import Lean
import Aesop

open Lean Elab Meta Tactic

/-- Default `leaf` closing strategy.

A macro `leafClosers` as tactic that expands to "try each tactic in order,
succeed on the first that closes the goal, otherwise throw."

If you want to add any further tactics to help default leaf closing
strategy add below. -/

syntax "leafClosers" : tactic

macro_rules
  | `(tactic| leafClosers) =>
    `(tactic| first
        | omega                   -- decidable arithmetic, instant fail/succeed
        | grind                   -- general decision procedure
        | native_decide
        | bv_decide
        -- `simp_all`'s `maxRecDepth` is logged via diagnostics, not thrown,
        -- so `attemptTactic`/`first`'s catch can't swallow it. Re-add only
        -- behind `try` (e.g. `(try simp_all; grind)`) once verified per case.
        | (constructor <;> grind) -- commit to constructor (∃, ∨, structs)
        | aesop                   -- last resort: best-first search
      )
