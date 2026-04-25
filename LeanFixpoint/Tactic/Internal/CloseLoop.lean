import Lean
import Aesop

import LeanFixpoint.Core.Types
import LeanFixpoint.Core.Fusion
import LeanFixpoint.Elab.ToExpr
import LeanFixpoint.Elab.FromExpr
import LeanFixpoint.Monad
import LeanFixpoint.Tactic.Internal.Utils
import LeanFixpoint.Tactic.Closers

open Lean Elab Meta Tactic

/--
  Default leaf-closing strategy:
    `leafClosers` tactic.

  If you want to add support for more tactics
  strategies for default `leaf` closer, please
  add it in the `leafClosers` tactic.
-/
private def tryLeafClosers : TacticM Bool := do
  attemptTactic (evalTactic (← `(tactic| leafClosers)))

/--
  Strip one structural connective from the head of a goal:
  `∀`/`→` via `intro _`, or top-level `∧` via `and_intros`.
  Returns `true` if the goal was reshaped/decomposed, `false`
  if it is already in leaf form.
-/
private def tryDecomposeGoal : TacticM Bool := do
  let ty ← whnfR (← (← getMainGoal).getType)
  if ty.isConstOf ``True then
    evalTactic (← `(tactic| exact True.intro))
    return true
  if ty.isForall then
    evalTactic (← `(tactic| intro _))
    return true
  else if ty.isAppOfArity ``And 2 then
    evalTactic (← `(tactic| and_intros))
    return true
  else if ty.isAppOfArity ``Iff 2 then
    evalTactic (← `(tactic| constructor))
    return true
  else
    return false

/--
  This decomposes the hypotheses to allow for improved performance
  for closing the goal on the `leaf`.

  Strips one round of structure connectives from the **hypotheses**
  of the main goal: `∧`, `∨`, `∃`. Returns `true` if any hypothesis
  was decomposed, `false` if every hypothesis was already in the leaf
  form.

  Operates only on the main goal (not `any_goals`) or sub-goals
-/
private def tryDecomposeHypotheses : TacticM Bool :=
  -- attemptTactic (evalTactic (←
  --   `(tactic| repeat (first
  --       | split_hyp_ands
  --       | split_hyp_ors
  --       | split_hyp_exists)))
  pure true

/--
  Walk the goal list, decomposing each goal further into sub-goals/leaf form.
  The closer on the leaf is supplied by the caller as a `TacticM Bool` returing
  `true` iff it closed the main goal (state should already be rolled back on
  failure - use `attemptTactic`)

  `tryClose`: tactic passed by caller to try close a leaf goal.
-/
partial def closeLoopWith (tryClose : TacticM Bool) : TacticM Unit := do
  let goals ← getGoals
  match goals with
  | []        => return
  | g :: rest =>
      -- if goal could be decomposed further
      if ← tryDecomposeGoal then
        -- then, we loop further inside
        closeLoopWith tryClose

      -- if goal couldn't be decomposed or solved
      -- then, try decompose hypotheses before another attempt
      else if ← tryDecomposeHypotheses then
        closeLoopWith tryClose

      -- if goal is already in leaf form, couldn't be decomposed,
      -- and/or hypothesis couldn't be decomposed either
      else if ← tryClose then
        -- we apply `tryClose` and if closed
        -- then we go further on remaining goals
        closeLoopWith tryClose

      -- if leaf form but couldn't be closed
      else
        -- then, we leave it be and go try `close` remaining
        -- goals inside `rest`
        setGoals rest
        closeLoopWith tryClose
        setGoals (g :: (← getGoals))

/--
  Default-version for closeLoop:

  walk goals, decomposing then closing with
  the `leafClosers` strategy
-/
def closeLoop : TacticM Unit :=
  closeLoopWith tryLeafClosers

-- private partial def closeLoop : TacticM Unit := do
--   let goals ← getGoals
--   match goals with
--   | [] => pure ()
--   | g :: restGoals =>
--     let ty ← whnfR (← g.getType)
--     if ty.isForall then
--       evalTactic (← `(tactic| intro _))
--       closeLoop
--     else if ty.isAppOfArity ``And 2 then
--       evalTactic (← `(tactic| and_intros))
--       closeLoop
--     else
--       let closers := #[
--         `(tactic| omega),
--         `(tactic| grind),
--         `(tactic| aesop),
--         `(tactic| (constructor <;> grind)),
--         `(tactic| (simp_all; grind))
--       ]
--       let mut closed := false
--       for c in closers do
--         if !closed then
--           let b ← attemptTactic (evalTactic (← c))
--           if b then closed := true
--       if closed then
--         closeLoop
--       else
--         setGoals restGoals
--         closeLoop
--         let remaining ← getGoals
--         setGoals (g :: remaining)
