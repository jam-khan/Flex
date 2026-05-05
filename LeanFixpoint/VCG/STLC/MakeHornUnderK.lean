import LeanFixpoint.VCG.STLC.Soundness
import LeanFixpoint.Tactic.Hoist

-- Applies `under_exists` once, then dispatches `check_sound` inside it.
-- `args` (optional, default empty) are extra lemmas passed to `simp`.
macro "make_horn_under_k" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    under_exists =>
      apply check_sound
      · repeat (first | unfold check | unfold synth)
        simp [$args,*]; rfl
      focus simp)

macro "make_horn_under_k" : tactic => `(tactic| make_horn_under_k [])
