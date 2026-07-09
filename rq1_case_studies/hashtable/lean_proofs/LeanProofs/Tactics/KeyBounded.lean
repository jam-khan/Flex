import Lean

open Lean Meta Elab Tactic

macro "key_bounded" : tactic =>
  `(tactic | (and_intros ; apply Int.emod_nonneg ; omega ; apply Int.emod_lt_of_pos ; omega))
