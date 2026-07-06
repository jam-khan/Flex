import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Fun.AlistAseqKeyMatches
set_option linter.unusedVariables false


namespace F

@[simp, grind]
def alist_aseq_keys_unchanged_except_k : {t0 : Type} -> [Inhabited t0] -> {t1 : Type} -> [Inhabited t1] -> (ASeq t0 t1) -> (ASeq t0 t1) -> t0 -> Prop :=
  fun l1 l2 k => ∀ k' v, k' ≠ k → (alist_aseq_key_matches l1 k' v ↔ alist_aseq_key_matches l2 k' v)


end F
