import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.FSlice
import LeanProofs.User.Struct.FSlice
open Classical
set_option linter.unusedVariables false


namespace F

noncomputable def ringbuffer_fslice_set : {t0 : Type} -> [Inhabited t0] -> (FSlice t0) -> Int -> t0 -> (FSlice t0) := sorry


end F
