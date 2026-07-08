import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.OVec
import LeanProofs.User.Fun.SvecLen
open Classical

namespace F



def SvecImpl__Index := 
 ∀ (a'₀ : (OVec Int)),
  ∀ (index₀ : Int),
   (index₀ ≥ 0) ->
    (index₀ < (svec_len (t0 := Int) a'₀))
end F
