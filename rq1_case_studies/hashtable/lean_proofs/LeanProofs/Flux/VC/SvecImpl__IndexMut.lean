import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.OVec
import LeanProofs.User.Fun.SvecLen
import LeanProofs.User.Fun.SvecGet
open Classical

namespace F



def SvecImpl__IndexMut := 
 ∀ (index₀ : Int),
  (index₀ ≥ 0) ->
   ∀ (a'₁ : (OVec Int)),
    ((index₀ < (svec_len (t0 := Int) a'₁))) ∧
    (∀ (a'₂ : Int),
     (a'₂ = (svec_get (t0 := Int) a'₁ index₀)))
    
end F
