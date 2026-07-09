import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.FSlice
import LeanProofs.Flux.Struct.RingbufferRingBuffer
import LeanProofs.User.Fun.RingbufferFsliceLen
open Classical
set_option linter.unusedVariables false


namespace F



def RingbufferImpl__1__IsValid := 
 ∀ (s₀ : (RingbufferRingBuffer Int)),
  ∀ (index₀ : Int),
   (∀ (a'₀ : Int), (((0 ≤ a'₀) ∧ (a'₀ < (RingbufferRingBuffer.len (RingbufferRingBuffer.mkRingbufferRingBuffer₀ (RingbufferRingBuffer.len s₀) (RingbufferRingBuffer.hd s₀) (RingbufferRingBuffer.tl s₀) (RingbufferRingBuffer.init s₀) (RingbufferRingBuffer.elems s₀))))) -> (((((a'₀ + (RingbufferRingBuffer.len (RingbufferRingBuffer.mkRingbufferRingBuffer₀ (RingbufferRingBuffer.len s₀) (RingbufferRingBuffer.hd s₀) (RingbufferRingBuffer.tl s₀) (RingbufferRingBuffer.init s₀) (RingbufferRingBuffer.elems s₀)))) - (RingbufferRingBuffer.hd (RingbufferRingBuffer.mkRingbufferRingBuffer₀ (RingbufferRingBuffer.len s₀) (RingbufferRingBuffer.hd s₀) (RingbufferRingBuffer.tl s₀) (RingbufferRingBuffer.init s₀) (RingbufferRingBuffer.elems s₀)))) % (RingbufferRingBuffer.len (RingbufferRingBuffer.mkRingbufferRingBuffer₀ (RingbufferRingBuffer.len s₀) (RingbufferRingBuffer.hd s₀) (RingbufferRingBuffer.tl s₀) (RingbufferRingBuffer.init s₀) (RingbufferRingBuffer.elems s₀)))) < (if ((RingbufferRingBuffer.tl (RingbufferRingBuffer.mkRingbufferRingBuffer₀ (RingbufferRingBuffer.len s₀) (RingbufferRingBuffer.hd s₀) (RingbufferRingBuffer.tl s₀) (RingbufferRingBuffer.init s₀) (RingbufferRingBuffer.elems s₀))) > (RingbufferRingBuffer.hd (RingbufferRingBuffer.mkRingbufferRingBuffer₀ (RingbufferRingBuffer.len s₀) (RingbufferRingBuffer.hd s₀) (RingbufferRingBuffer.tl s₀) (RingbufferRingBuffer.init s₀) (RingbufferRingBuffer.elems s₀)))) then ((RingbufferRingBuffer.tl (RingbufferRingBuffer.mkRingbufferRingBuffer₀ (RingbufferRingBuffer.len s₀) (RingbufferRingBuffer.hd s₀) (RingbufferRingBuffer.tl s₀) (RingbufferRingBuffer.init s₀) (RingbufferRingBuffer.elems s₀))) - (RingbufferRingBuffer.hd (RingbufferRingBuffer.mkRingbufferRingBuffer₀ (RingbufferRingBuffer.len s₀) (RingbufferRingBuffer.hd s₀) (RingbufferRingBuffer.tl s₀) (RingbufferRingBuffer.init s₀) (RingbufferRingBuffer.elems s₀)))) else (if ((RingbufferRingBuffer.tl (RingbufferRingBuffer.mkRingbufferRingBuffer₀ (RingbufferRingBuffer.len s₀) (RingbufferRingBuffer.hd s₀) (RingbufferRingBuffer.tl s₀) (RingbufferRingBuffer.init s₀) (RingbufferRingBuffer.elems s₀))) < (RingbufferRingBuffer.hd (RingbufferRingBuffer.mkRingbufferRingBuffer₀ (RingbufferRingBuffer.len s₀) (RingbufferRingBuffer.hd s₀) (RingbufferRingBuffer.tl s₀) (RingbufferRingBuffer.init s₀) (RingbufferRingBuffer.elems s₀)))) then (((RingbufferRingBuffer.len (RingbufferRingBuffer.mkRingbufferRingBuffer₀ (RingbufferRingBuffer.len s₀) (RingbufferRingBuffer.hd s₀) (RingbufferRingBuffer.tl s₀) (RingbufferRingBuffer.init s₀) (RingbufferRingBuffer.elems s₀))) - (RingbufferRingBuffer.hd (RingbufferRingBuffer.mkRingbufferRingBuffer₀ (RingbufferRingBuffer.len s₀) (RingbufferRingBuffer.hd s₀) (RingbufferRingBuffer.tl s₀) (RingbufferRingBuffer.init s₀) (RingbufferRingBuffer.elems s₀)))) + (RingbufferRingBuffer.tl (RingbufferRingBuffer.mkRingbufferRingBuffer₀ (RingbufferRingBuffer.len s₀) (RingbufferRingBuffer.hd s₀) (RingbufferRingBuffer.tl s₀) (RingbufferRingBuffer.init s₀) (RingbufferRingBuffer.elems s₀)))) else 0))) -> (SmtMap_select (t0 := _) (t1 := _) (RingbufferRingBuffer.init s₀) a'₀)))) ->
    ((1 < (RingbufferRingBuffer.len s₀)) ∧ (0 ≤ (RingbufferRingBuffer.hd s₀)) ∧ ((RingbufferRingBuffer.hd s₀) < (RingbufferRingBuffer.len s₀)) ∧ (0 ≤ (RingbufferRingBuffer.tl s₀)) ∧ ((RingbufferRingBuffer.tl s₀) < (RingbufferRingBuffer.len s₀)) ∧ ((RingbufferRingBuffer.len s₀) = (ringbuffer_fslice_len (t0 := Int) (RingbufferRingBuffer.elems s₀)))) ->
     (index₀ ≥ 0) ->
      ((RingbufferRingBuffer.hd s₀) ≥ 0) ->
       ((RingbufferRingBuffer.tl s₀) ≥ 0) ->
        ((RingbufferRingBuffer.len s₀) ≥ 0) ->
         ((((index₀ + (RingbufferRingBuffer.len s₀)) - (RingbufferRingBuffer.hd s₀)) ≥ 0)) ∧
         (((RingbufferRingBuffer.len s₀) ≠ 0))
         
end F
