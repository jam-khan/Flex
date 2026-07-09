import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.FSlice
import LeanProofs.Flux.Struct.RingbufferRingBuffer
import LeanProofs.User.Fun.RingbufferFsliceLen
open Classical
set_option linter.unusedVariables false


namespace F



def RingbufferImpl__1__New := 
 ∀ (len₀ : Int),
  ∀ (f₀ : (SmtMap Int Prop)),
   ∀ (e₀ : (FSlice Int)),
    (1 < len₀) ->
     (len₀ = (ringbuffer_fslice_len (t0 := Int) e₀)) ->
      (∀ (a'₀ : Int),
       ((0 ≤ a'₀) ∧ (a'₀ < (RingbufferRingBuffer.len (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀ e₀)))) ->
        ((((a'₀ + (RingbufferRingBuffer.len (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀ e₀))) - (RingbufferRingBuffer.hd (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀ e₀))) % (RingbufferRingBuffer.len (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀ e₀))) < (if ((RingbufferRingBuffer.tl (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀ e₀)) > (RingbufferRingBuffer.hd (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀ e₀))) then ((RingbufferRingBuffer.tl (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀ e₀)) - (RingbufferRingBuffer.hd (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀ e₀))) else (if ((RingbufferRingBuffer.tl (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀ e₀)) < (RingbufferRingBuffer.hd (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀ e₀))) then (((RingbufferRingBuffer.len (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀ e₀)) - (RingbufferRingBuffer.hd (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀ e₀))) + (RingbufferRingBuffer.tl (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀ e₀))) else 0))) ->
         (SmtMap_select (t0 := _) (t1 := _) f₀ a'₀)) ∧
      (((0 < len₀)) ∧
      ((0 < len₀))
      )
      
end F
