import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.RingbufferRingBuffer
open Classical
set_option linter.unusedVariables false


namespace F



def RingbufferImpl__1__New := 
 ∀ (len₀ : Int),
  ∀ (f₀ : (SmtMap Int Prop)),
   (0 < len₀) ->
    ∀ (a'₀ : Int),
     ((0 ≤ a'₀) ∧ (a'₀ < (RingbufferRingBuffer.len (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀)))) ->
      ((((a'₀ + (RingbufferRingBuffer.len (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀))) - (RingbufferRingBuffer.hd (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀))) % (RingbufferRingBuffer.len (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀))) < (if ((RingbufferRingBuffer.tl (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀)) > (RingbufferRingBuffer.hd (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀))) then ((RingbufferRingBuffer.tl (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀)) - (RingbufferRingBuffer.hd (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀))) else (if ((RingbufferRingBuffer.tl (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀)) < (RingbufferRingBuffer.hd (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀))) then (((RingbufferRingBuffer.len (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀)) - (RingbufferRingBuffer.hd (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀))) + (RingbufferRingBuffer.tl (RingbufferRingBuffer.mkRingbufferRingBuffer₀ len₀ 0 0 f₀))) else 0))) ->
       (SmtMap_select (t0 := _) (t1 := _) f₀ a'₀)
end F
