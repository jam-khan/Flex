import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.RingbufferRingBuffer
open Classical
set_option linter.unusedVariables false


namespace F



def RingbufferImpl__2__IsValid := 
 ∀ (s₀ : RingbufferRingBuffer),
  ∀ (index₀ : Int),
   (((RingbufferRingBuffer.num_enqueues s₀) < (RingbufferRingBuffer.len s₀)) -> (((RingbufferRingBuffer.tl s₀) = (RingbufferRingBuffer.num_enqueues s₀)) ∧ ((RingbufferRingBuffer.hd s₀) ≤ (RingbufferRingBuffer.tl s₀)))) ->
    ((0 < (RingbufferRingBuffer.len s₀)) ∧ ((RingbufferRingBuffer.hd s₀) < (RingbufferRingBuffer.len s₀)) ∧ ((RingbufferRingBuffer.tl s₀) < (RingbufferRingBuffer.len s₀))) ->
     (index₀ ≥ 0) ->
      ((RingbufferRingBuffer.hd s₀) ≥ 0) ->
       ((RingbufferRingBuffer.tl s₀) ≥ 0) ->
        ((RingbufferRingBuffer.len s₀) ≥ 0) ->
         ((((index₀ + (RingbufferRingBuffer.len s₀)) - (RingbufferRingBuffer.hd s₀)) ≥ 0)) ∧
         (((RingbufferRingBuffer.len s₀) ≠ 0))
         
end F
