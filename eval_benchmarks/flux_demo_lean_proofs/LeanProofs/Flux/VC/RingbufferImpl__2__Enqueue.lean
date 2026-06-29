import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.RingbufferRingBuffer
open Classical
set_option linter.unusedVariables false


namespace F



def RingbufferImpl__2__Enqueue := 
 ∀ (s₀ : RingbufferRingBuffer),
  ∀ (val₀ : Int),
   (((RingbufferRingBuffer.num_enqueues s₀) < (RingbufferRingBuffer.len s₀)) -> (((RingbufferRingBuffer.tl s₀) = (RingbufferRingBuffer.num_enqueues s₀)) ∧ ((RingbufferRingBuffer.hd s₀) ≤ (RingbufferRingBuffer.tl s₀)))) ->
    ((0 < (RingbufferRingBuffer.len s₀)) ∧ ((RingbufferRingBuffer.hd s₀) < (RingbufferRingBuffer.len s₀)) ∧ ((RingbufferRingBuffer.tl s₀) < (RingbufferRingBuffer.len s₀))) ->
     ((RingbufferRingBuffer.hd s₀) ≠ (((RingbufferRingBuffer.tl s₀) + 1) % (RingbufferRingBuffer.len s₀))) ->
      ((RingbufferRingBuffer.hd s₀) ≥ 0) ->
       ((RingbufferRingBuffer.tl s₀) ≥ 0) ->
        ((RingbufferRingBuffer.len s₀) ≥ 0) ->
         (((RingbufferRingBuffer.len s₀) ≠ 0)) ∧
         (((RingbufferRingBuffer.len s₀) ≠ 0) ->
          (∀ (j₀ : Int),
           (((j₀ = (RingbufferRingBuffer.tl s₀)) ∨ ((0 ≤ j₀) ∧ (j₀ < (if ((RingbufferRingBuffer.num_enqueues s₀) < (RingbufferRingBuffer.len s₀)) then (RingbufferRingBuffer.num_enqueues s₀) else (RingbufferRingBuffer.len s₀))))) = ((0 ≤ j₀) ∧ (j₀ < (if (((RingbufferRingBuffer.num_enqueues s₀) + 1) < (RingbufferRingBuffer.len s₀)) then ((RingbufferRingBuffer.num_enqueues s₀) + 1) else (RingbufferRingBuffer.len s₀)))))) ∧
          ((((RingbufferRingBuffer.num_enqueues s₀) + 1) < (RingbufferRingBuffer.len s₀)) ->
           (((((RingbufferRingBuffer.tl s₀) + 1) % (RingbufferRingBuffer.len s₀)) = ((RingbufferRingBuffer.num_enqueues s₀) + 1))) ∧
           (((RingbufferRingBuffer.hd s₀) ≤ (((RingbufferRingBuffer.tl s₀) + 1) % (RingbufferRingBuffer.len s₀))))
           ) ∧
          (((((RingbufferRingBuffer.tl s₀) + 1) % (RingbufferRingBuffer.len s₀)) < (RingbufferRingBuffer.len s₀)))
          )
         
end F
