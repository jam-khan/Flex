import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.RingbufferRingBuffer
open Classical
set_option linter.unusedVariables false


namespace F



def RingbufferImpl__2__Dequeue := 
 ∀ (s₀ : RingbufferRingBuffer),
  (((RingbufferRingBuffer.num_enqueues s₀) < (RingbufferRingBuffer.len s₀)) -> (((RingbufferRingBuffer.tl s₀) = (RingbufferRingBuffer.num_enqueues s₀)) ∧ ((RingbufferRingBuffer.hd s₀) ≤ (RingbufferRingBuffer.tl s₀)))) ->
   ((0 < (RingbufferRingBuffer.len s₀)) ∧ ((RingbufferRingBuffer.hd s₀) < (RingbufferRingBuffer.len s₀)) ∧ ((RingbufferRingBuffer.tl s₀) < (RingbufferRingBuffer.len s₀))) ->
    ((RingbufferRingBuffer.hd s₀) ≥ 0) ->
     ((RingbufferRingBuffer.tl s₀) ≥ 0) ->
      ((RingbufferRingBuffer.hd s₀) ≠ (RingbufferRingBuffer.tl s₀)) ->
       ((RingbufferRingBuffer.len s₀) ≥ 0) ->
        (((RingbufferRingBuffer.len s₀) ≠ 0)) ∧
        (((RingbufferRingBuffer.len s₀) ≠ 0) ->
         (((RingbufferRingBuffer.num_enqueues s₀) < (RingbufferRingBuffer.len s₀)) ->
          (((RingbufferRingBuffer.tl s₀) = (RingbufferRingBuffer.num_enqueues s₀))) ∧
          (((((RingbufferRingBuffer.hd s₀) + 1) % (RingbufferRingBuffer.len s₀)) ≤ (RingbufferRingBuffer.tl s₀)))
          ) ∧
         (((((RingbufferRingBuffer.hd s₀) + 1) % (RingbufferRingBuffer.len s₀)) < (RingbufferRingBuffer.len s₀)))
         )
        
end F
