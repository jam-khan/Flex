import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.RingbufferRingBuffer
open Classical
set_option linter.unusedVariables false


namespace F



def RingbufferImpl__2__Len := 
 ∀ (s₀ : RingbufferRingBuffer),
  (((RingbufferRingBuffer.num_enqueues s₀) < (RingbufferRingBuffer.len s₀)) -> (((RingbufferRingBuffer.tl s₀) = (RingbufferRingBuffer.num_enqueues s₀)) ∧ ((RingbufferRingBuffer.hd s₀) ≤ (RingbufferRingBuffer.tl s₀)))) ->
   ((0 < (RingbufferRingBuffer.len s₀)) ∧ ((RingbufferRingBuffer.hd s₀) < (RingbufferRingBuffer.len s₀)) ∧ ((RingbufferRingBuffer.tl s₀) < (RingbufferRingBuffer.len s₀))) ->
    ((RingbufferRingBuffer.hd s₀) ≥ 0) ->
     ((RingbufferRingBuffer.tl s₀) ≥ 0) ->
      ((¬((RingbufferRingBuffer.tl s₀) > (RingbufferRingBuffer.hd s₀))) ->
       ((¬((RingbufferRingBuffer.tl s₀) < (RingbufferRingBuffer.hd s₀))) ->
        (0 = (if ((RingbufferRingBuffer.tl s₀) > (RingbufferRingBuffer.hd s₀)) then ((RingbufferRingBuffer.tl s₀) - (RingbufferRingBuffer.hd s₀)) else (if ((RingbufferRingBuffer.tl s₀) < (RingbufferRingBuffer.hd s₀)) then (((RingbufferRingBuffer.len s₀) - (RingbufferRingBuffer.hd s₀)) + (RingbufferRingBuffer.tl s₀)) else 0)))) ∧
       (((RingbufferRingBuffer.tl s₀) < (RingbufferRingBuffer.hd s₀)) ->
        ((RingbufferRingBuffer.len s₀) ≥ 0) ->
         ((((RingbufferRingBuffer.len s₀) - (RingbufferRingBuffer.hd s₀)) ≥ 0)) ∧
         (((((RingbufferRingBuffer.len s₀) - (RingbufferRingBuffer.hd s₀)) + (RingbufferRingBuffer.tl s₀)) = (if ((RingbufferRingBuffer.tl s₀) > (RingbufferRingBuffer.hd s₀)) then ((RingbufferRingBuffer.tl s₀) - (RingbufferRingBuffer.hd s₀)) else (((RingbufferRingBuffer.len s₀) - (RingbufferRingBuffer.hd s₀)) + (RingbufferRingBuffer.tl s₀)))))
         )
       ) ∧
      (((RingbufferRingBuffer.tl s₀) > (RingbufferRingBuffer.hd s₀)) ->
       (((RingbufferRingBuffer.tl s₀) - (RingbufferRingBuffer.hd s₀)) ≥ 0))
      
end F
