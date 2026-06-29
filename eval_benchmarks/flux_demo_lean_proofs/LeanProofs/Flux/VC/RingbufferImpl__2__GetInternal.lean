import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.RingbufferRingBuffer
open Classical
set_option linter.unusedVariables false


namespace F



def RingbufferImpl__2__GetInternal := 
 ∀ (s₀ : RingbufferRingBuffer),
  ∀ (index₀ : Int),
   (index₀ < (RingbufferRingBuffer.len s₀)) ->
    (((RingbufferRingBuffer.num_enqueues s₀) < (RingbufferRingBuffer.len s₀)) -> (((RingbufferRingBuffer.tl s₀) = (RingbufferRingBuffer.num_enqueues s₀)) ∧ ((RingbufferRingBuffer.hd s₀) ≤ (RingbufferRingBuffer.tl s₀)))) ->
     ((0 < (RingbufferRingBuffer.len s₀)) ∧ ((RingbufferRingBuffer.hd s₀) < (RingbufferRingBuffer.len s₀)) ∧ ((RingbufferRingBuffer.tl s₀) < (RingbufferRingBuffer.len s₀))) ->
      (index₀ ≥ 0) ->
       ((¬((((index₀ + (RingbufferRingBuffer.len s₀)) - (RingbufferRingBuffer.hd s₀)) % (RingbufferRingBuffer.len s₀)) < (if ((RingbufferRingBuffer.tl s₀) > (RingbufferRingBuffer.hd s₀)) then ((RingbufferRingBuffer.tl s₀) - (RingbufferRingBuffer.hd s₀)) else (if ((RingbufferRingBuffer.tl s₀) < (RingbufferRingBuffer.hd s₀)) then (((RingbufferRingBuffer.len s₀) - (RingbufferRingBuffer.hd s₀)) + (RingbufferRingBuffer.tl s₀)) else 0)))) ->
        ((RingbufferRingBuffer.hd s₀) ≥ 0) ->
         ((RingbufferRingBuffer.tl s₀) ≥ 0) ->
          (False = ((((index₀ + (RingbufferRingBuffer.len s₀)) - (RingbufferRingBuffer.hd s₀)) % (RingbufferRingBuffer.len s₀)) < (if ((RingbufferRingBuffer.tl s₀) > (RingbufferRingBuffer.hd s₀)) then ((RingbufferRingBuffer.tl s₀) - (RingbufferRingBuffer.hd s₀)) else (if ((RingbufferRingBuffer.tl s₀) < (RingbufferRingBuffer.hd s₀)) then (((RingbufferRingBuffer.len s₀) - (RingbufferRingBuffer.hd s₀)) + (RingbufferRingBuffer.tl s₀)) else 0))))) ∧
       (((((index₀ + (RingbufferRingBuffer.len s₀)) - (RingbufferRingBuffer.hd s₀)) % (RingbufferRingBuffer.len s₀)) < (if ((RingbufferRingBuffer.tl s₀) > (RingbufferRingBuffer.hd s₀)) then ((RingbufferRingBuffer.tl s₀) - (RingbufferRingBuffer.hd s₀)) else (if ((RingbufferRingBuffer.tl s₀) < (RingbufferRingBuffer.hd s₀)) then (((RingbufferRingBuffer.len s₀) - (RingbufferRingBuffer.hd s₀)) + (RingbufferRingBuffer.tl s₀)) else 0))) ->
        ((RingbufferRingBuffer.hd s₀) ≥ 0) ->
         ((RingbufferRingBuffer.tl s₀) ≥ 0) ->
          ((0 ≤ index₀)) ∧
          ((index₀ < (if ((RingbufferRingBuffer.num_enqueues s₀) < (RingbufferRingBuffer.len s₀)) then (RingbufferRingBuffer.num_enqueues s₀) else (RingbufferRingBuffer.len s₀))))
          )
       
end F
