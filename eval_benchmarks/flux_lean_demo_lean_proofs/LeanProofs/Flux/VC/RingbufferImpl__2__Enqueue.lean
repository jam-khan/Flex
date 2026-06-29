import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.RingbufferRingBuffer
open Classical
set_option linter.unusedVariables false


namespace F



def RingbufferImpl__2__Enqueue := 
 ∀ (s₀ : RingbufferRingBuffer),
  ∀ (val₀ : Int),
   (∀ (a'₁ : Int), (((0 ≤ a'₁) ∧ (a'₁ < (if ((RingbufferRingBuffer.num_enqueues s₀) < (RingbufferRingBuffer.len s₀)) then (RingbufferRingBuffer.num_enqueues s₀) else (RingbufferRingBuffer.len s₀)))) -> (SmtMap_select (t0 := _) (t1 := _) (RingbufferRingBuffer.init s₀) a'₁))) ->
    (((RingbufferRingBuffer.num_enqueues s₀) < (RingbufferRingBuffer.len s₀)) -> (((RingbufferRingBuffer.tl s₀) = (RingbufferRingBuffer.num_enqueues s₀)) ∧ ((RingbufferRingBuffer.hd s₀) ≤ (RingbufferRingBuffer.tl s₀)))) ->
     ((0 < (RingbufferRingBuffer.len s₀)) ∧ (0 ≤ (RingbufferRingBuffer.hd s₀)) ∧ ((RingbufferRingBuffer.hd s₀) < (RingbufferRingBuffer.len s₀)) ∧ (0 ≤ (RingbufferRingBuffer.tl s₀)) ∧ ((RingbufferRingBuffer.tl s₀) < (RingbufferRingBuffer.len s₀)) ∧ (0 ≤ (RingbufferRingBuffer.num_enqueues s₀))) ->
      ((RingbufferRingBuffer.hd s₀) ≠ (((RingbufferRingBuffer.tl s₀) + 1) % (RingbufferRingBuffer.len s₀))) ->
       ((RingbufferRingBuffer.hd s₀) ≥ 0) ->
        ((RingbufferRingBuffer.tl s₀) ≥ 0) ->
         ((RingbufferRingBuffer.len s₀) ≥ 0) ->
          (((RingbufferRingBuffer.len s₀) ≠ 0)) ∧
          (((RingbufferRingBuffer.len s₀) ≠ 0) ->
           (∀ (a'₂ : Int),
            ((0 ≤ a'₂) ∧ (a'₂ < (if (((RingbufferRingBuffer.num_enqueues s₀) + 1) < (RingbufferRingBuffer.len s₀)) then ((RingbufferRingBuffer.num_enqueues s₀) + 1) else (RingbufferRingBuffer.len s₀)))) ->
             (SmtMap_select (t0 := _) (t1 := _) (SmtMap_store (t0 := _) (t1 := _) (RingbufferRingBuffer.init s₀) (RingbufferRingBuffer.tl s₀) True) a'₂)) ∧
           ((((RingbufferRingBuffer.num_enqueues s₀) + 1) < (RingbufferRingBuffer.len s₀)) ->
            (((((RingbufferRingBuffer.tl s₀) + 1) % (RingbufferRingBuffer.len s₀)) = ((RingbufferRingBuffer.num_enqueues s₀) + 1))) ∧
            (((RingbufferRingBuffer.hd s₀) ≤ (((RingbufferRingBuffer.tl s₀) + 1) % (RingbufferRingBuffer.len s₀))))
            ) ∧
           (((0 ≤ (((RingbufferRingBuffer.tl s₀) + 1) % (RingbufferRingBuffer.len s₀)))) ∧
           (((((RingbufferRingBuffer.tl s₀) + 1) % (RingbufferRingBuffer.len s₀)) < (RingbufferRingBuffer.len s₀))) ∧
           ((0 ≤ ((RingbufferRingBuffer.num_enqueues s₀) + 1)))
           )
           )
          
end F
