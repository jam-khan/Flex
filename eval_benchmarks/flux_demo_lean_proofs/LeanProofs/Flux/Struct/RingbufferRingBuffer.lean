import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure RingbufferRingBuffer  where
  mkRingbufferRingBuffer₀ ::
    len : Int 
    hd : Int 
    tl : Int 
    num_enqueues : Int 
  deriving Inhabited
attribute [grind .] RingbufferRingBuffer.ext


end F
