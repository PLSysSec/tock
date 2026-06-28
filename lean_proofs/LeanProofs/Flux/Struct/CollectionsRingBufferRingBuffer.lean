import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Slc
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure CollectionsRingBufferRingBuffer (t0 : Type) [Inhabited t0] where
  mkCollectionsRingBufferRingBuffer₀ ::
    ring : (Slc t0) 
    hd : Int 
    tl : Int 


end F
