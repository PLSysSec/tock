import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.AllocatorAppBreaks
open Classical

namespace F

@[ext]
structure AllocatorAppMemoryAllocator (t0 : Type) [Inhabited t0] where
  mkAllocatorAppMemoryAllocator₀ ::
    regions : (SmtMap Int t0) 
    breaks : AllocatorAppBreaks 


end F
