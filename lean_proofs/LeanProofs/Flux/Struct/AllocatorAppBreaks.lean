import LeanProofs.Flux.Prelude
open Classical

namespace F

@[ext]
structure AllocatorAppBreaks  where
  mkAllocatorAppBreaks₀ ::
    memory_start : Int 
    memory_size : Int 
    app_break : Int 
    high_water_mark : Int 
    kernel_break : Int 
    flash_start : Int 
    flash_size : Int 


end F
