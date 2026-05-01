import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.PlatformMpuPermissions
open Classical

namespace F

@[ext]
structure PlatformMpuDefaultGhost  where
  mkPlatformMpuDefaultGhost₀ ::
    start : Int 
    size : Int 
    permissions : PlatformMpuPermissions 


end F
