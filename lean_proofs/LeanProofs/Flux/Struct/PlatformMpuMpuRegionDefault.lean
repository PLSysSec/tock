import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.PlatformMpuPermissions
open Classical

namespace F

@[ext]
structure PlatformMpuMpuRegionDefault  where
  mkPlatformMpuMpuRegionDefault₀ ::
    start : Int 
    size : Int 
    perms : PlatformMpuPermissions 
    is_set : Prop 
    rnum : Int 


end F
