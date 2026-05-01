import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.PlatformMpuMpuRegionDefault
import LeanProofs.Flux.Struct.PlatformMpuPermissions
import LeanProofs.Flux.Fun.NumImplMAX
open Classical

namespace F



def PlatformMpuImpl__Start := 
 ∀ (r₀ : PlatformMpuMpuRegionDefault),
  ((PlatformMpuMpuRegionDefault.is_set r₀) -> (((0 ≤ (PlatformMpuMpuRegionDefault.size r₀)) ∧ ((PlatformMpuMpuRegionDefault.size r₀) ≤ num_impl__MAX)) ∧ ((0 ≤ ((PlatformMpuMpuRegionDefault.start r₀) + (PlatformMpuMpuRegionDefault.size r₀))) ∧ (((PlatformMpuMpuRegionDefault.start r₀) + (PlatformMpuMpuRegionDefault.size r₀)) ≤ num_impl__MAX)))) ->
   ((PlatformMpuMpuRegionDefault.rnum r₀) ≥ 0) ->
    ((PlatformMpuMpuRegionDefault.rnum r₀) ≤ 18446744073709551615) ->
     ∀ (a'₀ : Int),
      (a'₀ = (PlatformMpuMpuRegionDefault.start r₀)) ->
       ((PlatformMpuMpuRegionDefault.start r₀) = a'₀)
end F
