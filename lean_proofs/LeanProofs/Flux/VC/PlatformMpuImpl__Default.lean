import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.PlatformMpuDefaultGhost
import LeanProofs.Flux.Struct.PlatformMpuPermissions
import LeanProofs.Flux.Fun.NumImplMAX
open Classical

namespace F



def PlatformMpuImpl__Default := 
 ∀ (rnum₀ : Int),
  (rnum₀ ≥ 0) ->
   (rnum₀ ≤ 18446744073709551615) ->
    ∀ (a'₀ : PlatformMpuDefaultGhost),
     False ->
      ((0 ≤ (PlatformMpuDefaultGhost.size a'₀))) ∧
      (((PlatformMpuDefaultGhost.size a'₀) ≤ num_impl__MAX)) ∧
      ((0 ≤ ((PlatformMpuDefaultGhost.start a'₀) + (PlatformMpuDefaultGhost.size a'₀)))) ∧
      ((((PlatformMpuDefaultGhost.start a'₀) + (PlatformMpuDefaultGhost.size a'₀)) ≤ num_impl__MAX))
      
end F
