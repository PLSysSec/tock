import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.PlatformMpuPermissions
import LeanProofs.Flux.Struct.PlatformMpuMpuRegionDefault
import LeanProofs.Flux.Fun.NumImplMAX
open Classical

namespace F



def PlatformMpuImpl__CreateExactRegion := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Prop) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Prop) -> Prop, ∃ k2 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Prop) -> (a7 : Prop) -> (a8 : Prop) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Prop) -> (a11 : Prop) -> (a12 : Prop) -> Prop, 
 ∀ (region_number₀ : Int),
  ∀ (start₀ : Int),
   ∀ (size₀ : Int),
    ∀ (permissions₀ : PlatformMpuPermissions),
     (region_number₀ < 8) ->
      ((0 ≤ (start₀ + size₀)) ∧ ((start₀ + size₀) ≤ num_impl__MAX)) ->
       (region_number₀ ≥ 0) ->
        (region_number₀ ≤ 18446744073709551615) ->
         ((0 ≤ start₀) ∧ (start₀ ≤ num_impl__MAX)) ->
          (size₀ ≥ 0) ->
           (size₀ ≤ 18446744073709551615) ->
            (((k0 start₀ region_number₀ start₀ size₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀)))) ∧
            (((k1 size₀ region_number₀ start₀ size₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀)))) ∧
            (((k2 (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀) region_number₀ start₀ size₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀)))) ∧
            (((0 ≤ size₀)) ∧
            ((size₀ ≤ num_impl__MAX))
            ) ∧
            (∀ (a'₀ : Int),
             ((k0 a'₀ region_number₀ start₀ size₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀))) ->
              (a'₀ = start₀)) ∧
            (∀ (a'₁ : Int),
             ((k1 a'₁ region_number₀ start₀ size₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀))) ->
              (a'₁ = size₀)) ∧
            (∀ (a'₂ : PlatformMpuPermissions),
             ((k2 (PlatformMpuPermissions.r a'₂) (PlatformMpuPermissions.w a'₂) (PlatformMpuPermissions.x a'₂) region_number₀ start₀ size₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀))) ->
              (a'₂ = permissions₀)) ∧
            (((k3 start₀ size₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀) True region_number₀ region_number₀ start₀ size₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀)))) ∧
            (∀ (a'₃ : PlatformMpuMpuRegionDefault),
             ((k3 (PlatformMpuMpuRegionDefault.start a'₃) (PlatformMpuMpuRegionDefault.size a'₃) (PlatformMpuPermissions.r (PlatformMpuMpuRegionDefault.perms a'₃)) (PlatformMpuPermissions.w (PlatformMpuMpuRegionDefault.perms a'₃)) (PlatformMpuPermissions.x (PlatformMpuMpuRegionDefault.perms a'₃)) (PlatformMpuMpuRegionDefault.is_set a'₃) (PlatformMpuMpuRegionDefault.rnum a'₃) region_number₀ start₀ size₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀))) ->
              ((PlatformMpuMpuRegionDefault.is_set a'₃)) ∧
              ((start₀ = (PlatformMpuMpuRegionDefault.start a'₃))) ∧
              (((start₀ + size₀) = ((PlatformMpuMpuRegionDefault.start a'₃) + (PlatformMpuMpuRegionDefault.size a'₃)))) ∧
              ((permissions₀ = (PlatformMpuMpuRegionDefault.perms a'₃)))
              )
            
end F
