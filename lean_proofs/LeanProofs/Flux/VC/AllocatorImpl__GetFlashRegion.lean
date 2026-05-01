import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.PlatformMpuPermissions
import LeanProofs.Flux.Fun.NumImplMAX
open Classical

namespace F



def AllocatorImpl__GetFlashRegion := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Prop) -> Prop, 
 ∀ (c4 : (Int -> PlatformMpuPermissions)),
  ∀ (c3 : (Int -> Int)),
   ∀ (c2 : (Int -> Int)),
    ∀ (c1 : (Int -> Prop)),
     ∀ (flash_start₀ : Int),
      ∀ (flash_size₀ : Int),
       ((0 ≤ (flash_start₀ + flash_size₀)) ∧ ((flash_start₀ + flash_size₀) ≤ num_impl__MAX)) ->
        ((0 ≤ flash_start₀) ∧ (flash_start₀ ≤ num_impl__MAX)) ->
         (flash_size₀ ≥ 0) ->
          (flash_size₀ ≤ 18446744073709551615) ->
           ∀ (a'₀ : Prop),
            (∀ (r₀ : Int),
             ((c1 r₀) ∧ (flash_start₀ = (c2 r₀)) ∧ ((flash_start₀ + flash_size₀) = ((c2 r₀) + (c3 r₀))) ∧ ((PlatformMpuPermissions.mkPlatformMpuPermissions₀ True False True) = (c4 r₀))) ->
              ((k0 r₀ flash_start₀ flash_size₀ a'₀))) ∧
            (∀ (a'₂ : Prop),
             ∀ (a'₃ : Int),
              ((k0 a'₃ flash_start₀ flash_size₀ a'₀)) ->
               ((c1 a'₃)) ∧
               ((flash_start₀ = (c2 a'₃))) ∧
               (((flash_start₀ + flash_size₀) = ((c2 a'₃) + (c3 a'₃)))) ∧
               (((c4 a'₃) = (PlatformMpuPermissions.mkPlatformMpuPermissions₀ True False True)))
               )
            
end F
