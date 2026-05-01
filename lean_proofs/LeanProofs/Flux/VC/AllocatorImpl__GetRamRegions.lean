import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.FluxPairPair
import LeanProofs.Flux.Struct.PlatformMpuPermissions
import LeanProofs.Flux.Fun.NumImplMAX
open Classical

namespace F



def AllocatorImpl__GetRamRegions := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Prop) -> Prop, 
 ∀ (c4 : (Int -> Int)),
  ∀ (c3 : (Int -> PlatformMpuPermissions)),
   ∀ (c2 : (Int -> Prop)),
    ∀ (c1 : (Int -> Int)),
     ∀ (mem_start₀ : Int),
      ∀ (mem_size₀ : Int),
       ∀ (min_memory_size₀ : Int),
        ∀ (initial_app_memory_size₀ : Int),
         ((0 ≤ (mem_start₀ + mem_size₀)) ∧ ((mem_start₀ + mem_size₀) ≤ num_impl__MAX)) ->
          ((0 ≤ mem_start₀) ∧ (mem_start₀ ≤ num_impl__MAX)) ->
           (mem_size₀ ≥ 0) ->
            (mem_size₀ ≤ 18446744073709551615) ->
             (min_memory_size₀ ≥ 0) ->
              (min_memory_size₀ ≤ 18446744073709551615) ->
               (initial_app_memory_size₀ ≥ 0) ->
                (initial_app_memory_size₀ ≤ 18446744073709551615) ->
                 ((if (min_memory_size₀ ≥ initial_app_memory_size₀) then min_memory_size₀ else initial_app_memory_size₀) ≥ 0) ->
                  ((if (min_memory_size₀ ≥ initial_app_memory_size₀) then min_memory_size₀ else initial_app_memory_size₀) ≤ 18446744073709551615) ->
                   ∀ (a'₂ : Prop),
                    (∀ (p₀ : (FluxPairPair Int Int)),
                     (((c1 (FluxPairPair.fst p₀)) ≥ mem_start₀) ∧ ((¬(c2 (FluxPairPair.snd p₀))) -> ((((((c2 (FluxPairPair.fst p₀)) ∧ ((c3 (FluxPairPair.fst p₀)) = (PlatformMpuPermissions.mkPlatformMpuPermissions₀ True True False))) ∧ ((c1 (FluxPairPair.fst p₀)) = (c1 (FluxPairPair.fst p₀)))) ∧ ((c4 (FluxPairPair.fst p₀)) > 0)) ∧ ((¬(c2 (FluxPairPair.snd p₀))) -> (((c1 (FluxPairPair.fst p₀)) + (c4 (FluxPairPair.fst p₀))) = ((c1 (FluxPairPair.fst p₀)) + (c4 (FluxPairPair.fst p₀)))))) ∧ ((c2 (FluxPairPair.snd p₀)) -> (((((c4 (FluxPairPair.snd p₀)) > 0) ∧ (((c1 (FluxPairPair.fst p₀)) + (c4 (FluxPairPair.fst p₀))) = (c1 (FluxPairPair.snd p₀)))) ∧ (((c1 (FluxPairPair.fst p₀)) + (c4 (FluxPairPair.fst p₀))) = (((c1 (FluxPairPair.fst p₀)) + (c4 (FluxPairPair.fst p₀))) + (c4 (FluxPairPair.snd p₀))))) ∧ ((c3 (FluxPairPair.snd p₀)) = (PlatformMpuPermissions.mkPlatformMpuPermissions₀ True True False)))))) ∧ ((c2 (FluxPairPair.snd p₀)) -> ((((((c2 (FluxPairPair.fst p₀)) ∧ ((c3 (FluxPairPair.fst p₀)) = (PlatformMpuPermissions.mkPlatformMpuPermissions₀ True True False))) ∧ ((c1 (FluxPairPair.fst p₀)) = (c1 (FluxPairPair.fst p₀)))) ∧ ((c4 (FluxPairPair.fst p₀)) > 0)) ∧ ((¬(c2 (FluxPairPair.snd p₀))) -> ((((c1 (FluxPairPair.fst p₀)) + (c4 (FluxPairPair.fst p₀))) + (c4 (FluxPairPair.snd p₀))) = ((c1 (FluxPairPair.fst p₀)) + (c4 (FluxPairPair.fst p₀)))))) ∧ ((c2 (FluxPairPair.snd p₀)) -> (((((c4 (FluxPairPair.snd p₀)) > 0) ∧ (((c1 (FluxPairPair.fst p₀)) + (c4 (FluxPairPair.fst p₀))) = (c1 (FluxPairPair.snd p₀)))) ∧ ((((c1 (FluxPairPair.fst p₀)) + (c4 (FluxPairPair.fst p₀))) + (c4 (FluxPairPair.snd p₀))) = (((c1 (FluxPairPair.fst p₀)) + (c4 (FluxPairPair.fst p₀))) + (c4 (FluxPairPair.snd p₀))))) ∧ ((c3 (FluxPairPair.snd p₀)) = (PlatformMpuPermissions.mkPlatformMpuPermissions₀ True True False))))))) ->
                      ((k0 (FluxPairPair.fst p₀) (FluxPairPair.snd p₀) mem_start₀ mem_size₀ min_memory_size₀ initial_app_memory_size₀ a'₂))) ∧
                    (∀ (a'₄ : Prop),
                     ∀ (a'₅ : (FluxPairPair Int Int)),
                      ((k0 (FluxPairPair.fst a'₅) (FluxPairPair.snd a'₅) mem_start₀ mem_size₀ min_memory_size₀ initial_app_memory_size₀ a'₂)) ->
                       (((c1 (FluxPairPair.fst a'₅)) ≥ mem_start₀)) ∧
                       ((¬(c2 (FluxPairPair.snd a'₅))) ->
                        ((c2 (FluxPairPair.fst a'₅))) ∧
                        (((c3 (FluxPairPair.fst a'₅)) = (PlatformMpuPermissions.mkPlatformMpuPermissions₀ True True False))) ∧
                        (((c1 (FluxPairPair.fst a'₅)) = (c1 (FluxPairPair.fst a'₅)))) ∧
                        (((c4 (FluxPairPair.fst a'₅)) > 0)) ∧
                        ((¬(c2 (FluxPairPair.snd a'₅))) ->
                         (((c1 (FluxPairPair.fst a'₅)) + (c4 (FluxPairPair.fst a'₅))) = ((c1 (FluxPairPair.fst a'₅)) + (c4 (FluxPairPair.fst a'₅))))) ∧
                        ((c2 (FluxPairPair.snd a'₅)) ->
                         (((c4 (FluxPairPair.snd a'₅)) > 0)) ∧
                         ((((c1 (FluxPairPair.fst a'₅)) + (c4 (FluxPairPair.fst a'₅))) = (c1 (FluxPairPair.snd a'₅)))) ∧
                         ((((c1 (FluxPairPair.fst a'₅)) + (c4 (FluxPairPair.fst a'₅))) = (((c1 (FluxPairPair.fst a'₅)) + (c4 (FluxPairPair.fst a'₅))) + (c4 (FluxPairPair.snd a'₅))))) ∧
                         (((c3 (FluxPairPair.snd a'₅)) = (PlatformMpuPermissions.mkPlatformMpuPermissions₀ True True False)))
                         )
                        ) ∧
                       ((c2 (FluxPairPair.snd a'₅)) ->
                        ((c2 (FluxPairPair.fst a'₅))) ∧
                        (((c3 (FluxPairPair.fst a'₅)) = (PlatformMpuPermissions.mkPlatformMpuPermissions₀ True True False))) ∧
                        (((c1 (FluxPairPair.fst a'₅)) = (c1 (FluxPairPair.fst a'₅)))) ∧
                        (((c4 (FluxPairPair.fst a'₅)) > 0)) ∧
                        ((¬(c2 (FluxPairPair.snd a'₅))) ->
                         ((((c1 (FluxPairPair.fst a'₅)) + (c4 (FluxPairPair.fst a'₅))) + (c4 (FluxPairPair.snd a'₅))) = ((c1 (FluxPairPair.fst a'₅)) + (c4 (FluxPairPair.fst a'₅))))) ∧
                        ((c2 (FluxPairPair.snd a'₅)) ->
                         (((c4 (FluxPairPair.snd a'₅)) > 0)) ∧
                         ((((c1 (FluxPairPair.fst a'₅)) + (c4 (FluxPairPair.fst a'₅))) = (c1 (FluxPairPair.snd a'₅)))) ∧
                         (((((c1 (FluxPairPair.fst a'₅)) + (c4 (FluxPairPair.fst a'₅))) + (c4 (FluxPairPair.snd a'₅))) = (((c1 (FluxPairPair.fst a'₅)) + (c4 (FluxPairPair.fst a'₅))) + (c4 (FluxPairPair.snd a'₅))))) ∧
                         (((c3 (FluxPairPair.snd a'₅)) = (PlatformMpuPermissions.mkPlatformMpuPermissions₀ True True False)))
                         )
                        )
                       )
                    
end F
