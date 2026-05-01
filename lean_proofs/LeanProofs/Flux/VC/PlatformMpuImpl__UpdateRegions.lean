import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.PlatformMpuPermissions
import LeanProofs.Flux.Struct.PlatformMpuMpuRegionDefault
import LeanProofs.Flux.Struct.FluxPairPair
import LeanProofs.Flux.Fun.NumImplMAX
open Classical

namespace F



def PlatformMpuImpl__UpdateRegions := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Prop) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Prop) -> Prop, ∃ k2 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : Prop) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Prop) -> (a10 : Prop) -> (a11 : Prop) -> (a12 : Prop) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> (a17 : Int) -> (a18 : Prop) -> (a19 : Prop) -> (a20 : Prop) -> (a21 : Int) -> (a22 : Int) -> (a23 : Int) -> (a24 : Prop) -> (a25 : Prop) -> (a26 : Prop) -> (a27 : Prop) -> (a28 : Int) -> Prop, 
 ∀ (region_start₀ : Int),
  ∀ (available_size₀ : Int),
   ∀ (region_size₀ : Int),
    ∀ (max_region_number₀ : Int),
     ∀ (permissions₀ : PlatformMpuPermissions),
      ((max_region_number₀ > 0) ∧ (max_region_number₀ < 8)) ->
       ((0 ≤ (region_start₀ + available_size₀)) ∧ ((region_start₀ + available_size₀) ≤ num_impl__MAX)) ->
        ((0 ≤ region_start₀) ∧ (region_start₀ ≤ num_impl__MAX)) ->
         (available_size₀ ≥ 0) ->
          (available_size₀ ≤ 18446744073709551615) ->
           (region_size₀ ≥ 0) ->
            (region_size₀ ≤ 18446744073709551615) ->
             (max_region_number₀ ≥ 0) ->
              (max_region_number₀ ≤ 18446744073709551615) ->
               (¬(region_size₀ > available_size₀)) ->
                (region_size₀ ≠ 0) ->
                 (((k0 region_start₀ region_start₀ available_size₀ region_size₀ max_region_number₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀)))) ∧
                 (((k1 region_size₀ region_start₀ available_size₀ region_size₀ max_region_number₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀)))) ∧
                 (((k2 (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀) region_start₀ available_size₀ region_size₀ max_region_number₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀)))) ∧
                 (∀ (a'₀ : Int),
                  (a'₀ ≥ 0) ->
                   (a'₀ ≤ 18446744073709551615) ->
                    ((((max_region_number₀ - 1) ≥ 0) ∧ ((max_region_number₀ - 1) ≤ 18446744073709551615)) -> (a'₀ = (max_region_number₀ - 1))) ->
                     (((0 ≤ region_size₀)) ∧
                     ((region_size₀ ≤ num_impl__MAX)) ∧
                     ((0 ≤ (region_start₀ + region_size₀))) ∧
                     (((region_start₀ + region_size₀) ≤ num_impl__MAX))
                     ) ∧
                     (∀ (a'₁ : Int),
                      ((k0 a'₁ region_start₀ available_size₀ region_size₀ max_region_number₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀))) ->
                       (a'₁ = region_start₀)) ∧
                     (∀ (a'₂ : Int),
                      ((k1 a'₂ region_start₀ available_size₀ region_size₀ max_region_number₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀))) ->
                       (a'₂ = region_size₀)) ∧
                     (∀ (a'₃ : PlatformMpuPermissions),
                      ((k2 (PlatformMpuPermissions.r a'₃) (PlatformMpuPermissions.w a'₃) (PlatformMpuPermissions.x a'₃) region_start₀ available_size₀ region_size₀ max_region_number₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀))) ->
                       (a'₃ = permissions₀)) ∧
                     (∀ (r₀ : PlatformMpuMpuRegionDefault),
                      ((¬(PlatformMpuMpuRegionDefault.is_set r₀)) ∧ ((PlatformMpuMpuRegionDefault.rnum r₀) = max_region_number₀)) ->
                       ((PlatformMpuMpuRegionDefault.is_set r₀) -> (((0 ≤ (PlatformMpuMpuRegionDefault.size r₀)) ∧ ((PlatformMpuMpuRegionDefault.size r₀) ≤ num_impl__MAX)) ∧ ((0 ≤ ((PlatformMpuMpuRegionDefault.start r₀) + (PlatformMpuMpuRegionDefault.size r₀))) ∧ (((PlatformMpuMpuRegionDefault.start r₀) + (PlatformMpuMpuRegionDefault.size r₀)) ≤ num_impl__MAX)))) ->
                        (((k3 region_start₀ region_size₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀) True a'₀ (PlatformMpuMpuRegionDefault.start r₀) (PlatformMpuMpuRegionDefault.size r₀) (PlatformMpuPermissions.r (PlatformMpuMpuRegionDefault.perms r₀)) (PlatformMpuPermissions.w (PlatformMpuMpuRegionDefault.perms r₀)) (PlatformMpuPermissions.x (PlatformMpuMpuRegionDefault.perms r₀)) (PlatformMpuMpuRegionDefault.is_set r₀) (PlatformMpuMpuRegionDefault.rnum r₀) region_start₀ available_size₀ region_size₀ max_region_number₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀) a'₀ (PlatformMpuMpuRegionDefault.start r₀) (PlatformMpuMpuRegionDefault.size r₀) (PlatformMpuPermissions.r (PlatformMpuMpuRegionDefault.perms r₀)) (PlatformMpuPermissions.w (PlatformMpuMpuRegionDefault.perms r₀)) (PlatformMpuPermissions.x (PlatformMpuMpuRegionDefault.perms r₀)) (PlatformMpuMpuRegionDefault.is_set r₀) (PlatformMpuMpuRegionDefault.rnum r₀)))) ∧
                        (∀ (a'₅ : (FluxPairPair PlatformMpuMpuRegionDefault PlatformMpuMpuRegionDefault)),
                         ((k3 (PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₅)) (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₅)) (PlatformMpuPermissions.r (PlatformMpuMpuRegionDefault.perms (FluxPairPair.fst a'₅))) (PlatformMpuPermissions.w (PlatformMpuMpuRegionDefault.perms (FluxPairPair.fst a'₅))) (PlatformMpuPermissions.x (PlatformMpuMpuRegionDefault.perms (FluxPairPair.fst a'₅))) (PlatformMpuMpuRegionDefault.is_set (FluxPairPair.fst a'₅)) (PlatformMpuMpuRegionDefault.rnum (FluxPairPair.fst a'₅)) (PlatformMpuMpuRegionDefault.start (FluxPairPair.snd a'₅)) (PlatformMpuMpuRegionDefault.size (FluxPairPair.snd a'₅)) (PlatformMpuPermissions.r (PlatformMpuMpuRegionDefault.perms (FluxPairPair.snd a'₅))) (PlatformMpuPermissions.w (PlatformMpuMpuRegionDefault.perms (FluxPairPair.snd a'₅))) (PlatformMpuPermissions.x (PlatformMpuMpuRegionDefault.perms (FluxPairPair.snd a'₅))) (PlatformMpuMpuRegionDefault.is_set (FluxPairPair.snd a'₅)) (PlatformMpuMpuRegionDefault.rnum (FluxPairPair.snd a'₅)) region_start₀ available_size₀ region_size₀ max_region_number₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀) a'₀ (PlatformMpuMpuRegionDefault.start r₀) (PlatformMpuMpuRegionDefault.size r₀) (PlatformMpuPermissions.r (PlatformMpuMpuRegionDefault.perms r₀)) (PlatformMpuPermissions.w (PlatformMpuMpuRegionDefault.perms r₀)) (PlatformMpuPermissions.x (PlatformMpuMpuRegionDefault.perms r₀)) (PlatformMpuMpuRegionDefault.is_set r₀) (PlatformMpuMpuRegionDefault.rnum r₀))) ->
                          ((0 ≤ ((PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₅)) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₅))))) ∧
                          ((((PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₅)) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₅))) ≤ num_impl__MAX)) ∧
                          ((¬(PlatformMpuMpuRegionDefault.is_set (FluxPairPair.snd a'₅))) ->
                           ((PlatformMpuMpuRegionDefault.is_set (FluxPairPair.fst a'₅))) ∧
                           (((PlatformMpuMpuRegionDefault.perms (FluxPairPair.fst a'₅)) = permissions₀)) ∧
                           ((region_start₀ = (PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₅)))) ∧
                           (((PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₅)) > 0)) ∧
                           ((¬(PlatformMpuMpuRegionDefault.is_set (FluxPairPair.snd a'₅))) ->
                            ((region_start₀ + (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₅))) = ((PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₅)) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₅))))) ∧
                           ((PlatformMpuMpuRegionDefault.is_set (FluxPairPair.snd a'₅)) ->
                            (((PlatformMpuMpuRegionDefault.size (FluxPairPair.snd a'₅)) > 0)) ∧
                            ((((PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₅)) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₅))) = (PlatformMpuMpuRegionDefault.start (FluxPairPair.snd a'₅)))) ∧
                            (((region_start₀ + (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₅))) = (((PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₅)) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₅))) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.snd a'₅))))) ∧
                            (((PlatformMpuMpuRegionDefault.perms (FluxPairPair.snd a'₅)) = permissions₀))
                            ) ∧
                           (((PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₅)) ≥ region_size₀))
                           ) ∧
                          ((PlatformMpuMpuRegionDefault.is_set (FluxPairPair.snd a'₅)) ->
                           ((PlatformMpuMpuRegionDefault.is_set (FluxPairPair.fst a'₅))) ∧
                           (((PlatformMpuMpuRegionDefault.perms (FluxPairPair.fst a'₅)) = permissions₀)) ∧
                           ((region_start₀ = (PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₅)))) ∧
                           (((PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₅)) > 0)) ∧
                           ((¬(PlatformMpuMpuRegionDefault.is_set (FluxPairPair.snd a'₅))) ->
                            (((region_start₀ + (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₅))) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.snd a'₅))) = ((PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₅)) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₅))))) ∧
                           ((PlatformMpuMpuRegionDefault.is_set (FluxPairPair.snd a'₅)) ->
                            (((PlatformMpuMpuRegionDefault.size (FluxPairPair.snd a'₅)) > 0)) ∧
                            ((((PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₅)) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₅))) = (PlatformMpuMpuRegionDefault.start (FluxPairPair.snd a'₅)))) ∧
                            ((((region_start₀ + (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₅))) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.snd a'₅))) = (((PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₅)) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₅))) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.snd a'₅))))) ∧
                            (((PlatformMpuMpuRegionDefault.perms (FluxPairPair.snd a'₅)) = permissions₀))
                            ) ∧
                           ((((PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₅)) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.snd a'₅))) ≥ region_size₀))
                           )
                          )
                        )
                     )
                 
end F
