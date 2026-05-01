import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.PlatformMpuPermissions
import LeanProofs.Flux.Struct.PlatformMpuMpuRegionDefault
import LeanProofs.Flux.Struct.FluxPairPair
import LeanProofs.Flux.Fun.NumImplMAX
open Classical

namespace F



def PlatformMpuImpl__AllocateRegions := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Int) -> Prop, ∃ k2 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Prop) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Prop) -> (a10 : Prop) -> (a11 : Prop) -> (a12 : Prop) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> (a17 : Prop) -> (a18 : Prop) -> (a19 : Prop) -> (a20 : Int) -> (a21 : Int) -> (a22 : Int) -> (a23 : Int) -> (a24 : Prop) -> (a25 : Prop) -> (a26 : Prop) -> (a27 : Prop) -> (a28 : Int) -> Prop, 
 ∀ (max_region_number₀ : Int),
  ∀ (available_start₀ : Int),
   ∀ (available_size₀ : Int),
    ∀ (permissions₀ : PlatformMpuPermissions),
     ∀ (region_size₀ : Int),
      ((max_region_number₀ > 0) ∧ (max_region_number₀ < 8)) ->
       ((0 ≤ (available_start₀ + available_size₀)) ∧ ((available_start₀ + available_size₀) ≤ num_impl__MAX)) ->
        (max_region_number₀ ≥ 0) ->
         (max_region_number₀ ≤ 18446744073709551615) ->
          ((0 ≤ available_start₀) ∧ (available_start₀ ≤ num_impl__MAX)) ->
           (available_size₀ ≥ 0) ->
            (available_size₀ ≤ 18446744073709551615) ->
             (region_size₀ ≥ 0) ->
              (region_size₀ ≤ 18446744073709551615) ->
               (¬(region_size₀ > available_size₀)) ->
                (region_size₀ ≠ 0) ->
                 (((k0 available_start₀ max_region_number₀ available_start₀ available_size₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀) region_size₀))) ∧
                 (((k1 region_size₀ max_region_number₀ available_start₀ available_size₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀) region_size₀))) ∧
                 (((k2 (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀) max_region_number₀ available_start₀ available_size₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀) region_size₀))) ∧
                 (∀ (a'₁ : Int),
                  (a'₁ ≥ 0) ->
                   (a'₁ ≤ 18446744073709551615) ->
                    ((((max_region_number₀ - 1) ≥ 0) ∧ ((max_region_number₀ - 1) ≤ 18446744073709551615)) -> (a'₁ = (max_region_number₀ - 1))) ->
                     (((0 ≤ region_size₀)) ∧
                     ((region_size₀ ≤ num_impl__MAX)) ∧
                     ((0 ≤ (available_start₀ + region_size₀))) ∧
                     (((available_start₀ + region_size₀) ≤ num_impl__MAX))
                     ) ∧
                     (∀ (a'₂ : Int),
                      ((k0 a'₂ max_region_number₀ available_start₀ available_size₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀) region_size₀)) ->
                       (a'₂ = available_start₀)) ∧
                     (∀ (a'₃ : Int),
                      ((k1 a'₃ max_region_number₀ available_start₀ available_size₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀) region_size₀)) ->
                       (a'₃ = region_size₀)) ∧
                     (∀ (a'₄ : PlatformMpuPermissions),
                      ((k2 (PlatformMpuPermissions.r a'₄) (PlatformMpuPermissions.w a'₄) (PlatformMpuPermissions.x a'₄) max_region_number₀ available_start₀ available_size₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀) region_size₀)) ->
                       (a'₄ = permissions₀)) ∧
                     (∀ (r₀ : PlatformMpuMpuRegionDefault),
                      ((¬(PlatformMpuMpuRegionDefault.is_set r₀)) ∧ ((PlatformMpuMpuRegionDefault.rnum r₀) = max_region_number₀)) ->
                       ((PlatformMpuMpuRegionDefault.is_set r₀) -> (((0 ≤ (PlatformMpuMpuRegionDefault.size r₀)) ∧ ((PlatformMpuMpuRegionDefault.size r₀) ≤ num_impl__MAX)) ∧ ((0 ≤ ((PlatformMpuMpuRegionDefault.start r₀) + (PlatformMpuMpuRegionDefault.size r₀))) ∧ (((PlatformMpuMpuRegionDefault.start r₀) + (PlatformMpuMpuRegionDefault.size r₀)) ≤ num_impl__MAX)))) ->
                        (((k3 available_start₀ region_size₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀) True a'₁ (PlatformMpuMpuRegionDefault.start r₀) (PlatformMpuMpuRegionDefault.size r₀) (PlatformMpuPermissions.r (PlatformMpuMpuRegionDefault.perms r₀)) (PlatformMpuPermissions.w (PlatformMpuMpuRegionDefault.perms r₀)) (PlatformMpuPermissions.x (PlatformMpuMpuRegionDefault.perms r₀)) (PlatformMpuMpuRegionDefault.is_set r₀) (PlatformMpuMpuRegionDefault.rnum r₀) max_region_number₀ available_start₀ available_size₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀) region_size₀ a'₁ (PlatformMpuMpuRegionDefault.start r₀) (PlatformMpuMpuRegionDefault.size r₀) (PlatformMpuPermissions.r (PlatformMpuMpuRegionDefault.perms r₀)) (PlatformMpuPermissions.w (PlatformMpuMpuRegionDefault.perms r₀)) (PlatformMpuPermissions.x (PlatformMpuMpuRegionDefault.perms r₀)) (PlatformMpuMpuRegionDefault.is_set r₀) (PlatformMpuMpuRegionDefault.rnum r₀)))) ∧
                        (∀ (a'₆ : (FluxPairPair PlatformMpuMpuRegionDefault PlatformMpuMpuRegionDefault)),
                         ((k3 (PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₆)) (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₆)) (PlatformMpuPermissions.r (PlatformMpuMpuRegionDefault.perms (FluxPairPair.fst a'₆))) (PlatformMpuPermissions.w (PlatformMpuMpuRegionDefault.perms (FluxPairPair.fst a'₆))) (PlatformMpuPermissions.x (PlatformMpuMpuRegionDefault.perms (FluxPairPair.fst a'₆))) (PlatformMpuMpuRegionDefault.is_set (FluxPairPair.fst a'₆)) (PlatformMpuMpuRegionDefault.rnum (FluxPairPair.fst a'₆)) (PlatformMpuMpuRegionDefault.start (FluxPairPair.snd a'₆)) (PlatformMpuMpuRegionDefault.size (FluxPairPair.snd a'₆)) (PlatformMpuPermissions.r (PlatformMpuMpuRegionDefault.perms (FluxPairPair.snd a'₆))) (PlatformMpuPermissions.w (PlatformMpuMpuRegionDefault.perms (FluxPairPair.snd a'₆))) (PlatformMpuPermissions.x (PlatformMpuMpuRegionDefault.perms (FluxPairPair.snd a'₆))) (PlatformMpuMpuRegionDefault.is_set (FluxPairPair.snd a'₆)) (PlatformMpuMpuRegionDefault.rnum (FluxPairPair.snd a'₆)) max_region_number₀ available_start₀ available_size₀ (PlatformMpuPermissions.r permissions₀) (PlatformMpuPermissions.w permissions₀) (PlatformMpuPermissions.x permissions₀) region_size₀ a'₁ (PlatformMpuMpuRegionDefault.start r₀) (PlatformMpuMpuRegionDefault.size r₀) (PlatformMpuPermissions.r (PlatformMpuMpuRegionDefault.perms r₀)) (PlatformMpuPermissions.w (PlatformMpuMpuRegionDefault.perms r₀)) (PlatformMpuPermissions.x (PlatformMpuMpuRegionDefault.perms r₀)) (PlatformMpuMpuRegionDefault.is_set r₀) (PlatformMpuMpuRegionDefault.rnum r₀))) ->
                          (((PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₆)) ≥ available_start₀)) ∧
                          ((0 ≤ ((PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₆)) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₆))))) ∧
                          ((((PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₆)) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₆))) ≤ num_impl__MAX)) ∧
                          ((¬(PlatformMpuMpuRegionDefault.is_set (FluxPairPair.snd a'₆))) ->
                           ((PlatformMpuMpuRegionDefault.is_set (FluxPairPair.fst a'₆))) ∧
                           (((PlatformMpuMpuRegionDefault.perms (FluxPairPair.fst a'₆)) = permissions₀)) ∧
                           (((PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₆)) = (PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₆)))) ∧
                           (((PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₆)) > 0)) ∧
                           ((¬(PlatformMpuMpuRegionDefault.is_set (FluxPairPair.snd a'₆))) ->
                            (((PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₆)) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₆))) = ((PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₆)) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₆))))) ∧
                           ((PlatformMpuMpuRegionDefault.is_set (FluxPairPair.snd a'₆)) ->
                            (((PlatformMpuMpuRegionDefault.size (FluxPairPair.snd a'₆)) > 0)) ∧
                            ((((PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₆)) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₆))) = (PlatformMpuMpuRegionDefault.start (FluxPairPair.snd a'₆)))) ∧
                            ((((PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₆)) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₆))) = (((PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₆)) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₆))) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.snd a'₆))))) ∧
                            (((PlatformMpuMpuRegionDefault.perms (FluxPairPair.snd a'₆)) = permissions₀))
                            )
                           ) ∧
                          ((PlatformMpuMpuRegionDefault.is_set (FluxPairPair.snd a'₆)) ->
                           ((PlatformMpuMpuRegionDefault.is_set (FluxPairPair.fst a'₆))) ∧
                           (((PlatformMpuMpuRegionDefault.perms (FluxPairPair.fst a'₆)) = permissions₀)) ∧
                           (((PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₆)) = (PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₆)))) ∧
                           (((PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₆)) > 0)) ∧
                           ((¬(PlatformMpuMpuRegionDefault.is_set (FluxPairPair.snd a'₆))) ->
                            ((((PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₆)) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₆))) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.snd a'₆))) = ((PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₆)) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₆))))) ∧
                           ((PlatformMpuMpuRegionDefault.is_set (FluxPairPair.snd a'₆)) ->
                            (((PlatformMpuMpuRegionDefault.size (FluxPairPair.snd a'₆)) > 0)) ∧
                            ((((PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₆)) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₆))) = (PlatformMpuMpuRegionDefault.start (FluxPairPair.snd a'₆)))) ∧
                            (((((PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₆)) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₆))) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.snd a'₆))) = (((PlatformMpuMpuRegionDefault.start (FluxPairPair.fst a'₆)) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.fst a'₆))) + (PlatformMpuMpuRegionDefault.size (FluxPairPair.snd a'₆))))) ∧
                            (((PlatformMpuMpuRegionDefault.perms (FluxPairPair.snd a'₆)) = permissions₀))
                            )
                           )
                          )
                        )
                     )
                 
end F
