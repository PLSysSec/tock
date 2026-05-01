import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.FluxPairPair
import LeanProofs.Flux.Struct.AllocatorAppBreaks
import LeanProofs.Flux.Fun.NumImplMAX
open Classical

namespace F



def AllocatorImpl__GetAppBreaks := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Prop) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Prop) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Prop) -> (a10 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Prop) -> (a9 : Int) -> (a10 : Int) -> (a11 : Prop) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Prop) -> (a9 : Int) -> (a10 : Int) -> (a11 : Prop) -> (a12 : Prop) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Prop) -> (a15 : Int) -> (a16 : Int) -> (a17 : Prop) -> (a18 : Prop) -> (a19 : Int) -> Prop, 
 ∀ (c3 : (Int -> Int)),
  ∀ (c2 : (Int -> Prop)),
   ∀ (c0 : (Int -> Int)),
    ∀ (ram_regions₀ : (FluxPairPair Int Int)),
     ∀ (unallocated_memory_start₀ : Int),
      ∀ (unallocated_memory_size₀ : Int),
       ∀ (initial_kernel_memory_size₀ : Int),
        ∀ (flash_start₀ : Int),
         ∀ (flash_size₀ : Int),
          ((0 ≤ ((c0 (FluxPairPair.fst ram_regions₀)) + initial_kernel_memory_size₀)) ∧ (((c0 (FluxPairPair.fst ram_regions₀)) + initial_kernel_memory_size₀) ≤ num_impl__MAX) ∧ (c2 (FluxPairPair.fst ram_regions₀)) ∧ ((c3 (FluxPairPair.fst ram_regions₀)) ≥ unallocated_memory_start₀) ∧ ((unallocated_memory_start₀ + unallocated_memory_size₀) ≤ num_impl__MAX) ∧ (unallocated_memory_start₀ > 0) ∧ (initial_kernel_memory_size₀ > 0) ∧ ((flash_start₀ + flash_size₀) < unallocated_memory_start₀)) ->
           ((0 ≤ unallocated_memory_start₀) ∧ (unallocated_memory_start₀ ≤ num_impl__MAX)) ->
            (unallocated_memory_size₀ ≥ 0) ->
             (unallocated_memory_size₀ ≤ 18446744073709551615) ->
              (initial_kernel_memory_size₀ ≥ 0) ->
               (initial_kernel_memory_size₀ ≤ 18446744073709551615) ->
                ((0 ≤ flash_start₀) ∧ (flash_start₀ ≤ num_impl__MAX)) ->
                 (flash_size₀ ≥ 0) ->
                  (flash_size₀ ≤ 18446744073709551615) ->
                   (∀ (ptr₀ : Int),
                    ((c3 (FluxPairPair.fst ram_regions₀)) = ptr₀) ->
                     ((k0 ptr₀ (FluxPairPair.fst ram_regions₀) (FluxPairPair.snd ram_regions₀) unallocated_memory_start₀ unallocated_memory_size₀ initial_kernel_memory_size₀ flash_start₀ flash_size₀))) ∧
                   (∀ (a'₁ : Prop),
                    (∀ (a'₂ : Int),
                     ((k0 a'₂ (FluxPairPair.fst ram_regions₀) (FluxPairPair.snd ram_regions₀) unallocated_memory_start₀ unallocated_memory_size₀ initial_kernel_memory_size₀ flash_start₀ flash_size₀)) ->
                      ((k1 a'₂ (FluxPairPair.fst ram_regions₀) (FluxPairPair.snd ram_regions₀) unallocated_memory_start₀ unallocated_memory_size₀ initial_kernel_memory_size₀ flash_start₀ flash_size₀ a'₁))) ∧
                    (∀ (a'₃ : Int),
                     ((k1 a'₃ (FluxPairPair.fst ram_regions₀) (FluxPairPair.snd ram_regions₀) unallocated_memory_start₀ unallocated_memory_size₀ initial_kernel_memory_size₀ flash_start₀ flash_size₀ a'₁)) ->
                      ((0 ≤ a'₃) ∧ (a'₃ ≤ num_impl__MAX)) ->
                       (((c2 (FluxPairPair.snd ram_regions₀)) = False) ->
                        ((k2 0 False (FluxPairPair.fst ram_regions₀) (FluxPairPair.snd ram_regions₀) unallocated_memory_start₀ unallocated_memory_size₀ initial_kernel_memory_size₀ flash_start₀ flash_size₀ a'₁ a'₃))) ∧
                       (((c2 (FluxPairPair.snd ram_regions₀)) = True) ->
                        ∀ (a'₄ : Int),
                         (((c0 (FluxPairPair.snd ram_regions₀)) = a'₄) ∧ (0 ≤ a'₄) ∧ (a'₄ ≤ num_impl__MAX) ∧ (0 ≤ ((c3 (FluxPairPair.snd ram_regions₀)) + a'₄)) ∧ (((c3 (FluxPairPair.snd ram_regions₀)) + a'₄) ≤ num_impl__MAX)) ->
                          (a'₄ ≥ 0) ->
                           (a'₄ ≤ 18446744073709551615) ->
                            ((k2 a'₄ True (FluxPairPair.fst ram_regions₀) (FluxPairPair.snd ram_regions₀) unallocated_memory_start₀ unallocated_memory_size₀ initial_kernel_memory_size₀ flash_start₀ flash_size₀ a'₁ a'₃))) ∧
                       (∀ (snd_region_size₀ : Int),
                        ∀ (a'₆ : Prop),
                         ((k2 snd_region_size₀ a'₆ (FluxPairPair.fst ram_regions₀) (FluxPairPair.snd ram_regions₀) unallocated_memory_start₀ unallocated_memory_size₀ initial_kernel_memory_size₀ flash_start₀ flash_size₀ a'₁ a'₃)) ->
                          (∀ (sz₀ : Int),
                           (((c0 (FluxPairPair.fst ram_regions₀)) = sz₀) ∧ (0 ≤ sz₀) ∧ (sz₀ ≤ num_impl__MAX) ∧ (0 ≤ ((c3 (FluxPairPair.fst ram_regions₀)) + sz₀)) ∧ (((c3 (FluxPairPair.fst ram_regions₀)) + sz₀) ≤ num_impl__MAX)) ->
                            ((k3 sz₀ (FluxPairPair.fst ram_regions₀) (FluxPairPair.snd ram_regions₀) unallocated_memory_start₀ unallocated_memory_size₀ initial_kernel_memory_size₀ flash_start₀ flash_size₀ a'₁ a'₃ snd_region_size₀ a'₆))) ∧
                          (∀ (a'₈ : Prop),
                           (∀ (a'₉ : Int),
                            ((k3 a'₉ (FluxPairPair.fst ram_regions₀) (FluxPairPair.snd ram_regions₀) unallocated_memory_start₀ unallocated_memory_size₀ initial_kernel_memory_size₀ flash_start₀ flash_size₀ a'₁ a'₃ snd_region_size₀ a'₆)) ->
                             ((k4 a'₉ (FluxPairPair.fst ram_regions₀) (FluxPairPair.snd ram_regions₀) unallocated_memory_start₀ unallocated_memory_size₀ initial_kernel_memory_size₀ flash_start₀ flash_size₀ a'₁ a'₃ snd_region_size₀ a'₆ a'₈))) ∧
                           (∀ (a'₁₀ : Int),
                            ((k4 a'₁₀ (FluxPairPair.fst ram_regions₀) (FluxPairPair.snd ram_regions₀) unallocated_memory_start₀ unallocated_memory_size₀ initial_kernel_memory_size₀ flash_start₀ flash_size₀ a'₁ a'₃ snd_region_size₀ a'₆ a'₈)) ->
                             (a'₁₀ ≥ 0) ->
                              (a'₁₀ ≤ 18446744073709551615) ->
                               ((((a'₁₀ + snd_region_size₀) ≥ 0)) ∧
                               (((a'₁₀ + snd_region_size₀) ≤ 18446744073709551615))
                               ) ∧
                               ((a'₃ ≥ 0) ->
                                (a'₃ ≤ 18446744073709551615) ->
                                 ((((a'₃ + (a'₁₀ + snd_region_size₀)) ≥ 0)) ∧
                                 (((a'₃ + (a'₁₀ + snd_region_size₀)) ≤ 18446744073709551615))
                                 ) ∧
                                 (((((a'₁₀ + snd_region_size₀) + initial_kernel_memory_size₀) ≥ 0)) ∧
                                 ((((a'₁₀ + snd_region_size₀) + initial_kernel_memory_size₀) ≤ 18446744073709551615))
                                 ) ∧
                                 (((((a'₃ + ((a'₁₀ + snd_region_size₀) + initial_kernel_memory_size₀)) ≥ 0)) ∧
                                 (((a'₃ + ((a'₁₀ + snd_region_size₀) + initial_kernel_memory_size₀)) ≤ 18446744073709551615))
                                 ) ∧
                                 ((unallocated_memory_start₀ ≥ 0) ->
                                  (unallocated_memory_start₀ ≤ 18446744073709551615) ->
                                   ((((unallocated_memory_start₀ + unallocated_memory_size₀) ≥ 0)) ∧
                                   (((unallocated_memory_start₀ + unallocated_memory_size₀) ≤ 18446744073709551615))
                                   ) ∧
                                   ((¬((a'₃ + ((a'₁₀ + snd_region_size₀) + initial_kernel_memory_size₀)) > (unallocated_memory_start₀ + unallocated_memory_size₀))) ->
                                    (((((a'₃ + ((a'₁₀ + snd_region_size₀) + initial_kernel_memory_size₀)) - initial_kernel_memory_size₀) ≥ 0)) ∧
                                    ((((a'₃ + ((a'₁₀ + snd_region_size₀) + initial_kernel_memory_size₀)) - initial_kernel_memory_size₀) ≤ 18446744073709551615))
                                    ) ∧
                                    (((0 ≤ (a'₃ + (a'₁₀ + snd_region_size₀))) ∧ ((a'₃ + (a'₁₀ + snd_region_size₀)) ≤ num_impl__MAX)) ->
                                     ((0 ≤ ((a'₃ + ((a'₁₀ + snd_region_size₀) + initial_kernel_memory_size₀)) - initial_kernel_memory_size₀)) ∧ (((a'₃ + ((a'₁₀ + snd_region_size₀) + initial_kernel_memory_size₀)) - initial_kernel_memory_size₀) ≤ num_impl__MAX)) ->
                                      ((a'₃ ≥ a'₃)) ∧
                                      (((a'₃ + (a'₁₀ + snd_region_size₀)) ≤ ((a'₃ + ((a'₁₀ + snd_region_size₀) + initial_kernel_memory_size₀)) - initial_kernel_memory_size₀))) ∧
                                      (((a'₃ + (a'₁₀ + snd_region_size₀)) ≥ a'₃)) ∧
                                      (((flash_start₀ + flash_size₀) < a'₃)) ∧
                                      ((((a'₃ + ((a'₁₀ + snd_region_size₀) + initial_kernel_memory_size₀)) - initial_kernel_memory_size₀) ≤ (a'₃ + ((a'₁₀ + snd_region_size₀) + initial_kernel_memory_size₀)))) ∧
                                      (((a'₃ + ((a'₁₀ + snd_region_size₀) + initial_kernel_memory_size₀)) ≤ num_impl__MAX)) ∧
                                      (((k5 a'₃ ((a'₁₀ + snd_region_size₀) + initial_kernel_memory_size₀) (a'₃ + (a'₁₀ + snd_region_size₀)) a'₃ ((a'₃ + ((a'₁₀ + snd_region_size₀) + initial_kernel_memory_size₀)) - initial_kernel_memory_size₀) flash_start₀ flash_size₀ (FluxPairPair.fst ram_regions₀) (FluxPairPair.snd ram_regions₀) unallocated_memory_start₀ unallocated_memory_size₀ initial_kernel_memory_size₀ flash_start₀ flash_size₀ a'₁ a'₃ snd_region_size₀ a'₆ a'₈ a'₁₀))) ∧
                                      (∀ (a'₁₁ : AllocatorAppBreaks),
                                       ((k5 (AllocatorAppBreaks.memory_start a'₁₁) (AllocatorAppBreaks.memory_size a'₁₁) (AllocatorAppBreaks.app_break a'₁₁) (AllocatorAppBreaks.high_water_mark a'₁₁) (AllocatorAppBreaks.kernel_break a'₁₁) (AllocatorAppBreaks.flash_start a'₁₁) (AllocatorAppBreaks.flash_size a'₁₁) (FluxPairPair.fst ram_regions₀) (FluxPairPair.snd ram_regions₀) unallocated_memory_start₀ unallocated_memory_size₀ initial_kernel_memory_size₀ flash_start₀ flash_size₀ a'₁ a'₃ snd_region_size₀ a'₆ a'₈ a'₁₀)) ->
                                        (((AllocatorAppBreaks.memory_start a'₁₁) = (c3 (FluxPairPair.fst ram_regions₀)))) ∧
                                        ((¬(c2 (FluxPairPair.snd ram_regions₀))) ->
                                         ((AllocatorAppBreaks.app_break a'₁₁) = ((c3 (FluxPairPair.fst ram_regions₀)) + (c0 (FluxPairPair.fst ram_regions₀))))) ∧
                                        ((c2 (FluxPairPair.snd ram_regions₀)) ->
                                         ((AllocatorAppBreaks.app_break a'₁₁) = (((c3 (FluxPairPair.fst ram_regions₀)) + (c0 (FluxPairPair.fst ram_regions₀))) + (c0 (FluxPairPair.snd ram_regions₀))))) ∧
                                        (((AllocatorAppBreaks.flash_start a'₁₁) = flash_start₀)) ∧
                                        (((AllocatorAppBreaks.flash_size a'₁₁) = flash_size₀)) ∧
                                        (((AllocatorAppBreaks.memory_start a'₁₁) ≥ unallocated_memory_start₀)) ∧
                                        ((0 ≤ ((AllocatorAppBreaks.memory_start a'₁₁) + (AllocatorAppBreaks.memory_size a'₁₁)))) ∧
                                        ((((AllocatorAppBreaks.memory_start a'₁₁) + (AllocatorAppBreaks.memory_size a'₁₁)) ≤ num_impl__MAX)) ∧
                                        (((AllocatorAppBreaks.memory_start a'₁₁) > 0)) ∧
                                        (((AllocatorAppBreaks.memory_size a'₁₁) ≥ initial_kernel_memory_size₀)) ∧
                                        (((((AllocatorAppBreaks.memory_start a'₁₁) + (AllocatorAppBreaks.memory_size a'₁₁)) - (AllocatorAppBreaks.kernel_break a'₁₁)) = initial_kernel_memory_size₀))
                                        )
                                      )
                                    )
                                   )
                                 )
                                 )
                               )
                           )
                          )
                       )
                    )
                   
end F
