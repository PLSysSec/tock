import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImplMAX
open Classical

namespace F



def UtilitiesMathLogBaseTwoU32Usize := 
 ∀ (num₀ : Int),
  (num₀ < num_impl__MAX) ->
   (num₀ ≥ 0) ->
    (num₀ ≤ 18446744073709551615) ->
     ((num₀ ≠ 0) ->
      ((num₀ ≤ num_impl__MAX)) ∧
      (∀ (r₀ : Int),
       (((num₀ = 0) -> (r₀ = 32)) ∧ ((num₀ > 0) -> (r₀ ≤ 31)) ∧ ((num₀ ≥ 512) -> (r₀ ≤ 22)) ∧ ((num₀ < 512) -> (r₀ > 22))) ->
        (r₀ ≥ 0) ->
         (r₀ ≤ 4294967295) ->
          ∀ (a'₁ : Int),
           (a'₁ ≥ 0) ->
            (a'₁ ≤ 4294967295) ->
             ((((31 - r₀) ≥ 0) ∧ ((31 - r₀) ≤ 4294967295)) -> (a'₁ = (31 - r₀))) ->
              ((num₀ = 0) ->
               (a'₁ = 0)) ∧
              ((a'₁ ≤ 31)) ∧
              ((num₀ < 512) ->
               (a'₁ < 9)) ∧
              ((num₀ ≥ 512) ->
               (a'₁ ≥ 9))
              )
      ) ∧
     ((¬(num₀ ≠ 0)) ->
      ((num₀ = 0) ->
       True) ∧
      ((num₀ < 512) ->
       True) ∧
      ((num₀ ≥ 512) ->
       False)
      )
     
end F
