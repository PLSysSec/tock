import LeanProofs.Flux.Prelude
open Classical

namespace F



def UtilitiesMathLogBaseTwoU64 := 
 ∀ (num₀ : Int),
  (num₀ ≥ 0) ->
   (num₀ ≤ 18446744073709551615) ->
    ((num₀ ≠ 0) ->
     ∀ (r₀ : Int),
      (((num₀ = 0) -> (r₀ = 64)) ∧ ((num₀ > 0) -> (r₀ ≤ 63)) ∧ ((num₀ > 1) -> (r₀ ≤ 62))) ->
       (r₀ ≥ 0) ->
        (r₀ ≤ 4294967295) ->
         ∀ (a'₁ : Int),
          (a'₁ ≥ 0) ->
           (a'₁ ≤ 4294967295) ->
            ((((63 - r₀) ≥ 0) ∧ ((63 - r₀) ≤ 4294967295)) -> (a'₁ = (63 - r₀))) ->
             ((a'₁ < 64)) ∧
             ((num₀ > 1) ->
              (a'₁ > 0))
             ) ∧
    ((¬(num₀ ≠ 0)) ->
     (num₀ > 1) ->
      False)
    
end F
