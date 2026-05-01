import LeanProofs.Flux.Prelude
open Classical

namespace F



def UtilitiesMathLogBaseTwo := 
 ∀ (num₀ : Int),
  (num₀ ≥ 0) ->
   (num₀ ≤ 4294967295) ->
    ((num₀ ≠ 0) ->
     ∀ (r₀ : Int),
      (((num₀ = 0) -> (r₀ = 32)) ∧ ((num₀ > 0) -> (r₀ ≤ 31)) ∧ ((num₀ > 1) -> (r₀ ≤ 30))) ->
       (r₀ ≥ 0) ->
        (r₀ ≤ 4294967295) ->
         ∀ (a'₁ : Int),
          (a'₁ ≥ 0) ->
           (a'₁ ≤ 4294967295) ->
            ((((31 - r₀) ≥ 0) ∧ ((31 - r₀) ≤ 4294967295)) -> (a'₁ = (31 - r₀))) ->
             ((a'₁ < 32)) ∧
             ((num₀ > 1) ->
              (a'₁ > 0))
             ) ∧
    ((¬(num₀ ≠ 0)) ->
     (num₀ > 1) ->
      False)
    
end F
