import LeanProofs.Flux.Prelude
open Classical

namespace F



def HilTimeImpl__SaturatingScale := 
 ∀ (denom₀ : Int),
  ∀ (numerator₀ : Int),
   (denom₀ > 0) ->
    (numerator₀ ≥ 0) ->
     (numerator₀ ≤ 4294967295) ->
      (denom₀ ≥ 0) ->
       (denom₀ ≤ 4294967295) ->
        ∀ (a'₂ : Int),
         (a'₂ ≥ 0) ->
          (a'₂ ≤ 4294967295) ->
           ∀ (a'₃ : Int),
            (a'₃ ≥ 0) ->
             (a'₃ ≤ 18446744073709551615) ->
              ((((a'₂ * numerator₀) ≥ 0) ∧ ((a'₂ * numerator₀) ≤ 18446744073709551615)) -> (a'₃ = (a'₂ * numerator₀))) ->
               (denom₀ ≠ 0)
end F
