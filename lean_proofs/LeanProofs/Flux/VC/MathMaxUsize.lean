import LeanProofs.Flux.Prelude
open Classical

namespace F



def MathMaxUsize := 
 ∀ (lhs₀ : Int),
  ∀ (rhs₀ : Int),
   (lhs₀ ≥ 0) ->
    (lhs₀ ≤ 18446744073709551615) ->
     (rhs₀ ≥ 0) ->
      (rhs₀ ≤ 18446744073709551615) ->
       (¬(lhs₀ ≥ rhs₀)) ->
        (rhs₀ = (if (lhs₀ ≥ rhs₀) then lhs₀ else rhs₀))
end F
