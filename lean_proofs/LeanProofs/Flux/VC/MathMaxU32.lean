import LeanProofs.Flux.Prelude
open Classical

namespace F



def MathMaxU32 := 
 ∀ (lhs₀ : Int),
  ∀ (rhs₀ : Int),
   (lhs₀ ≥ 0) ->
    (lhs₀ ≤ 4294967295) ->
     (rhs₀ ≥ 0) ->
      (rhs₀ ≤ 4294967295) ->
       ((¬(lhs₀ ≥ rhs₀)) ->
        ((lhs₀ ≥ rhs₀) ->
         (rhs₀ = lhs₀)) ∧
        ((rhs₀ > lhs₀) ->
         (rhs₀ = rhs₀))
        ) ∧
       ((lhs₀ ≥ rhs₀) ->
        ((lhs₀ = lhs₀)) ∧
        ((rhs₀ > lhs₀) ->
         (lhs₀ = rhs₀))
        )
       
end F
