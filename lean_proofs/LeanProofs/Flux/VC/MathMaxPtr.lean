import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImplMAX
open Classical

namespace F



def MathMaxPtr := 
 ∀ (lhs₀ : Int),
  ∀ (rhs₀ : Int),
   ((0 ≤ lhs₀) ∧ (lhs₀ ≤ num_impl__MAX)) ->
    ((0 ≤ rhs₀) ∧ (rhs₀ ≤ num_impl__MAX)) ->
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
