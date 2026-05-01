import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImplMAX
open Classical

namespace F



def FluxPtrImpl__InBounds := 
 ∀ (n₀ : Int),
  ∀ (offset₀ : Int),
   ((0 ≤ n₀) ∧ (n₀ ≤ num_impl__MAX)) ->
    (offset₀ ≥ 0) ->
     (offset₀ ≤ 18446744073709551615) ->
      (n₀ ≥ 0) ->
       (n₀ ≤ 18446744073709551615) ->
        ((¬(offset₀ ≤ 4294967295)) ->
         (False = ((0 ≤ (n₀ + offset₀)) ∧ ((n₀ + offset₀) ≤ num_impl__MAX)))) ∧
        ((offset₀ ≤ 4294967295) ->
         ((((n₀ + offset₀) ≥ 0)) ∧
         (((n₀ + offset₀) ≤ 18446744073709551615))
         ) ∧
         ((((n₀ + offset₀) ≤ 4294967295) = ((0 ≤ (n₀ + offset₀)) ∧ ((n₀ + offset₀) ≤ num_impl__MAX))))
         )
        
end F
