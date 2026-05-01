import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImplMAX
open Classical

namespace F



def ProcessStandardImpl__BuildReadwriteProcessBuffer := 
 ∀ (a'₀ : Int),
  ∀ (size₀ : Int),
   ((0 ≤ a'₀) ∧ (a'₀ ≤ num_impl__MAX)) ->
    (size₀ ≥ 0) ->
     (size₀ ≤ 18446744073709551615) ->
      ∀ (a'₂ : Prop),
       a'₂ ->
        (¬(size₀ ≠ 0)) ->
         ((0 ≤ (a'₀ + 0))) ∧
         (((a'₀ + 0) ≤ num_impl__MAX))
         
end F
