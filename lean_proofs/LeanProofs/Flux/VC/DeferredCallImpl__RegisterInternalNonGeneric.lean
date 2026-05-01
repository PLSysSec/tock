import LeanProofs.Flux.Prelude
open Classical

namespace F



def DeferredCallImpl__RegisterInternalNonGeneric := 
 ∀ (a'₀ : Int),
  ∀ (a'₁ : Int),
   ∀ (a'₂ : Int),
    (a'₂ ≥ 0) ->
     (a'₂ ≤ 18446744073709551615) ->
      (¬(a'₂ ≥ 32)) ->
       (a'₂ < 32)
end F
