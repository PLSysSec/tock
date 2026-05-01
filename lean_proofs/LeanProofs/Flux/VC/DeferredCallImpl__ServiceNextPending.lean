import LeanProofs.Flux.Prelude
open Classical

namespace F



def DeferredCallImpl__ServiceNextPending := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, 
 ∀ (a'₀ : Int),
  ∀ (a'₁ : Int),
   ∀ (a'₂ : Int),
    ∀ (a'₃ : Int),
     (∀ (a'₄ : Int),
      ((k0 a'₄ a'₀ a'₁ a'₂ a'₃))) ∧
     (∀ (val₀ : Int),
      ((k0 val₀ a'₀ a'₁ a'₂ a'₃)) ->
       (val₀ ≥ 0) ->
        (val₀ ≤ 4294967295) ->
         (val₀ ≠ 0) ->
          ∀ (r₀ : Int),
           (((val₀ = 0) -> (r₀ = 32)) ∧ (True -> (r₀ ≤ 31))) ->
            (r₀ ≥ 0) ->
             (r₀ ≤ 4294967295) ->
              ∀ (a'₇ : Int),
               (a'₇ ≥ 0) ->
                (a'₇ ≤ 4294967295) ->
                 (r₀ < 32))
     
end F
