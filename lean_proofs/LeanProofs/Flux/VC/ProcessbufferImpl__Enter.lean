import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImplMAX
open Classical

namespace F



def ProcessbufferImpl__Enter := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Prop) -> (a4 : Int) -> (a5 : Int) -> Prop, 
 ∀ (c1 : Prop),
  ∀ (fun₀ : Int),
   ∀ (a'₁ : Int),
    ((0 ≤ a'₁) ∧ (a'₁ ≤ num_impl__MAX)) ->
     ∀ (a'₂ : Int),
      (a'₂ ≥ 0) ->
       (a'₂ ≤ 18446744073709551615) ->
        ∀ (a'₃ : Prop),
         (a'₃ = True) ->
          ∀ (a'₄ : Int),
           (a'₄ ≥ 0) ->
            (a'₄ ≤ 18446744073709551615) ->
             ∀ (a'₅ : Int),
              (a'₅ ≥ 0) ->
               (a'₅ ≤ 18446744073709551615) ->
                (((k0 fun₀ a'₁ a'₂ a'₃ a'₄ a'₅)) ->
                 ∀ (a'₆ : Int),
                  ((0 ≤ a'₆) ∧ (a'₆ ≤ num_impl__MAX)) ->
                   ∀ (a'₇ : Int),
                    (a'₇ ≥ 0) ->
                     (a'₇ ≤ 18446744073709551615) ->
                      ∀ (a'₈ : Prop),
                       ∀ (a'₉ : Int),
                        False ->
                         (c1)) ∧
                (((k0 fun₀ a'₁ a'₂ a'₃ a'₄ a'₅)))
                
end F
