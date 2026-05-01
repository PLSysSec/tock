import LeanProofs.Flux.Prelude
open Classical

namespace F



def GrantImpl__AccessGrantWithAllocator := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Prop) -> (a3 : Int) -> (a4 : Int) -> (a5 : Prop) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Prop) -> (a3 : Int) -> (a4 : Int) -> (a5 : Prop) -> (a6 : Prop) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Prop) -> (a3 : Int) -> (a4 : Int) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Prop) -> Prop, 
 ∀ (c0 : Prop),
  ∀ (fun₀ : Int),
   ∀ (panic_on_reenter₀ : Prop),
    ∀ (a'₂ : Int),
     (a'₂ ≥ 0) ->
      (a'₂ ≤ 18446744073709551615) ->
       ∀ (a'₃ : Int),
        (a'₃ ≥ 0) ->
         (a'₃ ≤ 18446744073709551615) ->
          ∀ (a'₄ : Prop),
           (∀ (a'₅ : Int),
            ((k0 a'₅ fun₀ panic_on_reenter₀ a'₂ a'₃ a'₄))) ∧
           (∀ (a'₆ : Prop),
            (∀ (a'₇ : Int),
             ((k0 a'₇ fun₀ panic_on_reenter₀ a'₂ a'₃ a'₄)) ->
              ((k1 a'₇ fun₀ panic_on_reenter₀ a'₂ a'₃ a'₄ a'₆))) ∧
            (∀ (a'₈ : Prop),
             (∀ (a'₉ : Int),
              ((k1 a'₉ fun₀ panic_on_reenter₀ a'₂ a'₃ a'₄ a'₆)) ->
               ((k2 a'₉ fun₀ panic_on_reenter₀ a'₂ a'₃ a'₄ a'₆ a'₈))) ∧
             (∀ (a'₁₀ : Int),
              ((k2 a'₁₀ fun₀ panic_on_reenter₀ a'₂ a'₃ a'₄ a'₆ a'₈)) ->
               ∀ (align₀ : Int),
                (align₀ > 0) ->
                 (align₀ ≥ 0) ->
                  (align₀ ≤ 18446744073709551615) ->
                   ∀ (a'₁₂ : Int),
                    (a'₁₂ ≥ 0) ->
                     (a'₁₂ ≤ 18446744073709551615) ->
                      ∀ (a'₁₃ : Int),
                       (a'₁₃ ≥ 0) ->
                        (a'₁₃ ≤ 255) ->
                         ∀ (a'₁₄ : Int),
                          (a'₁₄ ≥ 0) ->
                           (a'₁₄ ≤ 255) ->
                            ∀ (a'₁₅ : Int),
                             (a'₁₅ ≥ 0) ->
                              (a'₁₅ ≤ 255) ->
                               ((align₀ > 0)) ∧
                               (∀ (alloc_size₀ : Int),
                                (alloc_size₀ ≥ a'₁₂) ->
                                 (alloc_size₀ ≥ 0) ->
                                  (alloc_size₀ ≤ 18446744073709551615) ->
                                   ∀ (a'₁₇ : Int),
                                    ∀ (a'₁₈ : Int),
                                     ∀ (a'₁₉ : Int),
                                      (a'₁₇ ≥ 0) ->
                                       (a'₁₇ ≤ 18446744073709551615) ->
                                        (a'₁₈ ≥ 0) ->
                                         (a'₁₈ ≤ 18446744073709551615) ->
                                          (a'₁₉ ≥ 0) ->
                                           (a'₁₉ ≤ 18446744073709551615) ->
                                            ((a'₁₂ ≤ alloc_size₀)) ∧
                                            (∀ (a'₂₀ : Int),
                                             ∀ (a'₂₁ : Int),
                                              ∀ (a'₂₂ : Int),
                                               False ->
                                                (c0))
                                            )
                               )
             )
            )
           
end F
