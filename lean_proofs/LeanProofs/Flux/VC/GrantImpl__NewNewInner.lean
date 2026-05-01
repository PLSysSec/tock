import LeanProofs.Flux.Prelude
open Classical

namespace F



def GrantImpl__NewNewInner := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : Prop) -> (a10 : Prop) -> (a11 : Int) -> (a12 : Int) -> (a13 : Prop) -> (a14 : Prop) -> Prop, 
 ∀ (dalign₀ : Int),
  ∀ (a'₁ : Int),
   ∀ (a'₂ : Int),
    ∀ (a'₃ : Int),
     (dalign₀ > 0) ->
      (a'₁ ≥ 0) ->
       (a'₁ ≤ 18446744073709551615) ->
        (a'₂ ≥ 0) ->
         (a'₂ ≤ 18446744073709551615) ->
          ∀ (a'₄ : Int),
           (a'₄ ≥ 0) ->
            (a'₄ ≤ 18446744073709551615) ->
             ∀ (a'₅ : Int),
              (a'₅ ≥ 0) ->
               (a'₅ ≤ 18446744073709551615) ->
                ∀ (a'₆ : Prop),
                 ∀ (a'₇ : Prop),
                  ∀ (a'₈ : Prop),
                   (a'₈ = True) ->
                    ∀ (a'₉ : Prop),
                     (¬a'₉) ->
                      ∀ (alloc_align₀ : Int),
                       (alloc_align₀ ≥ 0) ->
                        (alloc_align₀ ≤ 18446744073709551615) ->
                         ∀ (alloc_size₀ : Int),
                          (alloc_size₀ ≥ a'₃) ->
                           (alloc_size₀ ≥ 0) ->
                            (alloc_size₀ ≤ 18446744073709551615) ->
                             ∀ (a'₁₂ : Prop),
                              a'₁₂ ->
                               ∀ (a'₁₃ : Prop),
                                (∀ (a'₁₄ : Int),
                                 ((k0 a'₁₄ dalign₀ a'₁ a'₂ a'₃ a'₄ a'₅ a'₆ a'₇ a'₈ a'₉ alloc_align₀ alloc_size₀ True a'₁₃))) ∧
                                (∀ (a'₁₅ : Int),
                                 ((k0 a'₁₅ dalign₀ a'₁ a'₂ a'₃ a'₄ a'₅ a'₆ a'₇ a'₈ a'₉ alloc_align₀ alloc_size₀ True a'₁₃)) ->
                                  (a'₃ ≤ alloc_size₀))
                                
end F
