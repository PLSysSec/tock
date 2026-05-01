import LeanProofs.Flux.Prelude
open Classical

namespace F



def GrantImpl__GrantSize := 
 ∀ (data_sz₀ : Int),
  ∀ (g₀ : Int),
   (g₀ > 0) ->
    ∀ (a'₁ : Int),
     (a'₁ ≥ 0) ->
      ∀ (a'₂ : Int),
       (a'₂ ≥ 0) ->
        ∀ (a'₃ : Int),
         (a'₃ ≥ 0) ->
          ∀ (a'₄ : Int),
           (a'₄ ≥ 0) ->
            ∀ (a'₅ : Int),
             (a'₅ ≥ 0) ->
              ∀ (a'₆ : Int),
               (a'₆ ≥ 0) ->
                ∀ (a'₇ : Int),
                 (a'₇ ≥ 0) ->
                  (g₀ ≥ 0) ->
                   ((0 < g₀)) ∧
                   (∀ (padding₀ : Int),
                    ((0 < padding₀) ∧ (padding₀ < g₀)) ->
                     (padding₀ ≥ 0) ->
                      (data_sz₀ ≥ 0) ->
                       ((((((a'₁ + (a'₂ * a'₃)) + (a'₄ * a'₅)) + (a'₆ * a'₇)) + padding₀) + data_sz₀) ≥ data_sz₀))
                   
end F
