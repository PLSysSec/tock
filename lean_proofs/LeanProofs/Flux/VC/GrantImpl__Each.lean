import LeanProofs.Flux.Prelude
open Classical

namespace F



def GrantImpl__Each := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Prop) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Prop) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Prop) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Prop) -> Prop, 
 ∀ (c0 : Prop),
  ∀ (fun₀ : Int),
   (((k0 fun₀ fun₀))) ∧
   (∀ (fun₁ : Int),
    ((k0 fun₁ fun₀)) ->
     ∀ (a'₂ : Prop),
      (a'₂ = True) ->
       (((k1 fun₁ fun₀ fun₁ a'₂))) ∧
       (((k2 fun₀ fun₁ a'₂)) ->
        (False ->
         (c0)) ∧
        (∀ (a'₃ : Int),
         ((k1 a'₃ fun₀ fun₁ a'₂)) ->
          ((k3 a'₃ fun₀ fun₁ a'₂))) ∧
        (∀ (a'₄ : Int),
         ((k3 a'₄ fun₀ fun₁ a'₂)) ->
          ((k1 a'₄ fun₀ fun₁ a'₂)))
        ) ∧
       (((k2 fun₀ fun₁ a'₂))) ∧
       (∀ (a'₅ : Int),
        ((k1 a'₅ fun₀ fun₁ a'₂)) ->
         ((k4 a'₅ fun₀ fun₁ a'₂))) ∧
       (∀ (a'₆ : Int),
        ((k4 a'₆ fun₀ fun₁ a'₂)) ->
         ((k1 a'₆ fun₀ fun₁ a'₂))) ∧
       (∀ (a'₇ : Int),
        ((k1 a'₇ fun₀ fun₁ a'₂)) ->
         ((k0 a'₇ fun₀)))
       )
   
end F
