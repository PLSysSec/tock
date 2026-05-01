import LeanProofs.Flux.Prelude
open Classical

namespace F



def GrantImpl__AllocWith := ∃ k0 : (a0 : Int) -> (a1 : Prop) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Prop) -> Prop, 
 ∀ (c0 : Prop),
  ∀ (init₀ : Int),
   ∀ (a'₁ : Prop),
    (∀ (a'₂ : Int),
     (((k0 init₀ a'₁))) ∧
     (((k1 a'₂ init₀ a'₁)))
     ) ∧
    (((k0 init₀ a'₁)) ->
     ∀ (a'₃ : Int),
      ((k1 a'₃ init₀ a'₁)) ->
       ∀ (a'₄ : Int),
        False ->
         (c0))
    
end F
