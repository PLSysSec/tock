import LeanProofs.Flux.Prelude
open Classical

namespace F



def GrantImpl__AccessGrant := ∃ k0 : (a0 : Int) -> (a1 : Prop) -> Prop, 
 ∀ (c0 : Prop),
  ∀ (fun₀ : Int),
   ∀ (panic_on_reenter₀ : Prop),
    (((k0 fun₀ panic_on_reenter₀)) ->
     False ->
      (c0)) ∧
    (((k0 fun₀ panic_on_reenter₀)))
    
end F
