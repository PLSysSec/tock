import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.OpsRangeRange
open Classical

namespace F



def DebugPanicBegin := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (c0 : Prop),
  ∀ (a'₀ : (OpsRangeRange Int)),
   (((k0 (OpsRangeRange.start a'₀) (OpsRangeRange.end a'₀) (OpsRangeRange.start a'₀) (OpsRangeRange.end a'₀)))) ∧
   (∀ (iter₀ : (OpsRangeRange Int)),
    ((k0 (OpsRangeRange.start iter₀) (OpsRangeRange.end iter₀) (OpsRangeRange.start a'₀) (OpsRangeRange.end a'₀))) ->
     ∀ (a'₂ : Prop),
      ∀ (a'₃ : (OpsRangeRange Int)),
       (a'₂ = True) ->
        ∀ (a'₄ : Int),
         (a'₄ ≥ (-2147483648)) ->
          (a'₄ ≤ 2147483647) ->
           (False ->
            (c0)) ∧
           (((k0 (OpsRangeRange.start a'₃) (OpsRangeRange.end a'₃) (OpsRangeRange.start a'₀) (OpsRangeRange.end a'₀))))
           )
   
end F
