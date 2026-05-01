import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.OpsRangeRange
open Classical

namespace F



def GrantImpl__AllocNWith := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Prop) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Prop) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Prop) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Prop) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Prop) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Prop) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Prop) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Prop) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Prop) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> Prop, 
 ∀ (c0 : Prop),
  ∀ (constgen_NUM_ITEMS_2 : Int),
   ∀ (init₀ : Int),
    ∀ (a'₁ : Prop),
     (∀ (a'₂ : Int),
      (((k0 constgen_NUM_ITEMS_2 init₀ a'₁))) ∧
      (((k1 a'₂ constgen_NUM_ITEMS_2 init₀ a'₁)))
      ) ∧
     (((k0 constgen_NUM_ITEMS_2 init₀ a'₁)) ->
      ∀ (a'₃ : Int),
       ((k1 a'₃ constgen_NUM_ITEMS_2 init₀ a'₁)) ->
        ∀ (a'₄ : (OpsRangeRange Int)),
         (((k2 init₀ (OpsRangeRange.start a'₄) (OpsRangeRange.end a'₄) constgen_NUM_ITEMS_2 init₀ a'₁ a'₃ (OpsRangeRange.start a'₄) (OpsRangeRange.end a'₄)))) ∧
         (∀ (init₁ : Int),
          ∀ (iter₀ : (OpsRangeRange Int)),
           ((k2 init₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end iter₀) constgen_NUM_ITEMS_2 init₀ a'₁ a'₃ (OpsRangeRange.start a'₄) (OpsRangeRange.end a'₄))) ->
            ∀ (a'₇ : Prop),
             ∀ (a'₈ : (OpsRangeRange Int)),
              (a'₇ = True) ->
               ∀ (a'₉ : Int),
                (a'₉ ≥ 0) ->
                 (a'₉ ≤ 18446744073709551615) ->
                  ∀ (a'₁₀ : Int),
                   ∀ (a'₁₁ : Int),
                    (∀ (a'₁₂ : Int),
                     ((k3 a'₁₂ constgen_NUM_ITEMS_2 init₀ a'₁ a'₃ (OpsRangeRange.start a'₄) (OpsRangeRange.end a'₄) init₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end iter₀) a'₇ (OpsRangeRange.start a'₈) (OpsRangeRange.end a'₈) a'₉ a'₁₀ a'₁₁)) ->
                      ∀ (a'₁₃ : Int),
                       ((k4 a'₁₃ constgen_NUM_ITEMS_2 init₀ a'₁ a'₃ (OpsRangeRange.start a'₄) (OpsRangeRange.end a'₄) init₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end iter₀) a'₇ (OpsRangeRange.start a'₈) (OpsRangeRange.end a'₈) a'₉ a'₁₀ a'₁₁)) ->
                        ∀ (a'₁₄ : Int),
                         ((k3 a'₁₄ constgen_NUM_ITEMS_2 init₀ a'₁ a'₃ (OpsRangeRange.start a'₄) (OpsRangeRange.end a'₄) init₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end iter₀) a'₇ (OpsRangeRange.start a'₈) (OpsRangeRange.end a'₈) a'₉ a'₁₀ a'₁₁)) ->
                          ∀ (a'₁₅ : Int),
                           ((k4 a'₁₅ constgen_NUM_ITEMS_2 init₀ a'₁ a'₃ (OpsRangeRange.start a'₄) (OpsRangeRange.end a'₄) init₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end iter₀) a'₇ (OpsRangeRange.start a'₈) (OpsRangeRange.end a'₈) a'₉ a'₁₀ a'₁₁)) ->
                            ∀ (a'₁₆ : Int),
                             ((k5 a'₁₆ constgen_NUM_ITEMS_2 init₀ a'₁ a'₃ (OpsRangeRange.start a'₄) (OpsRangeRange.end a'₄) init₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end iter₀) a'₇ (OpsRangeRange.start a'₈) (OpsRangeRange.end a'₈) a'₉ a'₁₀ a'₁₁))) ∧
                    (False ->
                     (c0)) ∧
                    (((k3 init₁ constgen_NUM_ITEMS_2 init₀ a'₁ a'₃ (OpsRangeRange.start a'₄) (OpsRangeRange.end a'₄) init₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end iter₀) a'₇ (OpsRangeRange.start a'₈) (OpsRangeRange.end a'₈) a'₉ a'₁₀ a'₁₁))) ∧
                    (((k4 a'₉ constgen_NUM_ITEMS_2 init₀ a'₁ a'₃ (OpsRangeRange.start a'₄) (OpsRangeRange.end a'₄) init₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end iter₀) a'₇ (OpsRangeRange.start a'₈) (OpsRangeRange.end a'₈) a'₉ a'₁₀ a'₁₁))) ∧
                    (∀ (a'₁₇ : Int),
                     ((k5 a'₁₇ constgen_NUM_ITEMS_2 init₀ a'₁ a'₃ (OpsRangeRange.start a'₄) (OpsRangeRange.end a'₄) init₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end iter₀) a'₇ (OpsRangeRange.start a'₈) (OpsRangeRange.end a'₈) a'₉ a'₁₀ a'₁₁)) ->
                      ∀ (a'₁₈ : Int),
                       ((k3 a'₁₈ constgen_NUM_ITEMS_2 init₀ a'₁ a'₃ (OpsRangeRange.start a'₄) (OpsRangeRange.end a'₄) init₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end iter₀) a'₇ (OpsRangeRange.start a'₈) (OpsRangeRange.end a'₈) a'₉ a'₁₀ a'₁₁)) ->
                        ((k2 a'₁₈ (OpsRangeRange.start a'₈) (OpsRangeRange.end a'₈) constgen_NUM_ITEMS_2 init₀ a'₁ a'₃ (OpsRangeRange.start a'₄) (OpsRangeRange.end a'₄))))
                    )
         )
     
end F
