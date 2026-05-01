import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SliceIterIter
open Classical

namespace F



def KernelImpl__ProcessEach := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, ∃ k1 : (a0 : Prop) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k2 : (a0 : Prop) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Prop) -> (a9 : Int) -> (a10 : Int) -> (a11 : Prop) -> Prop, ∃ k4 : (a0 : Prop) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Prop) -> (a10 : Int) -> (a11 : Int) -> (a12 : Prop) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Prop) -> (a9 : Int) -> (a10 : Int) -> (a11 : Prop) -> Prop, 
 ∀ (c0 : Prop),
  ∀ (closure₀ : Int),
   ∀ (a'₁ : Int),
    (a'₁ ≥ 0) ->
     (a'₁ ≤ 18446744073709551615) ->
      ∀ (a'₂ : SliceIterIter),
       (((k0 (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) closure₀ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂)))) ∧
       (∀ (a'₃ : Prop),
        ((k1 a'₃ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) closure₀ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂)))) ∧
       (∀ (iter₀ : SliceIterIter),
        ∀ (closure₁ : Int),
         ((k0 (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) closure₁ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂))) ->
          (∀ (a'₆ : Prop),
           ((k1 a'₆ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) closure₁ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂))) ->
            ((k2 a'₆ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) closure₁))) ∧
          (∀ (a'₇ : Prop),
           ∀ (a'₈ : SliceIterIter),
            (a'₇ = True) ->
             ∀ (a'₉ : Prop),
              ((k2 a'₉ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) closure₁)) ->
               ((a'₉ = False) ->
                (((k3 closure₁ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) closure₁ a'₇ (SliceIterIter.idx a'₈) (SliceIterIter.len a'₈) a'₉))) ∧
                (∀ (a'₁₀ : Prop),
                 ((k2 a'₁₀ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) closure₁)) ->
                  ((k4 a'₁₀ closure₁ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) closure₁ a'₇ (SliceIterIter.idx a'₈) (SliceIterIter.len a'₈) a'₉)))
                ) ∧
               ((a'₉ = True) ->
                (False ->
                 (c0)) ∧
                (((k5 closure₁ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) closure₁ a'₇ (SliceIterIter.idx a'₈) (SliceIterIter.len a'₈) a'₉))) ∧
                (∀ (a'₁₁ : Int),
                 ((k5 a'₁₁ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) closure₁ a'₇ (SliceIterIter.idx a'₈) (SliceIterIter.len a'₈) a'₉)) ->
                  (((k3 a'₁₁ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) closure₁ a'₇ (SliceIterIter.idx a'₈) (SliceIterIter.len a'₈) a'₉))) ∧
                  (∀ (a'₁₂ : Prop),
                   ((k2 a'₁₂ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) closure₁)) ->
                    ((k4 a'₁₂ a'₁₁ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) closure₁ a'₇ (SliceIterIter.idx a'₈) (SliceIterIter.len a'₈) a'₉)))
                  )
                ) ∧
               (∀ (closure₂ : Int),
                ((k3 closure₂ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) closure₁ a'₇ (SliceIterIter.idx a'₈) (SliceIterIter.len a'₈) a'₉)) ->
                 (((k0 (SliceIterIter.idx a'₈) (SliceIterIter.len a'₈) closure₂ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂)))) ∧
                 (∀ (a'₁₄ : Prop),
                  ((k4 a'₁₄ closure₂ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) closure₁ a'₇ (SliceIterIter.idx a'₈) (SliceIterIter.len a'₈) a'₉)) ->
                   ((k1 a'₁₄ (SliceIterIter.idx a'₈) (SliceIterIter.len a'₈) closure₂ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂))))
                 )
               )
          )
       
end F
