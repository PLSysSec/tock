import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SliceIterIter
open Classical

namespace F



def KernelImpl__ProcessUntil := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k1 : (a0 : Prop) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, ∃ k2 : (a0 : Prop) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Prop) -> (a7 : Int) -> (a8 : Int) -> (a9 : Prop) -> Prop, ∃ k4 : (a0 : Prop) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Prop) -> (a8 : Int) -> (a9 : Int) -> (a10 : Prop) -> Prop, 
 ∀ (c0 : Prop),
  ∀ (closure₀ : Int),
   ∀ (a'₁ : Int),
    (a'₁ ≥ 0) ->
     (a'₁ ≤ 18446744073709551615) ->
      ∀ (a'₂ : SliceIterIter),
       (((k0 (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂)))) ∧
       (∀ (a'₃ : Prop),
        ((k1 a'₃ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂)))) ∧
       (∀ (iter₀ : SliceIterIter),
        ((k0 (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂))) ->
         (∀ (a'₅ : Prop),
          ((k1 a'₅ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂))) ->
           ((k2 a'₅ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀)))) ∧
         (∀ (a'₆ : Prop),
          ∀ (a'₇ : SliceIterIter),
           (a'₆ = True) ->
            ∀ (a'₈ : Prop),
             ((k2 a'₈ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀))) ->
              ((a'₈ = False) ->
               (((k3 closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) a'₆ (SliceIterIter.idx a'₇) (SliceIterIter.len a'₇) a'₈))) ∧
               (∀ (a'₉ : Prop),
                ((k2 a'₉ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀))) ->
                 ((k4 a'₉ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) a'₆ (SliceIterIter.idx a'₇) (SliceIterIter.len a'₇) a'₈)))
               ) ∧
              ((a'₈ = True) ->
               (False ->
                (c0)) ∧
               (∀ (ret₀ : Prop),
                (¬ret₀) ->
                 (((k3 closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) a'₆ (SliceIterIter.idx a'₇) (SliceIterIter.len a'₇) a'₈))) ∧
                 (∀ (a'₁₁ : Prop),
                  ((k2 a'₁₁ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀))) ->
                   ((k4 a'₁₁ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) a'₆ (SliceIterIter.idx a'₇) (SliceIterIter.len a'₇) a'₈)))
                 )
               ) ∧
              (((k3 closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) a'₆ (SliceIterIter.idx a'₇) (SliceIterIter.len a'₇) a'₈)) ->
               (((k0 (SliceIterIter.idx a'₇) (SliceIterIter.len a'₇) closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂)))) ∧
               (∀ (a'₁₂ : Prop),
                ((k4 a'₁₂ closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂) (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) a'₆ (SliceIterIter.idx a'₇) (SliceIterIter.len a'₇) a'₈)) ->
                 ((k1 a'₁₂ (SliceIterIter.idx a'₇) (SliceIterIter.len a'₇) closure₀ a'₁ (SliceIterIter.idx a'₂) (SliceIterIter.len a'₂))))
               )
              )
         )
       
end F
