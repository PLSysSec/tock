import LeanProofs.Flux.Prelude
open Classical

namespace F



def AllocatorImpl__NewRegions := 
 ∀ (c1 : (Int -> Int)),
  ∀ (c0 : (Int -> Prop)),
   ∀ (r₀ : Int),
    ((¬(c0 r₀)) ∧ ((c1 r₀) = 0)) ->
     ∀ (regions₀ : (SmtMap Int Int)),
      ∀ (r₁ : Int),
       ((¬(c0 r₁)) ∧ ((c1 r₁) = 0)) ->
        ∀ (r₂ : Int),
         ((¬(c0 r₂)) ∧ ((c1 r₂) = 1)) ->
          ∀ (r₃ : Int),
           ((¬(c0 r₃)) ∧ ((c1 r₃) = 2)) ->
            ∀ (r₄ : Int),
             ((¬(c0 r₄)) ∧ ((c1 r₄) = 3)) ->
              ∀ (r₅ : Int),
               ((¬(c0 r₅)) ∧ ((c1 r₅) = 4)) ->
                ∀ (r₆ : Int),
                 ((¬(c0 r₆)) ∧ ((c1 r₆) = 5)) ->
                  ∀ (r₇ : Int),
                   ((¬(c0 r₇)) ∧ ((c1 r₇) = 6)) ->
                    ∀ (r₈ : Int),
                     ((¬(c0 r₈)) ∧ ((c1 r₈) = 7)) ->
                      ((((((((let a'₁₀ := (SmtMap_select (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) regions₀ 0 r₁) 1 r₂) 2 r₃) 3 r₄) 4 r₅) 5 r₆) 6 r₇) 7 r₈) 0); (¬(c0 a'₁₀))) ∧ (let a'₁₁ := (SmtMap_select (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) regions₀ 0 r₁) 1 r₂) 2 r₃) 3 r₄) 4 r₅) 5 r₆) 6 r₇) 7 r₈) 1); (¬(c0 a'₁₁)))) ∧ (let a'₁₂ := (SmtMap_select (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) regions₀ 0 r₁) 1 r₂) 2 r₃) 3 r₄) 4 r₅) 5 r₆) 6 r₇) 7 r₈) 2); (¬(c0 a'₁₂)))) ∧ (let a'₁₃ := (SmtMap_select (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) regions₀ 0 r₁) 1 r₂) 2 r₃) 3 r₄) 4 r₅) 5 r₆) 6 r₇) 7 r₈) 3); (¬(c0 a'₁₃)))) ∧ (let a'₁₄ := (SmtMap_select (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) regions₀ 0 r₁) 1 r₂) 2 r₃) 3 r₄) 4 r₅) 5 r₆) 6 r₇) 7 r₈) 4); (¬(c0 a'₁₄)))) ∧ (let a'₁₅ := (SmtMap_select (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) regions₀ 0 r₁) 1 r₂) 2 r₃) 3 r₄) 4 r₅) 5 r₆) 6 r₇) 7 r₈) 5); (¬(c0 a'₁₅)))) ∧ (let a'₁₆ := (SmtMap_select (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) regions₀ 0 r₁) 1 r₂) 2 r₃) 3 r₄) 4 r₅) 5 r₆) 6 r₇) 7 r₈) 6); (¬(c0 a'₁₆)))) ∧ (let a'₁₇ := (SmtMap_select (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) regions₀ 0 r₁) 1 r₂) 2 r₃) 3 r₄) 4 r₅) 5 r₆) 6 r₇) 7 r₈) 7); (¬(c0 a'₁₇))))
end F
