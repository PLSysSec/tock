import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Slc
import LeanProofs.Flux.Struct.CollectionsRingBufferRingBuffer
import LeanProofs.User.Fun.CollectionsSsliceLen
import LeanProofs.User.Fun.CollectionsSsliceSet
import LeanProofs.User.Fun.CollectionsSsliceGet
open Classical

namespace F

namespace CollectionsRingBufferImpl1PushKVarSolutions

-- acyclic (non-cut) kvars
def k3 (old₀ : (CollectionsRingBufferRingBuffer Int)) (val₀ : Int) (a'₈ : Int) (a'₉ : Prop) (a'₁₀ : (Slc Int)) (a'₁₁ : Int) (a'₁₂ : Int) (a'₁₃ : (Slc Int)) (a'₁₄ : Int) (a'₁₅ : Int) (a'₁₆ : Int) : Prop :=
  ((∃ (a'₁₇ : Int), ((((((CollectionsRingBufferRingBuffer.hd old₀) + 1) ≥ 0) ∧ (((CollectionsRingBufferRingBuffer.hd old₀) + 1) ≤ 18446744073709551615)) -> (a'₁₇ = ((CollectionsRingBufferRingBuffer.hd old₀) + 1))) ∧ (a'₁₁ = (a'₁₇ % (((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀)))) ∧ (a'₁₇ ≥ 0) ∧ (a'₁₇ ≤ 18446744073709551615))) ∧ (¬((CollectionsRingBufferRingBuffer.hd old₀) ≠ (((CollectionsRingBufferRingBuffer.tl old₀) + 1) % (((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀))))) ∧ (a'₉ = True) ∧ (a'₁₀ = (CollectionsRingBufferRingBuffer.ring old₀)) ∧ (a'₁₂ = (CollectionsRingBufferRingBuffer.tl old₀)) ∧ (a'₁₃ = (CollectionsRingBufferRingBuffer.ring old₀)) ∧ (a'₁₄ = (CollectionsRingBufferRingBuffer.hd old₀)) ∧ (a'₁₅ = (CollectionsRingBufferRingBuffer.tl old₀)) ∧ (a'₁₆ = val₀) ∧ (a'₈ = ((((((collections_sslice_get) : (((Slc Int) -> (Int -> Int)))) (CollectionsRingBufferRingBuffer.ring old₀))) : ((Int -> Int))) (CollectionsRingBufferRingBuffer.hd old₀))) ∧ ((((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀)) ≠ 0) ∧ ((((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀)) > 1) ∧ ((((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀)) ≥ 0) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) ≥ 0) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) ≥ 0) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) < (((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀))) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) < (((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀))) ∧ (0 ≤ (CollectionsRingBufferRingBuffer.hd old₀)) ∧ (0 ≤ (CollectionsRingBufferRingBuffer.tl old₀)) ∧ ((((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀)) ≤ 18446744073709551615) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) ≤ 18446744073709551615) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) ≤ 18446744073709551615))
def k0 (old₀ : (CollectionsRingBufferRingBuffer Int)) (val₀ : Int) (a'₁₈ : Prop) (a'₁₉ : (Slc Int)) (a'₂₀ : Int) (a'₂₁ : Int) (a'₂₂ : (Slc Int)) (a'₂₃ : Int) (a'₂₄ : Int) (a'₂₅ : Int) : Prop :=
  (((∃ (a'₂₆ : Int)(a'₂₇ : Int), ((((((CollectionsRingBufferRingBuffer.hd old₀) + 1) ≥ 0) ∧ (((CollectionsRingBufferRingBuffer.hd old₀) + 1) ≤ 18446744073709551615)) -> (a'₂₇ = ((CollectionsRingBufferRingBuffer.hd old₀) + 1))) ∧ (a'₂₀ = (a'₂₇ % (((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀)))) ∧ (a'₂₆ = ((((((collections_sslice_get) : (((Slc Int) -> (Int -> Int)))) (CollectionsRingBufferRingBuffer.ring old₀))) : ((Int -> Int))) (CollectionsRingBufferRingBuffer.hd old₀))) ∧ (a'₂₇ ≥ 0) ∧ (a'₂₇ ≤ 18446744073709551615))) ∧ (¬((CollectionsRingBufferRingBuffer.hd old₀) ≠ (((CollectionsRingBufferRingBuffer.tl old₀) + 1) % (((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀))))) ∧ (a'₁₈ = True) ∧ (a'₁₉ = (CollectionsRingBufferRingBuffer.ring old₀)) ∧ (a'₂₁ = (CollectionsRingBufferRingBuffer.tl old₀)) ∧ (a'₂₂ = (CollectionsRingBufferRingBuffer.ring old₀)) ∧ (a'₂₃ = (CollectionsRingBufferRingBuffer.hd old₀)) ∧ (a'₂₄ = (CollectionsRingBufferRingBuffer.tl old₀)) ∧ (a'₂₅ = val₀) ∧ ((((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀)) ≠ 0) ∧ ((((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀)) > 1) ∧ ((((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀)) ≥ 0) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) ≥ 0) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) ≥ 0) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) < (((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀))) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) < (((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀))) ∧ (0 ≤ (CollectionsRingBufferRingBuffer.hd old₀)) ∧ (0 ≤ (CollectionsRingBufferRingBuffer.tl old₀)) ∧ ((((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀)) ≤ 18446744073709551615) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) ≤ 18446744073709551615) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) ≤ 18446744073709551615)) ∨ ((a'₁₈ = False) ∧ (a'₁₉ = (CollectionsRingBufferRingBuffer.ring old₀)) ∧ (a'₂₀ = (CollectionsRingBufferRingBuffer.hd old₀)) ∧ (a'₂₁ = (CollectionsRingBufferRingBuffer.tl old₀)) ∧ (a'₂₂ = (CollectionsRingBufferRingBuffer.ring old₀)) ∧ (a'₂₃ = (CollectionsRingBufferRingBuffer.hd old₀)) ∧ (a'₂₄ = (CollectionsRingBufferRingBuffer.tl old₀)) ∧ (a'₂₅ = val₀) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) ≠ (((CollectionsRingBufferRingBuffer.tl old₀) + 1) % (((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀)))) ∧ ((((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀)) > 1) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) < (((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀))) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) < (((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀))) ∧ (0 ≤ (CollectionsRingBufferRingBuffer.hd old₀)) ∧ (0 ≤ (CollectionsRingBufferRingBuffer.tl old₀))))
def k1 (old₀ : (CollectionsRingBufferRingBuffer Int)) (val₀ : Int) (a'₂₈ : Int) (a'₂₉ : (Slc Int)) (a'₃₀ : Int) (a'₃₁ : Int) (a'₃₂ : Int) : Prop :=
  ((¬((CollectionsRingBufferRingBuffer.hd old₀) ≠ (((CollectionsRingBufferRingBuffer.tl old₀) + 1) % (((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀))))) ∧ (a'₂₉ = (CollectionsRingBufferRingBuffer.ring old₀)) ∧ (a'₃₀ = (CollectionsRingBufferRingBuffer.hd old₀)) ∧ (a'₃₁ = (CollectionsRingBufferRingBuffer.tl old₀)) ∧ (a'₃₂ = val₀) ∧ ((((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀)) > 1) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) ≥ 0) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) ≥ 0) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) < (((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀))) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) < (((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀))) ∧ (0 ≤ (CollectionsRingBufferRingBuffer.hd old₀)) ∧ (0 ≤ (CollectionsRingBufferRingBuffer.tl old₀)) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) ≤ 18446744073709551615) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) ≤ 18446744073709551615))
def k2 (old₀ : (CollectionsRingBufferRingBuffer Int)) (a'₂ : Int) (o₀ : Int) (val₀ : Int) (a'₃₃ : Int) (a'₃₄ : (Slc Int)) (a'₃₅ : Int) (a'₃₆ : Int) (a'₃₇ : Int) (a'₃₈ : Int) (a'₃₉ : Int) : Prop :=
  ((¬((CollectionsRingBufferRingBuffer.hd old₀) ≠ (((CollectionsRingBufferRingBuffer.tl old₀) + 1) % (((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀))))) ∧ (((((CollectionsRingBufferRingBuffer.hd old₀) + 1) ≥ 0) ∧ (((CollectionsRingBufferRingBuffer.hd old₀) + 1) ≤ 18446744073709551615)) -> (a'₂ = ((CollectionsRingBufferRingBuffer.hd old₀) + 1))) ∧ (a'₃₃ = o₀) ∧ (a'₃₄ = (CollectionsRingBufferRingBuffer.ring old₀)) ∧ (a'₃₅ = (CollectionsRingBufferRingBuffer.hd old₀)) ∧ (a'₃₆ = (CollectionsRingBufferRingBuffer.tl old₀)) ∧ (a'₃₇ = val₀) ∧ (a'₃₈ = o₀) ∧ (a'₃₉ = a'₂) ∧ (o₀ = ((((((collections_sslice_get) : (((Slc Int) -> (Int -> Int)))) (CollectionsRingBufferRingBuffer.ring old₀))) : ((Int -> Int))) (CollectionsRingBufferRingBuffer.hd old₀))) ∧ ((((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀)) ≠ 0) ∧ ((((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀)) > 1) ∧ (a'₂ ≥ 0) ∧ ((((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀)) ≥ 0) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) ≥ 0) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) ≥ 0) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) < (((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀))) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) < (((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀))) ∧ (0 ≤ (CollectionsRingBufferRingBuffer.hd old₀)) ∧ (0 ≤ (CollectionsRingBufferRingBuffer.tl old₀)) ∧ (a'₂ ≤ 18446744073709551615) ∧ ((((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀)) ≤ 18446744073709551615) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) ≤ 18446744073709551615) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) ≤ 18446744073709551615))

end CollectionsRingBufferImpl1PushKVarSolutions


open CollectionsRingBufferImpl1PushKVarSolutions




def CollectionsRingBufferImpl__1__Push := ∃ k0 : (a0 : (CollectionsRingBufferRingBuffer Int)) -> (a1 : Int) -> (a2 : Prop) -> (a3 : (Slc Int)) -> (a4 : Int) -> (a5 : Int) -> (a6 : (Slc Int)) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> Prop, ∃ k1 : (a0 : (CollectionsRingBufferRingBuffer Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : (Slc Int)) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, ∃ k2 : (a0 : (CollectionsRingBufferRingBuffer Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : (Slc Int)) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> Prop, ∃ k3 : (a0 : (CollectionsRingBufferRingBuffer Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : Prop) -> (a4 : (Slc Int)) -> (a5 : Int) -> (a6 : Int) -> (a7 : (Slc Int)) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> Prop, 
 ∀ (old₀ : (CollectionsRingBufferRingBuffer Int)),
  ∀ (val₀ : Int),
   ((0 ≤ (CollectionsRingBufferRingBuffer.tl old₀)) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) < (collections_sslice_len (CollectionsRingBufferRingBuffer.ring old₀)))) ->
    ((0 ≤ (CollectionsRingBufferRingBuffer.hd old₀)) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) < (collections_sslice_len (CollectionsRingBufferRingBuffer.ring old₀)))) ->
     ((collections_sslice_len (CollectionsRingBufferRingBuffer.ring old₀)) > 1) ->
      (((CollectionsRingBufferRingBuffer.hd old₀) ≠ (((CollectionsRingBufferRingBuffer.tl old₀) + 1) % (collections_sslice_len (CollectionsRingBufferRingBuffer.ring old₀)))) ->
       ((k0 old₀ val₀ False (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀))) ∧
      ((¬((CollectionsRingBufferRingBuffer.hd old₀) ≠ (((CollectionsRingBufferRingBuffer.tl old₀) + 1) % (collections_sslice_len (CollectionsRingBufferRingBuffer.ring old₀))))) ->
       ((CollectionsRingBufferRingBuffer.hd old₀) ≥ 0) ->
        ((CollectionsRingBufferRingBuffer.hd old₀) ≤ 18446744073709551615) ->
         ((CollectionsRingBufferRingBuffer.tl old₀) ≥ 0) ->
          ((CollectionsRingBufferRingBuffer.tl old₀) ≤ 18446744073709551615) ->
           (∀ (a'₀ : Int),
            ((k1 old₀ val₀ a'₀ (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀))) ∧
           (∀ (o₀ : Int),
            (o₀ = (collections_sslice_get (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀))) ->
             ((k1 old₀ val₀ o₀ (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀)) ->
              ∀ (a'₂ : Int),
               (a'₂ ≥ 0) ->
                (a'₂ ≤ 18446744073709551615) ->
                 (((((CollectionsRingBufferRingBuffer.hd old₀) + 1) ≥ 0) ∧ (((CollectionsRingBufferRingBuffer.hd old₀) + 1) ≤ 18446744073709551615)) -> (a'₂ = ((CollectionsRingBufferRingBuffer.hd old₀) + 1))) ->
                  ((collections_sslice_len (CollectionsRingBufferRingBuffer.ring old₀)) ≥ 0) ->
                   ((collections_sslice_len (CollectionsRingBufferRingBuffer.ring old₀)) ≤ 18446744073709551615) ->
                    (((collections_sslice_len (CollectionsRingBufferRingBuffer.ring old₀)) ≠ 0)) ∧
                    (((collections_sslice_len (CollectionsRingBufferRingBuffer.ring old₀)) ≠ 0) ->
                     (((k2 old₀ a'₂ o₀ val₀ o₀ (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀ o₀ a'₂))) ∧
                     (((a'₂ % (collections_sslice_len (CollectionsRingBufferRingBuffer.ring old₀))) < (collections_sslice_len (CollectionsRingBufferRingBuffer.ring old₀)))) ∧
                     (((0 ≤ (a'₂ % (collections_sslice_len (CollectionsRingBufferRingBuffer.ring old₀))))) ∧
                     (((a'₂ % (collections_sslice_len (CollectionsRingBufferRingBuffer.ring old₀))) < (collections_sslice_len (CollectionsRingBufferRingBuffer.ring old₀))))
                     ) ∧
                     (((k0 old₀ val₀ True (CollectionsRingBufferRingBuffer.ring old₀) (a'₂ % (collections_sslice_len (CollectionsRingBufferRingBuffer.ring old₀))) (CollectionsRingBufferRingBuffer.tl old₀) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀))) ∧
                     (∀ (a'₃ : Int),
                      ((k2 old₀ a'₂ o₀ val₀ a'₃ (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀ o₀ a'₂)) ->
                       ((k3 old₀ val₀ a'₃ True (CollectionsRingBufferRingBuffer.ring old₀) (a'₂ % (collections_sslice_len (CollectionsRingBufferRingBuffer.ring old₀))) (CollectionsRingBufferRingBuffer.tl old₀) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀)))
                     )
                    )
           ) ∧
      (∀ (result₀ : Prop),
       ∀ (a'₅ : (CollectionsRingBufferRingBuffer Int)),
        ((k0 old₀ val₀ result₀ (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.hd a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀)) ->
         ((collections_sslice_len (CollectionsRingBufferRingBuffer.ring a'₅)) > 1) ->
          ((CollectionsRingBufferRingBuffer.hd a'₅) < (collections_sslice_len (CollectionsRingBufferRingBuffer.ring a'₅))) ->
           ((CollectionsRingBufferRingBuffer.hd a'₅) ≥ 0) ->
            ((CollectionsRingBufferRingBuffer.hd a'₅) ≤ 18446744073709551615) ->
             ((CollectionsRingBufferRingBuffer.tl a'₅) < (collections_sslice_len (CollectionsRingBufferRingBuffer.ring a'₅))) ->
              ((CollectionsRingBufferRingBuffer.tl a'₅) ≥ 0) ->
               ((CollectionsRingBufferRingBuffer.tl a'₅) ≤ 18446744073709551615) ->
                ∀ (a'₆ : Int),
                 (a'₆ ≥ 0) ->
                  (a'₆ ≤ 18446744073709551615) ->
                   (((((CollectionsRingBufferRingBuffer.tl a'₅) + 1) ≥ 0) ∧ (((CollectionsRingBufferRingBuffer.tl a'₅) + 1) ≤ 18446744073709551615)) -> (a'₆ = ((CollectionsRingBufferRingBuffer.tl a'₅) + 1))) ->
                    ((collections_sslice_len (collections_sslice_set (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀)) ≥ 0) ->
                     ((collections_sslice_len (collections_sslice_set (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀)) ≤ 18446744073709551615) ->
                      (((collections_sslice_len (collections_sslice_set (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀)) ≠ 0)) ∧
                      (((collections_sslice_len (collections_sslice_set (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀)) ≠ 0) ->
                       (((collections_sslice_len (collections_sslice_set (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀)) > 1)) ∧
                       (((CollectionsRingBufferRingBuffer.hd a'₅) < (collections_sslice_len (collections_sslice_set (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀)))) ∧
                       (((a'₆ % (collections_sslice_len (collections_sslice_set (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀))) < (collections_sslice_len (collections_sslice_set (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀)))) ∧
                       (((0 ≤ (a'₆ % (collections_sslice_len (collections_sslice_set (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀))))) ∧
                       (((a'₆ % (collections_sslice_len (collections_sslice_set (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀))) < (collections_sslice_len (collections_sslice_set (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀))))
                       ) ∧
                       (((0 ≤ (CollectionsRingBufferRingBuffer.hd a'₅))) ∧
                       (((CollectionsRingBufferRingBuffer.hd a'₅) < (collections_sslice_len (collections_sslice_set (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀))))
                       ) ∧
                       (((collections_sslice_len (collections_sslice_set (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀)) > 1)) ∧
                       (∀ (a'₇ : Int),
                        ((k3 old₀ val₀ a'₇ result₀ (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.hd a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀)) ->
                         (a'₇ = (collections_sslice_get (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀)))) ∧
                       ((result₀ = ((CollectionsRingBufferRingBuffer.hd old₀) = (((CollectionsRingBufferRingBuffer.tl old₀) + 1) % (collections_sslice_len (CollectionsRingBufferRingBuffer.ring old₀)))))) ∧
                       (((collections_sslice_set (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀) = (collections_sslice_set (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀))) ∧
                       (((a'₆ % (collections_sslice_len (collections_sslice_set (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀))) = (((CollectionsRingBufferRingBuffer.tl old₀) + 1) % (collections_sslice_len (CollectionsRingBufferRingBuffer.ring old₀))))) ∧
                       (result₀ ->
                        ((CollectionsRingBufferRingBuffer.hd a'₅) = (((CollectionsRingBufferRingBuffer.hd old₀) + 1) % (collections_sslice_len (CollectionsRingBufferRingBuffer.ring old₀))))) ∧
                       ((¬result₀) ->
                        ((CollectionsRingBufferRingBuffer.hd a'₅) = (CollectionsRingBufferRingBuffer.hd old₀)))
                       )
                      )
      
end F
