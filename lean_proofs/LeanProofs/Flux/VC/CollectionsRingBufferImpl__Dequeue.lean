import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Slc
import LeanProofs.Flux.Struct.CollectionsRingBufferRingBuffer
import LeanProofs.User.Fun.CollectionsSsliceLen
import LeanProofs.User.Fun.CollectionsSsliceGet
open Classical

namespace F

namespace CollectionsRingBufferImplDequeueKVarSolutions

-- acyclic (non-cut) kvars
def k0 (old₀ : (CollectionsRingBufferRingBuffer Int)) (a'₄ : Int) (a'₅ : (Slc Int)) (a'₆ : Int) (a'₇ : Int) : Prop :=
  ((a'₅ = (CollectionsRingBufferRingBuffer.ring old₀)) ∧ (a'₆ = (CollectionsRingBufferRingBuffer.hd old₀)) ∧ (a'₇ = (CollectionsRingBufferRingBuffer.tl old₀)) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) ≠ (CollectionsRingBufferRingBuffer.tl old₀)) ∧ ((((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀)) > 1) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) ≥ 0) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) ≥ 0) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) < (((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀))) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) < (((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀))) ∧ (0 ≤ (CollectionsRingBufferRingBuffer.hd old₀)) ∧ (0 ≤ (CollectionsRingBufferRingBuffer.tl old₀)) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) ≤ 18446744073709551615) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) ≤ 18446744073709551615))
def k1 (old₀ : (CollectionsRingBufferRingBuffer Int)) (a'₂ : Int) (o₀ : Int) (a'₈ : Int) (a'₉ : (Slc Int)) (a'₁₀ : Int) (a'₁₁ : Int) (a'₁₂ : Int) (a'₁₃ : Int) : Prop :=
  ((((((CollectionsRingBufferRingBuffer.hd old₀) + 1) ≥ 0) ∧ (((CollectionsRingBufferRingBuffer.hd old₀) + 1) ≤ 18446744073709551615)) -> (a'₂ = ((CollectionsRingBufferRingBuffer.hd old₀) + 1))) ∧ (a'₈ = o₀) ∧ (a'₉ = (CollectionsRingBufferRingBuffer.ring old₀)) ∧ (a'₁₀ = (CollectionsRingBufferRingBuffer.hd old₀)) ∧ (a'₁₁ = (CollectionsRingBufferRingBuffer.tl old₀)) ∧ (a'₁₂ = o₀) ∧ (a'₁₃ = a'₂) ∧ (o₀ = ((((((collections_sslice_get) : (((Slc Int) -> (Int -> Int)))) (CollectionsRingBufferRingBuffer.ring old₀))) : ((Int -> Int))) (CollectionsRingBufferRingBuffer.hd old₀))) ∧ ((((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀)) ≠ 0) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) ≠ (CollectionsRingBufferRingBuffer.tl old₀)) ∧ ((((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀)) > 1) ∧ (a'₂ ≥ 0) ∧ ((((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀)) ≥ 0) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) ≥ 0) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) ≥ 0) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) < (((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀))) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) < (((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀))) ∧ (0 ≤ (CollectionsRingBufferRingBuffer.hd old₀)) ∧ (0 ≤ (CollectionsRingBufferRingBuffer.tl old₀)) ∧ (a'₂ ≤ 18446744073709551615) ∧ ((((collections_sslice_len) : (((Slc Int) -> Int))) (CollectionsRingBufferRingBuffer.ring old₀)) ≤ 18446744073709551615) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) ≤ 18446744073709551615) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) ≤ 18446744073709551615))

end CollectionsRingBufferImplDequeueKVarSolutions


open CollectionsRingBufferImplDequeueKVarSolutions




def CollectionsRingBufferImpl__Dequeue := ∃ k0 : (a0 : (CollectionsRingBufferRingBuffer Int)) -> (a1 : Int) -> (a2 : (Slc Int)) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k1 : (a0 : (CollectionsRingBufferRingBuffer Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : (Slc Int)) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, 
 ∀ (old₀ : (CollectionsRingBufferRingBuffer Int)),
  ((0 ≤ (CollectionsRingBufferRingBuffer.tl old₀)) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)))) ->
   ((0 ≤ (CollectionsRingBufferRingBuffer.hd old₀)) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)))) ->
    ((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)) > 1) ->
     ((¬((CollectionsRingBufferRingBuffer.hd old₀) ≠ (CollectionsRingBufferRingBuffer.tl old₀))) ->
      ((False = ((CollectionsRingBufferRingBuffer.hd old₀) ≠ (CollectionsRingBufferRingBuffer.tl old₀)))) ∧
      (False ->
       ((CollectionsRingBufferRingBuffer.hd old₀) = (((CollectionsRingBufferRingBuffer.hd old₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀))))) ∧
      (((CollectionsRingBufferRingBuffer.hd old₀) = (CollectionsRingBufferRingBuffer.hd old₀)))
      ) ∧
     (((CollectionsRingBufferRingBuffer.hd old₀) ≠ (CollectionsRingBufferRingBuffer.tl old₀)) ->
      ((CollectionsRingBufferRingBuffer.hd old₀) ≥ 0) ->
       ((CollectionsRingBufferRingBuffer.hd old₀) ≤ 18446744073709551615) ->
        ((CollectionsRingBufferRingBuffer.tl old₀) ≥ 0) ->
         ((CollectionsRingBufferRingBuffer.tl old₀) ≤ 18446744073709551615) ->
          (∀ (a'₀ : Int),
           ((k0 old₀ a'₀ (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀)))) ∧
          (∀ (o₀ : Int),
           (o₀ = (collections_sslice_get (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀))) ->
            ((k0 old₀ o₀ (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀))) ->
             ∀ (a'₂ : Int),
              (a'₂ ≥ 0) ->
               (a'₂ ≤ 18446744073709551615) ->
                (((((CollectionsRingBufferRingBuffer.hd old₀) + 1) ≥ 0) ∧ (((CollectionsRingBufferRingBuffer.hd old₀) + 1) ≤ 18446744073709551615)) -> (a'₂ = ((CollectionsRingBufferRingBuffer.hd old₀) + 1))) ->
                 ((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)) ≥ 0) ->
                  ((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)) ≤ 18446744073709551615) ->
                   (((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)) ≠ 0)) ∧
                   (((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)) ≠ 0) ->
                    (((k1 old₀ a'₂ o₀ o₀ (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀) o₀ a'₂))) ∧
                    (((a'₂ % (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀))) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)))) ∧
                    (((0 ≤ (a'₂ % (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀))))) ∧
                    (((a'₂ % (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀))) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀))))
                    ) ∧
                    (∀ (a'₃ : Int),
                     ((k1 old₀ a'₂ o₀ a'₃ (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀) o₀ a'₂)) ->
                      (a'₃ = (collections_sslice_get (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀)))) ∧
                    ((True = ((CollectionsRingBufferRingBuffer.hd old₀) ≠ (CollectionsRingBufferRingBuffer.tl old₀)))) ∧
                    (((a'₂ % (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀))) = (((CollectionsRingBufferRingBuffer.hd old₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀))))) ∧
                    (False ->
                     ((a'₂ % (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀))) = (CollectionsRingBufferRingBuffer.hd old₀)))
                    )
                   )
          )
     
end F
