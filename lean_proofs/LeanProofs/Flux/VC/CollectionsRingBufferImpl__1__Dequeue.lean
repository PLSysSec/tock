import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Slc
import LeanProofs.Flux.Struct.CollectionsRingBufferRingBuffer
import LeanProofs.User.Fun.CollectionsSsliceLen
import LeanProofs.User.Fun.CollectionsSsliceGet
open Classical
set_option linter.unusedVariables false


namespace F



def CollectionsRingBufferImpl__1__Dequeue := ∃ k0 : (a0 : Int) -> (a1 : (Slc Int)) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : (Slc Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, 
 ∀ (old₀ : (CollectionsRingBufferRingBuffer Int)),
  ((0 ≤ (CollectionsRingBufferRingBuffer.tl old₀)) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)))) ->
   ((0 ≤ (CollectionsRingBufferRingBuffer.hd old₀)) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)))) ->
    ((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)) > 1) ->
     ((¬((CollectionsRingBufferRingBuffer.hd old₀) ≠ (CollectionsRingBufferRingBuffer.tl old₀))) ->
      ((False = ((CollectionsRingBufferRingBuffer.hd old₀) ≠ (CollectionsRingBufferRingBuffer.tl old₀)))) ∧
      ((old₀ = (if ((CollectionsRingBufferRingBuffer.hd old₀) ≠ (CollectionsRingBufferRingBuffer.tl old₀)) then (CollectionsRingBufferRingBuffer.mkCollectionsRingBufferRingBuffer₀ (CollectionsRingBufferRingBuffer.ring old₀) (((CollectionsRingBufferRingBuffer.hd old₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀))) (CollectionsRingBufferRingBuffer.tl old₀)) else old₀)))
      ) ∧
     (((CollectionsRingBufferRingBuffer.hd old₀) ≠ (CollectionsRingBufferRingBuffer.tl old₀)) ->
      ((CollectionsRingBufferRingBuffer.hd old₀) ≥ 0) ->
       ((CollectionsRingBufferRingBuffer.hd old₀) ≤ 18446744073709551615) ->
        ((CollectionsRingBufferRingBuffer.tl old₀) ≥ 0) ->
         ((CollectionsRingBufferRingBuffer.tl old₀) ≤ 18446744073709551615) ->
          (∀ (a'₀ : Int),
           ((k0 a'₀ (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀)))) ∧
          (∀ (o₀ : Int),
           (o₀ = (collections_sslice_get (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀))) ->
            ((k0 o₀ (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀))) ->
             ∀ (a'₂ : Int),
              (a'₂ ≥ 0) ->
               (a'₂ ≤ 18446744073709551615) ->
                (((((CollectionsRingBufferRingBuffer.hd old₀) + 1) ≥ 0) ∧ (((CollectionsRingBufferRingBuffer.hd old₀) + 1) ≤ 18446744073709551615)) -> (a'₂ = ((CollectionsRingBufferRingBuffer.hd old₀) + 1))) ->
                 ((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)) ≥ 0) ->
                  ((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)) ≤ 18446744073709551615) ->
                   (((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)) ≠ 0)) ∧
                   (((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)) ≠ 0) ->
                    (((k1 o₀ (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀) o₀ a'₂))) ∧
                    (((a'₂ % (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀))) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)))) ∧
                    (((0 ≤ (a'₂ % (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀))))) ∧
                    (((a'₂ % (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀))) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀))))
                    ) ∧
                    (∀ (a'₃ : Int),
                     ((k1 a'₃ (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀) o₀ a'₂)) ->
                      (a'₃ = (collections_sslice_get (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀)))) ∧
                    ((True = ((CollectionsRingBufferRingBuffer.hd old₀) ≠ (CollectionsRingBufferRingBuffer.tl old₀)))) ∧
                    (((CollectionsRingBufferRingBuffer.ring old₀) = (CollectionsRingBufferRingBuffer.ring (if ((CollectionsRingBufferRingBuffer.hd old₀) ≠ (CollectionsRingBufferRingBuffer.tl old₀)) then (CollectionsRingBufferRingBuffer.mkCollectionsRingBufferRingBuffer₀ (CollectionsRingBufferRingBuffer.ring old₀) (((CollectionsRingBufferRingBuffer.hd old₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀))) (CollectionsRingBufferRingBuffer.tl old₀)) else old₀)))) ∧
                    (((a'₂ % (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀))) = (CollectionsRingBufferRingBuffer.hd (if ((CollectionsRingBufferRingBuffer.hd old₀) ≠ (CollectionsRingBufferRingBuffer.tl old₀)) then (CollectionsRingBufferRingBuffer.mkCollectionsRingBufferRingBuffer₀ (CollectionsRingBufferRingBuffer.ring old₀) (((CollectionsRingBufferRingBuffer.hd old₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀))) (CollectionsRingBufferRingBuffer.tl old₀)) else old₀)))) ∧
                    (((CollectionsRingBufferRingBuffer.tl old₀) = (CollectionsRingBufferRingBuffer.tl (if ((CollectionsRingBufferRingBuffer.hd old₀) ≠ (CollectionsRingBufferRingBuffer.tl old₀)) then (CollectionsRingBufferRingBuffer.mkCollectionsRingBufferRingBuffer₀ (CollectionsRingBufferRingBuffer.ring old₀) (((CollectionsRingBufferRingBuffer.hd old₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀))) (CollectionsRingBufferRingBuffer.tl old₀)) else old₀))))
                    )
                   )
          )
     
end F
