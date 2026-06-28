import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Slc
import LeanProofs.Flux.Struct.CollectionsRingBufferRingBuffer
import LeanProofs.User.Fun.CollectionsSsliceLen
import LeanProofs.User.Fun.CollectionsSsliceSet
open Classical
set_option linter.unusedVariables false


namespace F



def CollectionsRingBufferImpl__1__Enqueue := 
 ∀ (old₀ : (CollectionsRingBufferRingBuffer Int)),
  ∀ (val₀ : Int),
   ((0 ≤ (CollectionsRingBufferRingBuffer.tl old₀)) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)))) ->
    ((0 ≤ (CollectionsRingBufferRingBuffer.hd old₀)) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)))) ->
     ((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)) > 1) ->
      (((CollectionsRingBufferRingBuffer.hd old₀) ≠ (((CollectionsRingBufferRingBuffer.tl old₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀)))) ->
       ((CollectionsRingBufferRingBuffer.hd old₀) ≥ 0) ->
        ((CollectionsRingBufferRingBuffer.hd old₀) ≤ 18446744073709551615) ->
         ((CollectionsRingBufferRingBuffer.tl old₀) ≥ 0) ->
          ((CollectionsRingBufferRingBuffer.tl old₀) ≤ 18446744073709551615) ->
           ∀ (a'₀ : Int),
            (a'₀ ≥ 0) ->
             (a'₀ ≤ 18446744073709551615) ->
              (((((CollectionsRingBufferRingBuffer.tl old₀) + 1) ≥ 0) ∧ (((CollectionsRingBufferRingBuffer.tl old₀) + 1) ≤ 18446744073709551615)) -> (a'₀ = ((CollectionsRingBufferRingBuffer.tl old₀) + 1))) ->
               ((collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀)) ≥ 0) ->
                ((collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀)) ≤ 18446744073709551615) ->
                 (((collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀)) ≠ 0)) ∧
                 (((collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀)) ≠ 0) ->
                  (((collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀)) > 1)) ∧
                  (((CollectionsRingBufferRingBuffer.hd old₀) < (collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀)))) ∧
                  (((a'₀ % (collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀))) < (collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀)))) ∧
                  (((0 ≤ (a'₀ % (collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀))))) ∧
                  (((a'₀ % (collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀))) < (collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀))))
                  ) ∧
                  (((CollectionsRingBufferRingBuffer.hd old₀) < (collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀)))) ∧
                  (((collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀)) > 1)) ∧
                  ((True = ((CollectionsRingBufferRingBuffer.hd old₀) ≠ (((CollectionsRingBufferRingBuffer.tl old₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀)))))) ∧
                  (((CollectionsRingBufferRingBuffer.mkCollectionsRingBufferRingBuffer₀ (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀) (CollectionsRingBufferRingBuffer.hd old₀) (a'₀ % (collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀)))) = (if ((CollectionsRingBufferRingBuffer.hd old₀) ≠ (((CollectionsRingBufferRingBuffer.tl old₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀)))) then (CollectionsRingBufferRingBuffer.mkCollectionsRingBufferRingBuffer₀ (collections_sslice_set (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀) (if ((CollectionsRingBufferRingBuffer.hd old₀) = (((CollectionsRingBufferRingBuffer.tl old₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀)))) then (((CollectionsRingBufferRingBuffer.hd old₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀))) else (CollectionsRingBufferRingBuffer.hd old₀)) (((CollectionsRingBufferRingBuffer.tl old₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀)))) else old₀)))
                  )
                 ) ∧
      ((¬((CollectionsRingBufferRingBuffer.hd old₀) ≠ (((CollectionsRingBufferRingBuffer.tl old₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀))))) ->
       ((False = ((CollectionsRingBufferRingBuffer.hd old₀) ≠ (((CollectionsRingBufferRingBuffer.tl old₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀)))))) ∧
       ((old₀ = (if ((CollectionsRingBufferRingBuffer.hd old₀) ≠ (((CollectionsRingBufferRingBuffer.tl old₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀)))) then (CollectionsRingBufferRingBuffer.mkCollectionsRingBufferRingBuffer₀ (collections_sslice_set (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀) (if ((CollectionsRingBufferRingBuffer.hd old₀) = (((CollectionsRingBufferRingBuffer.tl old₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀)))) then (((CollectionsRingBufferRingBuffer.hd old₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀))) else (CollectionsRingBufferRingBuffer.hd old₀)) (((CollectionsRingBufferRingBuffer.tl old₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀)))) else old₀)))
       )
      
end F
