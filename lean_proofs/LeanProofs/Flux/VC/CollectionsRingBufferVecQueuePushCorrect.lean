import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Slc
import LeanProofs.Flux.Struct.CollectionsRingBufferRingBuffer
import LeanProofs.User.Fun.CollectionsSsliceLen
import LeanProofs.User.Fun.CollectionsSsliceSet
import LeanProofs.User.Fun.CollectionsSslicePush
import LeanProofs.User.Fun.CollectionsSsliceAppend
import LeanProofs.User.Fun.CollectionsSsliceSubslice
open Classical
set_option linter.unusedVariables false


namespace F



def CollectionsRingBufferVecQueuePushCorrect := 
 ∀ (rb₀ : (CollectionsRingBufferRingBuffer Int)),
  ∀ (vq₀ : (Slc Int)),
   ∀ (e₀ : Int),
    (vq₀ = (if ((CollectionsRingBufferRingBuffer.hd rb₀) > (CollectionsRingBufferRingBuffer.tl rb₀)) then (collections_sslice_append (t0 := _) (collections_sslice_subslice (t0 := _) (CollectionsRingBufferRingBuffer.ring rb₀) (CollectionsRingBufferRingBuffer.hd rb₀) (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring rb₀))) (collections_sslice_subslice (t0 := _) (CollectionsRingBufferRingBuffer.ring rb₀) 0 (CollectionsRingBufferRingBuffer.tl rb₀))) else (collections_sslice_subslice (t0 := _) (CollectionsRingBufferRingBuffer.ring rb₀) (CollectionsRingBufferRingBuffer.hd rb₀) (CollectionsRingBufferRingBuffer.tl rb₀)))) ->
     ((0 ≤ (CollectionsRingBufferRingBuffer.tl rb₀)) ∧ ((CollectionsRingBufferRingBuffer.tl rb₀) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring rb₀)))) ->
      ((0 ≤ (CollectionsRingBufferRingBuffer.hd rb₀)) ∧ ((CollectionsRingBufferRingBuffer.hd rb₀) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring rb₀)))) ->
       ((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring rb₀)) > 1) ->
        ∀ (success₀ : Prop),
         ∀ (nrb₀ : (CollectionsRingBufferRingBuffer Int)),
          ((0 ≤ (CollectionsRingBufferRingBuffer.tl nrb₀)) ∧ ((CollectionsRingBufferRingBuffer.tl nrb₀) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring nrb₀)))) ->
           ((0 ≤ (CollectionsRingBufferRingBuffer.hd nrb₀)) ∧ ((CollectionsRingBufferRingBuffer.hd nrb₀) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring nrb₀)))) ->
            ((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring nrb₀)) > 1) ->
             (success₀ = ((CollectionsRingBufferRingBuffer.hd rb₀) ≠ (((CollectionsRingBufferRingBuffer.tl rb₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring rb₀))))) ->
              (nrb₀ = (if ((CollectionsRingBufferRingBuffer.hd rb₀) ≠ (((CollectionsRingBufferRingBuffer.tl rb₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring rb₀)))) then (CollectionsRingBufferRingBuffer.mkCollectionsRingBufferRingBuffer₀ (collections_sslice_set (t0 := _) (CollectionsRingBufferRingBuffer.ring rb₀) (CollectionsRingBufferRingBuffer.tl rb₀) e₀) (if ((CollectionsRingBufferRingBuffer.hd rb₀) = (((CollectionsRingBufferRingBuffer.tl rb₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring rb₀)))) then (((CollectionsRingBufferRingBuffer.hd rb₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring rb₀))) else (CollectionsRingBufferRingBuffer.hd rb₀)) (((CollectionsRingBufferRingBuffer.tl rb₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring rb₀)))) else rb₀)) ->
               success₀ ->
                ((collections_sslice_push (t0 := Int) vq₀ e₀) = (if ((CollectionsRingBufferRingBuffer.hd nrb₀) > (CollectionsRingBufferRingBuffer.tl nrb₀)) then (collections_sslice_append (t0 := _) (collections_sslice_subslice (t0 := _) (CollectionsRingBufferRingBuffer.ring nrb₀) (CollectionsRingBufferRingBuffer.hd nrb₀) (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring nrb₀))) (collections_sslice_subslice (t0 := _) (CollectionsRingBufferRingBuffer.ring nrb₀) 0 (CollectionsRingBufferRingBuffer.tl nrb₀))) else (collections_sslice_subslice (t0 := _) (CollectionsRingBufferRingBuffer.ring nrb₀) (CollectionsRingBufferRingBuffer.hd nrb₀) (CollectionsRingBufferRingBuffer.tl nrb₀))))
end F
