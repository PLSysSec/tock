import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Slc
import LeanProofs.Flux.Struct.CollectionsRingBufferRingBuffer
import LeanProofs.User.Fun.CollectionsSsliceLen
import LeanProofs.User.Fun.CollectionsSsliceSet
import LeanProofs.User.Fun.CollectionsSslicePush
import LeanProofs.User.Fun.CollectionsSsliceAppend
import LeanProofs.User.Fun.CollectionsSsliceSubslice
open Classical

namespace F



def CollectionsRingBufferVecQueuePushCorrect := 
 ∀ (rb₀ : (CollectionsRingBufferRingBuffer Int)),
  ∀ (vq₀ : (Slc Int)),
   ∀ (e₀ : Int),
    (((CollectionsRingBufferRingBuffer.hd rb₀) > (CollectionsRingBufferRingBuffer.tl rb₀)) -> ((collections_sslice_append (collections_sslice_subslice (CollectionsRingBufferRingBuffer.ring rb₀) (CollectionsRingBufferRingBuffer.hd rb₀) (collections_sslice_len (CollectionsRingBufferRingBuffer.ring rb₀))) (collections_sslice_subslice (CollectionsRingBufferRingBuffer.ring rb₀) 0 (CollectionsRingBufferRingBuffer.tl rb₀))) = vq₀)) ->
     (((CollectionsRingBufferRingBuffer.hd rb₀) ≤ (CollectionsRingBufferRingBuffer.tl rb₀)) -> ((collections_sslice_subslice (CollectionsRingBufferRingBuffer.ring rb₀) (CollectionsRingBufferRingBuffer.hd rb₀) (CollectionsRingBufferRingBuffer.tl rb₀)) = vq₀)) ->
      ((0 ≤ (CollectionsRingBufferRingBuffer.tl rb₀)) ∧ ((CollectionsRingBufferRingBuffer.tl rb₀) < (collections_sslice_len (CollectionsRingBufferRingBuffer.ring rb₀)))) ->
       ((0 ≤ (CollectionsRingBufferRingBuffer.hd rb₀)) ∧ ((CollectionsRingBufferRingBuffer.hd rb₀) < (collections_sslice_len (CollectionsRingBufferRingBuffer.ring rb₀)))) ->
        ((collections_sslice_len (CollectionsRingBufferRingBuffer.ring rb₀)) > 1) ->
         ∀ (success₀ : Prop),
          ∀ (new₀ : (CollectionsRingBufferRingBuffer Int)),
           ((0 ≤ (CollectionsRingBufferRingBuffer.tl new₀)) ∧ ((CollectionsRingBufferRingBuffer.tl new₀) < (collections_sslice_len (CollectionsRingBufferRingBuffer.ring new₀)))) ->
            ((0 ≤ (CollectionsRingBufferRingBuffer.hd new₀)) ∧ ((CollectionsRingBufferRingBuffer.hd new₀) < (collections_sslice_len (CollectionsRingBufferRingBuffer.ring new₀)))) ->
             ((collections_sslice_len (CollectionsRingBufferRingBuffer.ring new₀)) > 1) ->
              (success₀ = ((CollectionsRingBufferRingBuffer.hd rb₀) ≠ (((CollectionsRingBufferRingBuffer.tl rb₀) + 1) % (collections_sslice_len (CollectionsRingBufferRingBuffer.ring rb₀))))) ->
               ((¬success₀) -> (new₀ = rb₀)) ->
                (success₀ -> ((((CollectionsRingBufferRingBuffer.hd new₀) = (CollectionsRingBufferRingBuffer.hd rb₀)) ∧ ((CollectionsRingBufferRingBuffer.tl new₀) = (((CollectionsRingBufferRingBuffer.tl rb₀) + 1) % (collections_sslice_len (CollectionsRingBufferRingBuffer.ring rb₀))))) ∧ ((CollectionsRingBufferRingBuffer.ring new₀) = (collections_sslice_set (CollectionsRingBufferRingBuffer.ring rb₀) (CollectionsRingBufferRingBuffer.tl rb₀) e₀)))) ->
                 ((success₀ ∧ ((CollectionsRingBufferRingBuffer.hd new₀) > (CollectionsRingBufferRingBuffer.tl new₀))) ->
                  ((collections_sslice_append (collections_sslice_subslice (CollectionsRingBufferRingBuffer.ring new₀) (CollectionsRingBufferRingBuffer.hd new₀) (collections_sslice_len (CollectionsRingBufferRingBuffer.ring new₀))) (collections_sslice_subslice (CollectionsRingBufferRingBuffer.ring new₀) 0 (CollectionsRingBufferRingBuffer.tl new₀))) = (collections_sslice_push vq₀ e₀))) ∧
                 ((success₀ ∧ ((CollectionsRingBufferRingBuffer.hd new₀) ≤ (CollectionsRingBufferRingBuffer.tl new₀))) ->
                  ((collections_sslice_subslice (CollectionsRingBufferRingBuffer.ring new₀) (CollectionsRingBufferRingBuffer.hd new₀) (CollectionsRingBufferRingBuffer.tl new₀)) = (collections_sslice_push vq₀ e₀)))
                 
end F
