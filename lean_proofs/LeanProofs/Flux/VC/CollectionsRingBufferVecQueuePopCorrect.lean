import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Slc
import LeanProofs.Flux.Struct.CollectionsRingBufferRingBuffer
import LeanProofs.User.Fun.CollectionsSsliceLen
import LeanProofs.User.Fun.CollectionsSslicePopFront
import LeanProofs.User.Fun.CollectionsSsliceAppend
import LeanProofs.User.Fun.CollectionsSsliceSubslice
open Classical

namespace F



def CollectionsRingBufferVecQueuePopCorrect := 
 ∀ (rb₀ : (CollectionsRingBufferRingBuffer Int)),
  ∀ (vq₀ : (Slc Int)),
   (((CollectionsRingBufferRingBuffer.hd rb₀) > (CollectionsRingBufferRingBuffer.tl rb₀)) -> ((collections_sslice_append (collections_sslice_subslice (CollectionsRingBufferRingBuffer.ring rb₀) (CollectionsRingBufferRingBuffer.hd rb₀) (collections_sslice_len (CollectionsRingBufferRingBuffer.ring rb₀))) (collections_sslice_subslice (CollectionsRingBufferRingBuffer.ring rb₀) 0 (CollectionsRingBufferRingBuffer.tl rb₀))) = vq₀)) ->
    (((CollectionsRingBufferRingBuffer.hd rb₀) ≤ (CollectionsRingBufferRingBuffer.tl rb₀)) -> ((collections_sslice_subslice (CollectionsRingBufferRingBuffer.ring rb₀) (CollectionsRingBufferRingBuffer.hd rb₀) (CollectionsRingBufferRingBuffer.tl rb₀)) = vq₀)) ->
     ((CollectionsRingBufferRingBuffer.hd rb₀) ≠ (CollectionsRingBufferRingBuffer.tl rb₀)) ->
      ((collections_sslice_len vq₀) > 0) ->
       ((0 ≤ (CollectionsRingBufferRingBuffer.tl rb₀)) ∧ ((CollectionsRingBufferRingBuffer.tl rb₀) < (collections_sslice_len (CollectionsRingBufferRingBuffer.ring rb₀)))) ->
        ((0 ≤ (CollectionsRingBufferRingBuffer.hd rb₀)) ∧ ((CollectionsRingBufferRingBuffer.hd rb₀) < (collections_sslice_len (CollectionsRingBufferRingBuffer.ring rb₀)))) ->
         ((collections_sslice_len (CollectionsRingBufferRingBuffer.ring rb₀)) > 1) ->
          ∀ (res₀ : Prop),
           ∀ (new₀ : (CollectionsRingBufferRingBuffer Int)),
            ((0 ≤ (CollectionsRingBufferRingBuffer.tl new₀)) ∧ ((CollectionsRingBufferRingBuffer.tl new₀) < (collections_sslice_len (CollectionsRingBufferRingBuffer.ring new₀)))) ->
             ((0 ≤ (CollectionsRingBufferRingBuffer.hd new₀)) ∧ ((CollectionsRingBufferRingBuffer.hd new₀) < (collections_sslice_len (CollectionsRingBufferRingBuffer.ring new₀)))) ->
              ((collections_sslice_len (CollectionsRingBufferRingBuffer.ring new₀)) > 1) ->
               (res₀ = ((CollectionsRingBufferRingBuffer.hd rb₀) ≠ (CollectionsRingBufferRingBuffer.tl rb₀))) ->
                ((CollectionsRingBufferRingBuffer.tl new₀) = (CollectionsRingBufferRingBuffer.tl rb₀)) ->
                 ((CollectionsRingBufferRingBuffer.ring new₀) = (CollectionsRingBufferRingBuffer.ring rb₀)) ->
                  (res₀ -> ((CollectionsRingBufferRingBuffer.hd new₀) = (((CollectionsRingBufferRingBuffer.hd rb₀) + 1) % (collections_sslice_len (CollectionsRingBufferRingBuffer.ring rb₀))))) ->
                   ((¬res₀) -> ((CollectionsRingBufferRingBuffer.hd new₀) = (CollectionsRingBufferRingBuffer.hd rb₀))) ->
                    (((CollectionsRingBufferRingBuffer.hd new₀) > (CollectionsRingBufferRingBuffer.tl new₀)) ->
                     ((collections_sslice_append (collections_sslice_subslice (CollectionsRingBufferRingBuffer.ring new₀) (CollectionsRingBufferRingBuffer.hd new₀) (collections_sslice_len (CollectionsRingBufferRingBuffer.ring new₀))) (collections_sslice_subslice (CollectionsRingBufferRingBuffer.ring new₀) 0 (CollectionsRingBufferRingBuffer.tl new₀))) = (collections_sslice_pop_front vq₀))) ∧
                    (((CollectionsRingBufferRingBuffer.hd new₀) ≤ (CollectionsRingBufferRingBuffer.tl new₀)) ->
                     ((collections_sslice_subslice (CollectionsRingBufferRingBuffer.ring new₀) (CollectionsRingBufferRingBuffer.hd new₀) (CollectionsRingBufferRingBuffer.tl new₀)) = (collections_sslice_pop_front vq₀)))
                    
end F
