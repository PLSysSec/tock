import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Slc
import LeanProofs.Flux.Struct.CollectionsRingBufferRingBuffer
import LeanProofs.User.Fun.CollectionsSsliceLen
open Classical

namespace F



def CollectionsRingBufferImpl__IsFull := 
 ∀ (rb₀ : (CollectionsRingBufferRingBuffer Int)),
  ((0 ≤ (CollectionsRingBufferRingBuffer.tl rb₀)) ∧ ((CollectionsRingBufferRingBuffer.tl rb₀) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring rb₀)))) ->
   ((0 ≤ (CollectionsRingBufferRingBuffer.hd rb₀)) ∧ ((CollectionsRingBufferRingBuffer.hd rb₀) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring rb₀)))) ->
    ((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring rb₀)) > 1) ->
     ((CollectionsRingBufferRingBuffer.hd rb₀) ≥ 0) ->
      ((CollectionsRingBufferRingBuffer.hd rb₀) ≤ 18446744073709551615) ->
       ((CollectionsRingBufferRingBuffer.tl rb₀) ≥ 0) ->
        ((CollectionsRingBufferRingBuffer.tl rb₀) ≤ 18446744073709551615) ->
         ∀ (a'₀ : Int),
          (a'₀ ≥ 0) ->
           (a'₀ ≤ 18446744073709551615) ->
            (((((CollectionsRingBufferRingBuffer.tl rb₀) + 1) ≥ 0) ∧ (((CollectionsRingBufferRingBuffer.tl rb₀) + 1) ≤ 18446744073709551615)) -> (a'₀ = ((CollectionsRingBufferRingBuffer.tl rb₀) + 1))) ->
             ((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring rb₀)) ≥ 0) ->
              ((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring rb₀)) ≤ 18446744073709551615) ->
               (((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring rb₀)) ≠ 0)) ∧
               (((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring rb₀)) ≠ 0) ->
                (((CollectionsRingBufferRingBuffer.hd rb₀) = (a'₀ % (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring rb₀)))) = ((CollectionsRingBufferRingBuffer.hd rb₀) = (((CollectionsRingBufferRingBuffer.tl rb₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring rb₀))))))
               
end F
