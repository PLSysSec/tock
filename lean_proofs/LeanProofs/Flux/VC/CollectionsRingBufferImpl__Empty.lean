import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Slc
import LeanProofs.Flux.Struct.CollectionsRingBufferRingBuffer
import LeanProofs.User.Fun.CollectionsSsliceLen
open Classical

namespace F



def CollectionsRingBufferImpl__Empty := 
 ∀ (old₀ : (CollectionsRingBufferRingBuffer Int)),
  ((0 ≤ (CollectionsRingBufferRingBuffer.tl old₀)) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)))) ->
   ((0 ≤ (CollectionsRingBufferRingBuffer.hd old₀)) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)))) ->
    ((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)) > 1) ->
     ((CollectionsRingBufferRingBuffer.hd old₀) ≥ 0) ->
      ((CollectionsRingBufferRingBuffer.hd old₀) ≤ 18446744073709551615) ->
       ((CollectionsRingBufferRingBuffer.tl old₀) ≥ 0) ->
        ((CollectionsRingBufferRingBuffer.tl old₀) ≤ 18446744073709551615) ->
         ((0 < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)))) ∧
         ((0 < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)))) ∧
         ((0 < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)))) ∧
         ((0 < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀))))
         
end F
