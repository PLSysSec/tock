import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Slc
import LeanProofs.Flux.Struct.CollectionsRingBufferRingBuffer
import LeanProofs.User.Fun.CollectionsSsliceLen
open Classical

namespace F



def CollectionsRingBufferImpl__0__New := 
 ∀ (rl₀ : Int),
  (rl₀ > 1) ->
   (rl₀ ≥ 0) ->
    (rl₀ ≤ 18446744073709551615) ->
     ∀ (v₀ : (Slc Int)),
      ((collections_sslice_len v₀) = rl₀) ->
       ((0 < (collections_sslice_len v₀))) ∧
       ((0 < (collections_sslice_len v₀))) ∧
       (((collections_sslice_len v₀) > 1)) ∧
       (((collections_sslice_len v₀) > 1)) ∧
       ((0 < (collections_sslice_len v₀))) ∧
       ((0 < (collections_sslice_len v₀))) ∧
       (((collections_sslice_len (CollectionsRingBufferRingBuffer.ring (CollectionsRingBufferRingBuffer.mkCollectionsRingBufferRingBuffer₀ v₀ 0 0))) = rl₀))
       
end F
