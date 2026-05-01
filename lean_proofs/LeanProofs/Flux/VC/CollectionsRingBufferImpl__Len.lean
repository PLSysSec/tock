import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Slc
import LeanProofs.Flux.Struct.CollectionsRingBufferRingBuffer
import LeanProofs.User.Fun.CollectionsSsliceLen
open Classical

namespace F



def CollectionsRingBufferImpl__Len := ∃ k0 : (a0 : Int) -> (a1 : (Slc Int)) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (rb₀ : (CollectionsRingBufferRingBuffer Int)),
  ((0 ≤ (CollectionsRingBufferRingBuffer.tl rb₀)) ∧ ((CollectionsRingBufferRingBuffer.tl rb₀) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring rb₀)))) ->
   ((0 ≤ (CollectionsRingBufferRingBuffer.hd rb₀)) ∧ ((CollectionsRingBufferRingBuffer.hd rb₀) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring rb₀)))) ->
    ((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring rb₀)) > 1) ->
     ((CollectionsRingBufferRingBuffer.hd rb₀) ≥ 0) ->
      ((CollectionsRingBufferRingBuffer.hd rb₀) ≤ 18446744073709551615) ->
       ((CollectionsRingBufferRingBuffer.tl rb₀) ≥ 0) ->
        ((CollectionsRingBufferRingBuffer.tl rb₀) ≤ 18446744073709551615) ->
         ((¬((CollectionsRingBufferRingBuffer.tl rb₀) > (CollectionsRingBufferRingBuffer.hd rb₀))) ->
          ((¬((CollectionsRingBufferRingBuffer.tl rb₀) < (CollectionsRingBufferRingBuffer.hd rb₀))) ->
           ((k0 0 (CollectionsRingBufferRingBuffer.ring rb₀) (CollectionsRingBufferRingBuffer.hd rb₀) (CollectionsRingBufferRingBuffer.tl rb₀)))) ∧
          (((CollectionsRingBufferRingBuffer.tl rb₀) < (CollectionsRingBufferRingBuffer.hd rb₀)) ->
           ((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring rb₀)) ≥ 0) ->
            ((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring rb₀)) ≤ 18446744073709551615) ->
             ∀ (a'₀ : Int),
              (a'₀ ≥ 0) ->
               (a'₀ ≤ 18446744073709551615) ->
                (((((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring rb₀)) - (CollectionsRingBufferRingBuffer.hd rb₀)) ≥ 0) ∧ (((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring rb₀)) - (CollectionsRingBufferRingBuffer.hd rb₀)) ≤ 18446744073709551615)) -> (a'₀ = ((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring rb₀)) - (CollectionsRingBufferRingBuffer.hd rb₀)))) ->
                 ∀ (a'₁ : Int),
                  (a'₁ ≥ 0) ->
                   (a'₁ ≤ 18446744073709551615) ->
                    ((((a'₀ + (CollectionsRingBufferRingBuffer.tl rb₀)) ≥ 0) ∧ ((a'₀ + (CollectionsRingBufferRingBuffer.tl rb₀)) ≤ 18446744073709551615)) -> (a'₁ = (a'₀ + (CollectionsRingBufferRingBuffer.tl rb₀)))) ->
                     ((k0 a'₁ (CollectionsRingBufferRingBuffer.ring rb₀) (CollectionsRingBufferRingBuffer.hd rb₀) (CollectionsRingBufferRingBuffer.tl rb₀)))) ∧
          (∀ (a'₂ : Int),
           ((k0 a'₂ (CollectionsRingBufferRingBuffer.ring rb₀) (CollectionsRingBufferRingBuffer.hd rb₀) (CollectionsRingBufferRingBuffer.tl rb₀))) ->
            (((CollectionsRingBufferRingBuffer.tl rb₀) > (CollectionsRingBufferRingBuffer.hd rb₀)) ->
             (a'₂ = ((CollectionsRingBufferRingBuffer.tl rb₀) - (CollectionsRingBufferRingBuffer.hd rb₀)))) ∧
            (((CollectionsRingBufferRingBuffer.tl rb₀) < (CollectionsRingBufferRingBuffer.hd rb₀)) ->
             (a'₂ = (((collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring rb₀)) - (CollectionsRingBufferRingBuffer.hd rb₀)) + (CollectionsRingBufferRingBuffer.tl rb₀)))) ∧
            (((CollectionsRingBufferRingBuffer.hd rb₀) = (CollectionsRingBufferRingBuffer.tl rb₀)) ->
             (a'₂ = 0))
            )
          ) ∧
         (((CollectionsRingBufferRingBuffer.tl rb₀) > (CollectionsRingBufferRingBuffer.hd rb₀)) ->
          ∀ (a'₃ : Int),
           (a'₃ ≥ 0) ->
            (a'₃ ≤ 18446744073709551615) ->
             (((((CollectionsRingBufferRingBuffer.tl rb₀) - (CollectionsRingBufferRingBuffer.hd rb₀)) ≥ 0) ∧ (((CollectionsRingBufferRingBuffer.tl rb₀) - (CollectionsRingBufferRingBuffer.hd rb₀)) ≤ 18446744073709551615)) -> (a'₃ = ((CollectionsRingBufferRingBuffer.tl rb₀) - (CollectionsRingBufferRingBuffer.hd rb₀)))) ->
              ((a'₃ = ((CollectionsRingBufferRingBuffer.tl rb₀) - (CollectionsRingBufferRingBuffer.hd rb₀)))) ∧
              (((CollectionsRingBufferRingBuffer.tl rb₀) < (CollectionsRingBufferRingBuffer.hd rb₀)) ->
               (a'₃ = (((collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring rb₀)) - (CollectionsRingBufferRingBuffer.hd rb₀)) + (CollectionsRingBufferRingBuffer.tl rb₀)))) ∧
              (((CollectionsRingBufferRingBuffer.hd rb₀) = (CollectionsRingBufferRingBuffer.tl rb₀)) ->
               (a'₃ = 0))
              )
         
end F
