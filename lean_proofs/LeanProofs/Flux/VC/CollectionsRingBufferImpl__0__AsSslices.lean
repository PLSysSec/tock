import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Slc
import LeanProofs.Flux.Struct.CollectionsRingBufferRingBuffer
import LeanProofs.User.Fun.CollectionsSsliceLen
import LeanProofs.User.Fun.CollectionsSsliceSubslice
open Classical
set_option linter.unusedVariables false


namespace F



def CollectionsRingBufferImpl__0__AsSslices := ∃ k0 : (a0 : (Slc Int)) -> (a1 : (Slc Int)) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : (Slc Int)) -> (a1 : (Slc Int)) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k2 : (a0 : Prop) -> (a1 : (Slc Int)) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k3 : (a0 : (Slc Int)) -> (a1 : Prop) -> (a2 : (Slc Int)) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k4 : (a0 : (Slc Int)) -> (a1 : Prop) -> (a2 : (Slc Int)) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k5 : (a0 : (Slc Int)) -> (a1 : (Slc Int)) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (slf₀ : (CollectionsRingBufferRingBuffer Int)),
  ((0 ≤ (CollectionsRingBufferRingBuffer.tl slf₀)) ∧ ((CollectionsRingBufferRingBuffer.tl slf₀) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring slf₀)))) ->
   ((0 ≤ (CollectionsRingBufferRingBuffer.hd slf₀)) ∧ ((CollectionsRingBufferRingBuffer.hd slf₀) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring slf₀)))) ->
    ((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring slf₀)) > 1) ->
     ((CollectionsRingBufferRingBuffer.hd slf₀) ≥ 0) ->
      ((CollectionsRingBufferRingBuffer.hd slf₀) ≤ 18446744073709551615) ->
       ((CollectionsRingBufferRingBuffer.tl slf₀) ≥ 0) ->
        ((CollectionsRingBufferRingBuffer.tl slf₀) ≤ 18446744073709551615) ->
         ((¬((CollectionsRingBufferRingBuffer.hd slf₀) < (CollectionsRingBufferRingBuffer.tl slf₀))) ->
          ((CollectionsRingBufferRingBuffer.hd slf₀) > (CollectionsRingBufferRingBuffer.tl slf₀)) ->
           (((k0 (collections_sslice_subslice (t0 := Int) (CollectionsRingBufferRingBuffer.ring slf₀) (CollectionsRingBufferRingBuffer.hd slf₀) (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring slf₀))) (CollectionsRingBufferRingBuffer.ring slf₀) (CollectionsRingBufferRingBuffer.hd slf₀) (CollectionsRingBufferRingBuffer.tl slf₀)))) ∧
           (((CollectionsRingBufferRingBuffer.tl slf₀) ≠ 0) ->
            ((0 < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring slf₀)))) ∧
            (((k1 (collections_sslice_subslice (t0 := Int) (CollectionsRingBufferRingBuffer.ring slf₀) 0 (CollectionsRingBufferRingBuffer.tl slf₀)) (CollectionsRingBufferRingBuffer.ring slf₀) (CollectionsRingBufferRingBuffer.hd slf₀) (CollectionsRingBufferRingBuffer.tl slf₀)))) ∧
            (((k2 True (CollectionsRingBufferRingBuffer.ring slf₀) (CollectionsRingBufferRingBuffer.hd slf₀) (CollectionsRingBufferRingBuffer.tl slf₀)))) ∧
            (∀ (a'₀ : (Slc Int)),
             ((k0 a'₀ (CollectionsRingBufferRingBuffer.ring slf₀) (CollectionsRingBufferRingBuffer.hd slf₀) (CollectionsRingBufferRingBuffer.tl slf₀))) ->
              ((k3 a'₀ True (CollectionsRingBufferRingBuffer.ring slf₀) (CollectionsRingBufferRingBuffer.hd slf₀) (CollectionsRingBufferRingBuffer.tl slf₀)))) ∧
            (∀ (a'₁ : (Slc Int)),
             ((k1 a'₁ (CollectionsRingBufferRingBuffer.ring slf₀) (CollectionsRingBufferRingBuffer.hd slf₀) (CollectionsRingBufferRingBuffer.tl slf₀))) ->
              ((k4 a'₁ True (CollectionsRingBufferRingBuffer.ring slf₀) (CollectionsRingBufferRingBuffer.hd slf₀) (CollectionsRingBufferRingBuffer.tl slf₀))))
            ) ∧
           ((¬((CollectionsRingBufferRingBuffer.tl slf₀) ≠ 0)) ->
            (((k2 False (CollectionsRingBufferRingBuffer.ring slf₀) (CollectionsRingBufferRingBuffer.hd slf₀) (CollectionsRingBufferRingBuffer.tl slf₀)))) ∧
            (∀ (a'₂ : (Slc Int)),
             ((k0 a'₂ (CollectionsRingBufferRingBuffer.ring slf₀) (CollectionsRingBufferRingBuffer.hd slf₀) (CollectionsRingBufferRingBuffer.tl slf₀))) ->
              ((k3 a'₂ False (CollectionsRingBufferRingBuffer.ring slf₀) (CollectionsRingBufferRingBuffer.hd slf₀) (CollectionsRingBufferRingBuffer.tl slf₀))))
            ) ∧
           (∀ (a'₃ : Prop),
            ((k2 a'₃ (CollectionsRingBufferRingBuffer.ring slf₀) (CollectionsRingBufferRingBuffer.hd slf₀) (CollectionsRingBufferRingBuffer.tl slf₀))) ->
             (∀ (a'₄ : (Slc Int)),
              ((k3 a'₄ a'₃ (CollectionsRingBufferRingBuffer.ring slf₀) (CollectionsRingBufferRingBuffer.hd slf₀) (CollectionsRingBufferRingBuffer.tl slf₀))) ->
               ((CollectionsRingBufferRingBuffer.hd slf₀) < (CollectionsRingBufferRingBuffer.tl slf₀)) ->
                (a'₄ = (collections_sslice_subslice (t0 := Int) (CollectionsRingBufferRingBuffer.ring slf₀) (CollectionsRingBufferRingBuffer.hd slf₀) (CollectionsRingBufferRingBuffer.tl slf₀))) ->
                 (a'₄ = (collections_sslice_subslice (t0 := Int) (CollectionsRingBufferRingBuffer.ring slf₀) (CollectionsRingBufferRingBuffer.hd slf₀) (collections_sslice_len (t0 := Int) a'₄)))) ∧
             (∀ (a'₅ : (Slc Int)),
              ((k4 a'₅ a'₃ (CollectionsRingBufferRingBuffer.ring slf₀) (CollectionsRingBufferRingBuffer.hd slf₀) (CollectionsRingBufferRingBuffer.tl slf₀))) ->
               (a'₅ = (collections_sslice_subslice (t0 := Int) (CollectionsRingBufferRingBuffer.ring slf₀) 0 (CollectionsRingBufferRingBuffer.tl slf₀))))
             )
           ) ∧
         (((CollectionsRingBufferRingBuffer.hd slf₀) < (CollectionsRingBufferRingBuffer.tl slf₀)) ->
          (((CollectionsRingBufferRingBuffer.hd slf₀) ≤ (CollectionsRingBufferRingBuffer.tl slf₀))) ∧
          (((k5 (collections_sslice_subslice (t0 := Int) (CollectionsRingBufferRingBuffer.ring slf₀) (CollectionsRingBufferRingBuffer.hd slf₀) (CollectionsRingBufferRingBuffer.tl slf₀)) (CollectionsRingBufferRingBuffer.ring slf₀) (CollectionsRingBufferRingBuffer.hd slf₀) (CollectionsRingBufferRingBuffer.tl slf₀)))) ∧
          (∀ (a'₆ : (Slc Int)),
           ((k5 a'₆ (CollectionsRingBufferRingBuffer.ring slf₀) (CollectionsRingBufferRingBuffer.hd slf₀) (CollectionsRingBufferRingBuffer.tl slf₀))) ->
            ((a'₆ = (collections_sslice_subslice (t0 := Int) (CollectionsRingBufferRingBuffer.ring slf₀) (CollectionsRingBufferRingBuffer.hd slf₀) (CollectionsRingBufferRingBuffer.tl slf₀))) ∧ ((CollectionsRingBufferRingBuffer.hd slf₀) > (CollectionsRingBufferRingBuffer.tl slf₀))) ->
             (a'₆ = (collections_sslice_subslice (t0 := Int) (CollectionsRingBufferRingBuffer.ring slf₀) (CollectionsRingBufferRingBuffer.hd slf₀) (collections_sslice_len (t0 := Int) a'₆))))
          )
         
end F
