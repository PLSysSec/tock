import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Slc
import LeanProofs.Flux.Struct.CollectionsRingBufferRingBuffer
import LeanProofs.User.Fun.CollectionsSsliceLen
import LeanProofs.User.Fun.CollectionsSsliceSet
import LeanProofs.User.Fun.CollectionsSsliceGet
open Classical
set_option linter.unusedVariables false


namespace F



def CollectionsRingBufferImpl__1__Push := ∃ k0 : (a0 : Prop) -> (a1 : (Slc Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : (Slc Int)) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : (Slc Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : (Slc Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Prop) -> (a2 : (Slc Int)) -> (a3 : Int) -> (a4 : Int) -> (a5 : (Slc Int)) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, 
 ∀ (old₀ : (CollectionsRingBufferRingBuffer Int)),
  ∀ (val₀ : Int),
   ((0 ≤ (CollectionsRingBufferRingBuffer.tl old₀)) ∧ ((CollectionsRingBufferRingBuffer.tl old₀) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)))) ->
    ((0 ≤ (CollectionsRingBufferRingBuffer.hd old₀)) ∧ ((CollectionsRingBufferRingBuffer.hd old₀) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)))) ->
     ((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)) > 1) ->
      (((CollectionsRingBufferRingBuffer.hd old₀) ≠ (((CollectionsRingBufferRingBuffer.tl old₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀)))) ->
       ((k0 False (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀))) ∧
      ((¬((CollectionsRingBufferRingBuffer.hd old₀) ≠ (((CollectionsRingBufferRingBuffer.tl old₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀))))) ->
       ((CollectionsRingBufferRingBuffer.hd old₀) ≥ 0) ->
        ((CollectionsRingBufferRingBuffer.hd old₀) ≤ 18446744073709551615) ->
         ((CollectionsRingBufferRingBuffer.tl old₀) ≥ 0) ->
          ((CollectionsRingBufferRingBuffer.tl old₀) ≤ 18446744073709551615) ->
           (∀ (a'₀ : Int),
            ((k1 a'₀ (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀))) ∧
           (∀ (o₀ : Int),
            (o₀ = (collections_sslice_get (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀))) ->
             ((k1 o₀ (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀)) ->
              ∀ (a'₂ : Int),
               (a'₂ ≥ 0) ->
                (a'₂ ≤ 18446744073709551615) ->
                 (((((CollectionsRingBufferRingBuffer.hd old₀) + 1) ≥ 0) ∧ (((CollectionsRingBufferRingBuffer.hd old₀) + 1) ≤ 18446744073709551615)) -> (a'₂ = ((CollectionsRingBufferRingBuffer.hd old₀) + 1))) ->
                  ((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)) ≥ 0) ->
                   ((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)) ≤ 18446744073709551615) ->
                    (((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)) ≠ 0)) ∧
                    (((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)) ≠ 0) ->
                     (((k2 o₀ (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀ o₀ a'₂))) ∧
                     (((a'₂ % (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀))) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀)))) ∧
                     (((0 ≤ (a'₂ % (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀))))) ∧
                     (((a'₂ % (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀))) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀))))
                     ) ∧
                     (((k0 True (CollectionsRingBufferRingBuffer.ring old₀) (a'₂ % (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀))) (CollectionsRingBufferRingBuffer.tl old₀) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀))) ∧
                     (∀ (a'₃ : Int),
                      ((k2 a'₃ (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀ o₀ a'₂)) ->
                       ((k3 a'₃ True (CollectionsRingBufferRingBuffer.ring old₀) (a'₂ % (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀))) (CollectionsRingBufferRingBuffer.tl old₀) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀)))
                     )
                    )
           ) ∧
      (∀ (result₀ : Prop),
       ∀ (a'₅ : (CollectionsRingBufferRingBuffer Int)),
        ((k0 result₀ (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.hd a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀)) ->
         ((collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring a'₅)) > 1) ->
          ((CollectionsRingBufferRingBuffer.hd a'₅) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring a'₅))) ->
           ((CollectionsRingBufferRingBuffer.hd a'₅) ≥ 0) ->
            ((CollectionsRingBufferRingBuffer.hd a'₅) ≤ 18446744073709551615) ->
             ((CollectionsRingBufferRingBuffer.tl a'₅) < (collections_sslice_len (t0 := Int) (CollectionsRingBufferRingBuffer.ring a'₅))) ->
              ((CollectionsRingBufferRingBuffer.tl a'₅) ≥ 0) ->
               ((CollectionsRingBufferRingBuffer.tl a'₅) ≤ 18446744073709551615) ->
                ∀ (a'₆ : Int),
                 (a'₆ ≥ 0) ->
                  (a'₆ ≤ 18446744073709551615) ->
                   (((((CollectionsRingBufferRingBuffer.tl a'₅) + 1) ≥ 0) ∧ (((CollectionsRingBufferRingBuffer.tl a'₅) + 1) ≤ 18446744073709551615)) -> (a'₆ = ((CollectionsRingBufferRingBuffer.tl a'₅) + 1))) ->
                    ((collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀)) ≥ 0) ->
                     ((collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀)) ≤ 18446744073709551615) ->
                      (((collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀)) ≠ 0)) ∧
                      (((collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀)) ≠ 0) ->
                       (((collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀)) > 1)) ∧
                       (((CollectionsRingBufferRingBuffer.hd a'₅) < (collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀)))) ∧
                       (((a'₆ % (collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀))) < (collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀)))) ∧
                       (((0 ≤ (a'₆ % (collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀))))) ∧
                       (((a'₆ % (collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀))) < (collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀))))
                       ) ∧
                       (((0 ≤ (CollectionsRingBufferRingBuffer.hd a'₅))) ∧
                       (((CollectionsRingBufferRingBuffer.hd a'₅) < (collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀))))
                       ) ∧
                       (((collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀)) > 1)) ∧
                       (∀ (a'₇ : Int),
                        ((k3 a'₇ result₀ (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.hd a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀)) ->
                         (a'₇ = (collections_sslice_get (t0 := Int) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.hd old₀)))) ∧
                       ((result₀ = ((CollectionsRingBufferRingBuffer.hd old₀) = (((CollectionsRingBufferRingBuffer.tl old₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀)))))) ∧
                       (((CollectionsRingBufferRingBuffer.mkCollectionsRingBufferRingBuffer₀ (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀) (CollectionsRingBufferRingBuffer.hd a'₅) (a'₆ % (collections_sslice_len (t0 := Int) (collections_sslice_set (t0 := Int) (CollectionsRingBufferRingBuffer.ring a'₅) (CollectionsRingBufferRingBuffer.tl a'₅) val₀)))) = (CollectionsRingBufferRingBuffer.mkCollectionsRingBufferRingBuffer₀ (collections_sslice_set (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀) (CollectionsRingBufferRingBuffer.tl old₀) val₀) (if ((CollectionsRingBufferRingBuffer.hd old₀) = (((CollectionsRingBufferRingBuffer.tl old₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀)))) then (((CollectionsRingBufferRingBuffer.hd old₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀))) else (CollectionsRingBufferRingBuffer.hd old₀)) (((CollectionsRingBufferRingBuffer.tl old₀) + 1) % (collections_sslice_len (t0 := _) (CollectionsRingBufferRingBuffer.ring old₀))))))
                       )
                      )
      
end F
