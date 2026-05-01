import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.ProcessbufferReadWriteProcessBuffer
import LeanProofs.Flux.Fun.NumImplMAX
open Classical

namespace F



def ProcessbufferImpl__MutEnter := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Prop) -> (a4 : Int) -> (a5 : Int) -> Prop, 
 ∀ (c1 : Prop),
  ∀ (a'₀ : ProcessbufferReadWriteProcessBuffer),
   ∀ (fun₀ : Int),
    ((0 ≤ (ProcessbufferReadWriteProcessBuffer.len a'₀)) ∧ ((ProcessbufferReadWriteProcessBuffer.len a'₀) ≤ num_impl__MAX) ∧ (0 ≤ (ProcessbufferReadWriteProcessBuffer.ptr a'₀)) ∧ ((ProcessbufferReadWriteProcessBuffer.ptr a'₀) ≤ num_impl__MAX) ∧ (0 ≤ ((ProcessbufferReadWriteProcessBuffer.ptr a'₀) + (ProcessbufferReadWriteProcessBuffer.len a'₀))) ∧ (((ProcessbufferReadWriteProcessBuffer.ptr a'₀) + (ProcessbufferReadWriteProcessBuffer.len a'₀)) ≤ num_impl__MAX)) ->
     ((ProcessbufferReadWriteProcessBuffer.len a'₀) ≥ 0) ->
      ((ProcessbufferReadWriteProcessBuffer.len a'₀) ≤ 18446744073709551615) ->
       ∀ (a'₂ : Prop),
        (a'₂ = True) ->
         ∀ (a'₃ : Int),
          (a'₃ ≥ 0) ->
           (a'₃ ≤ 18446744073709551615) ->
            ∀ (a'₄ : Int),
             (a'₄ ≥ 0) ->
              (a'₄ ≤ 18446744073709551615) ->
               (((k0 (ProcessbufferReadWriteProcessBuffer.ptr a'₀) (ProcessbufferReadWriteProcessBuffer.len a'₀) fun₀ a'₂ a'₃ a'₄)) ->
                ∀ (a'₅ : Prop),
                 ∀ (a'₆ : Int),
                  False ->
                   (c1)) ∧
               (((k0 (ProcessbufferReadWriteProcessBuffer.ptr a'₀) (ProcessbufferReadWriteProcessBuffer.len a'₀) fun₀ a'₂ a'₃ a'₄)))
               
end F
