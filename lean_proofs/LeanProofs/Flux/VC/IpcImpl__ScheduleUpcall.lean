import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.ProcessbufferReadWriteProcessBuffer
import LeanProofs.Flux.Fun.NumImplMAX
open Classical

namespace F



def IpcImpl__ScheduleUpcall := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Prop) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Prop) -> (a3 : Prop) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Int) -> (a5 : Prop) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Int) -> (a5 : Prop) -> (a6 : Prop) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Int) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Int) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Int) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k6 : (a0 : Int) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Int) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Prop) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> Prop, 
 ∀ (constgen_NUM_PROCS_0 : Int),
  ∀ (a'₀ : Prop),
   (∀ (a'₁ : Int),
    ((k0 a'₁ constgen_NUM_PROCS_0 a'₀))) ∧
   (∀ (a'₂ : Prop),
    (∀ (a'₃ : Int),
     ((k0 a'₃ constgen_NUM_PROCS_0 a'₀)) ->
      ((k1 a'₃ constgen_NUM_PROCS_0 a'₀ a'₂))) ∧
    (∀ (a'₄ : Int),
     ((k1 a'₄ constgen_NUM_PROCS_0 a'₀ a'₂)) ->
      (a'₄ ≥ 0) ->
       (a'₄ ≤ 18446744073709551615) ->
        ∀ (a'₅ : Prop),
         (∀ (a'₆ : Int),
          ((k2 a'₆ constgen_NUM_PROCS_0 a'₀ a'₂ a'₄ a'₅))) ∧
         (∀ (a'₇ : Prop),
          (∀ (a'₈ : Int),
           ((k2 a'₈ constgen_NUM_PROCS_0 a'₀ a'₂ a'₄ a'₅)) ->
            ((k3 a'₈ constgen_NUM_PROCS_0 a'₀ a'₂ a'₄ a'₅ a'₇))) ∧
          (∀ (a'₉ : Int),
           ((k3 a'₉ constgen_NUM_PROCS_0 a'₀ a'₂ a'₄ a'₅ a'₇)) ->
            (a'₉ ≥ 0) ->
             (a'₉ ≤ 18446744073709551615) ->
              (a'₄ ≠ a'₉) ->
               (((k4 constgen_NUM_PROCS_0 a'₀ a'₂ a'₄ a'₅ a'₇ a'₉)) ->
                ∀ (a'₁₀ : Int),
                 (a'₁₀ ≥ 0) ->
                  (a'₁₀ ≤ 18446744073709551615) ->
                   ∀ (a'₁₁ : Int),
                    (a'₁₁ ≥ 0) ->
                     (a'₁₁ ≤ 18446744073709551615) ->
                      (((k5 constgen_NUM_PROCS_0 a'₀ a'₂ a'₄ a'₅ a'₇ a'₉ a'₁₀ a'₁₁)) ->
                       ∀ (a'₁₂ : Prop),
                        (a'₁₂ = True) ->
                         ∀ (a'₁₃ : ProcessbufferReadWriteProcessBuffer),
                          ((0 ≤ (ProcessbufferReadWriteProcessBuffer.len a'₁₃)) ∧ ((ProcessbufferReadWriteProcessBuffer.len a'₁₃) ≤ num_impl__MAX) ∧ (0 ≤ (ProcessbufferReadWriteProcessBuffer.ptr a'₁₃)) ∧ ((ProcessbufferReadWriteProcessBuffer.ptr a'₁₃) ≤ num_impl__MAX) ∧ (0 ≤ ((ProcessbufferReadWriteProcessBuffer.ptr a'₁₃) + (ProcessbufferReadWriteProcessBuffer.len a'₁₃))) ∧ (((ProcessbufferReadWriteProcessBuffer.ptr a'₁₃) + (ProcessbufferReadWriteProcessBuffer.len a'₁₃)) ≤ num_impl__MAX)) ->
                           ∀ (start₀ : Int),
                            ((start₀ = 0) ∨ (start₀ = (ProcessbufferReadWriteProcessBuffer.ptr a'₁₃))) ->
                             ((0 ≤ start₀) ∧ (start₀ ≤ num_impl__MAX)) ->
                              ∀ (size₀ : Int),
                               ((0 ≤ ((ProcessbufferReadWriteProcessBuffer.ptr a'₁₃) + size₀)) ∧ (((ProcessbufferReadWriteProcessBuffer.ptr a'₁₃) + size₀) ≤ num_impl__MAX)) ->
                                (size₀ ≥ 0) ->
                                 (size₀ ≤ 18446744073709551615) ->
                                  (((k6 constgen_NUM_PROCS_0 a'₀ a'₂ a'₄ a'₅ a'₇ a'₉ a'₁₀ a'₁₁ a'₁₂ (ProcessbufferReadWriteProcessBuffer.ptr a'₁₃) (ProcessbufferReadWriteProcessBuffer.len a'₁₃) start₀ size₀)) ->
                                   ((0 ≤ (start₀ + size₀))) ∧
                                   (((start₀ + size₀) ≤ num_impl__MAX))
                                   ) ∧
                                  (((k6 constgen_NUM_PROCS_0 a'₀ a'₂ a'₄ a'₅ a'₇ a'₉ a'₁₀ a'₁₁ a'₁₂ (ProcessbufferReadWriteProcessBuffer.ptr a'₁₃) (ProcessbufferReadWriteProcessBuffer.len a'₁₃) start₀ size₀)))
                                  ) ∧
                      (((k5 constgen_NUM_PROCS_0 a'₀ a'₂ a'₄ a'₅ a'₇ a'₉ a'₁₀ a'₁₁)))
                      ) ∧
               (((k4 constgen_NUM_PROCS_0 a'₀ a'₂ a'₄ a'₅ a'₇ a'₉)))
               )
          )
         )
    )
   
end F
