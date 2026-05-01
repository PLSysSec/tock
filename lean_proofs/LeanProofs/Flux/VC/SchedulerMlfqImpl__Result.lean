import LeanProofs.Flux.Prelude
open Classical

namespace F



def SchedulerMlfqImpl__Result := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Prop) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Prop) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k4 : (a0 : Prop) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Prop) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Prop) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Prop) -> Prop, ∃ k6 : (a0 : Int) -> (a1 : Prop) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Prop) -> (a6 : Int) -> (a7 : Prop) -> (a8 : Int) -> (a9 : Prop) -> (a10 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = 0) ->
   (k0 a'₀)) ∧
 (∀ (a'₁ : Int),
  (a'₁ = 0) ->
   (k1 a'₁)) ∧
 (∀ (execution_time_us₀ : Prop),
  (∀ (a'₃ : Int),
   ((k2 a'₃ execution_time_us₀))) ∧
  (∀ (execution_time_us₁ : Int),
   ((k2 execution_time_us₁ execution_time_us₀)) ->
    (execution_time_us₁ ≥ 0) ->
     (execution_time_us₁ ≤ 4294967295) ->
      ∀ (a'₅ : Int),
       (∀ (v₀ : Int),
        (v₀ < 3) ->
         ((k3 v₀ execution_time_us₀ execution_time_us₁ a'₅))) ∧
       (∀ (a'₇ : Int),
        ((k3 a'₇ execution_time_us₀ execution_time_us₁ a'₅)) ->
         (a'₇ < 3)) ∧
       (∀ (queue_idx₀ : Int),
        ((k3 queue_idx₀ execution_time_us₀ execution_time_us₁ a'₅)) ->
         (queue_idx₀ ≥ 0) ->
          (queue_idx₀ ≤ 18446744073709551615) ->
           ((queue_idx₀ < 3)) ∧
           ((queue_idx₀ < 3) ->
            ∀ (a'₉ : Prop),
             (((k4 execution_time_us₀ execution_time_us₁ a'₅ queue_idx₀ a'₉))) ∧
             (((k4 execution_time_us₀ execution_time_us₁ a'₅ queue_idx₀ a'₉)) ->
              (∀ (a'₁₀ : Int),
               ((k5 a'₁₀ execution_time_us₀ execution_time_us₁ a'₅ queue_idx₀ a'₉))) ∧
              (∀ (last_timeslice₀ : Int),
               ((k5 last_timeslice₀ execution_time_us₀ execution_time_us₁ a'₅ queue_idx₀ a'₉)) ->
                (last_timeslice₀ ≥ 0) ->
                 (last_timeslice₀ ≤ 4294967295) ->
                  ∀ (a'₁₂ : Prop),
                   ∀ (a'₁₃ : Int),
                    (a'₁₃ ≥ 0) ->
                     (a'₁₃ ≤ 4294967295) ->
                      ((((last_timeslice₀ - execution_time_us₁) ≥ 0) ∧ ((last_timeslice₀ - execution_time_us₁) ≤ 4294967295)) -> (a'₁₃ = (last_timeslice₀ - execution_time_us₁))) ->
                       ∀ (a'₁₄ : Int),
                        (a'₁₄ = 0) ->
                         (k0 a'₁₄) ->
                          ∀ (a'₁₅ : Int),
                           (a'₁₅ = 0) ->
                            (k1 a'₁₅) ->
                             ∀ (punish₀ : Prop),
                              punish₀ ->
                               ∀ (a'₁₇ : Int),
                                (a'₁₇ ≥ 0) ->
                                 (a'₁₇ ≤ 18446744073709551615) ->
                                  ((((3 - 1) ≥ 0) ∧ ((3 - 1) ≤ 18446744073709551615)) -> (a'₁₇ = (3 - 1))) ->
                                   ((queue_idx₀ ≠ a'₁₇) ->
                                    ∀ (a'₁₈ : Int),
                                     (a'₁₈ ≥ 0) ->
                                      (a'₁₈ ≤ 18446744073709551615) ->
                                       ((((queue_idx₀ + 1) ≥ 0) ∧ ((queue_idx₀ + 1) ≤ 18446744073709551615)) -> (a'₁₈ = (queue_idx₀ + 1))) ->
                                        ((k6 a'₁₈ execution_time_us₀ execution_time_us₁ a'₅ queue_idx₀ a'₉ last_timeslice₀ a'₁₂ a'₁₃ True a'₁₇))) ∧
                                   ((¬(queue_idx₀ ≠ a'₁₇)) ->
                                    ((k6 queue_idx₀ execution_time_us₀ execution_time_us₁ a'₅ queue_idx₀ a'₉ last_timeslice₀ a'₁₂ a'₁₃ True a'₁₇))) ∧
                                   (∀ (next_queue₀ : Int),
                                    ((k6 next_queue₀ execution_time_us₀ execution_time_us₁ a'₅ queue_idx₀ a'₉ last_timeslice₀ a'₁₂ a'₁₃ True a'₁₇)) ->
                                     (next_queue₀ < 3))
                                   )
              )
             )
           )
       )
  )
 
end F
