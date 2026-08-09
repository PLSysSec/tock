import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.TcbDefsAligned
import LeanProofs.Flux.Fun.TcbDefsPow2
open Classical
set_option linter.unusedVariables false


namespace F



def TcbTheoremsTheoremPow2LeAligned := 
 ∀ (x₀ : Int),
  ∀ (y₀ : Int),
   ∀ (z₀ : Int),
    ((tcb_defs_aligned x₀ y₀) ∧ (z₀ ≤ y₀) ∧ (tcb_defs_pow2 y₀) ∧ (tcb_defs_pow2 z₀)) ->
     (x₀ ≥ 0) ->
      (x₀ ≤ 4294967295) ->
       (y₀ ≥ 0) ->
        (y₀ ≤ 4294967295) ->
         (z₀ ≥ 0) ->
          (z₀ ≤ 4294967295) ->
           (tcb_defs_aligned x₀ z₀)
end F
