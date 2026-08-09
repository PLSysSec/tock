import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.TcbDefsPow2
open Classical
set_option linter.unusedVariables false


namespace F



def TcbTheoremsTheoremPow2Div2Pow2 := 
 ∀ (n₀ : Int),
  ((tcb_defs_pow2 n₀) ∧ (n₀ ≥ 4)) ->
   (n₀ ≥ 0) ->
    (n₀ ≤ 4294967295) ->
     (tcb_defs_pow2 (n₀ / 2))
end F
