import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.TcbDefsOctet
import LeanProofs.Flux.Fun.TcbDefsPow2
open Classical
set_option linter.unusedVariables false


namespace F



def TcbTheoremsTheoremPow2Octet := 
 ∀ (r₀ : Int),
  ((tcb_defs_pow2 r₀) ∧ (r₀ ≥ 8)) ->
   (r₀ ≥ 0) ->
    (r₀ ≤ 4294967295) ->
     (tcb_defs_octet r₀)
end F
