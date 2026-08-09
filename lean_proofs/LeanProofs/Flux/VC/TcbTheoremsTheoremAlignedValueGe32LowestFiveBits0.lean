import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.TcbDefsAligned
import LeanProofs.Flux.Fun.TcbDefsPow2
open Classical
set_option linter.unusedVariables false


namespace F



def TcbTheoremsTheoremAlignedValueGe32LowestFiveBits0 := 
 ∀ (x₀ : Int),
  ∀ (y₀ : Int),
   ((y₀ ≥ 32) ∧ (tcb_defs_pow2 y₀) ∧ (tcb_defs_aligned x₀ y₀)) ->
    (x₀ ≥ 0) ->
     (x₀ ≤ 4294967295) ->
      (y₀ ≥ 0) ->
       (y₀ ≤ 4294967295) ->
        ((BitVec.and (BitVec.ofInt 32 x₀) 31#32) = 0#32)
end F
