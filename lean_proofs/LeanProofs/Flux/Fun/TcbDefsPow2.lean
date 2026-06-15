import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

noncomputable def tcb_defs_pow2 (a'₂ : Int) : Prop :=
  (let a'₃ := (BitVec.ofInt 32 a'₂); ((a'₂ > 0) ∧ ((BitVec.and a'₃ (BitVec.sub a'₃ 1#32)) = 0#32)))


end F
