import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

noncomputable def tcb_defs_aligned (a'₀ : Int) (a'₁ : Int) : Prop :=
  ((a'₀ % a'₁) = 0)


end F
