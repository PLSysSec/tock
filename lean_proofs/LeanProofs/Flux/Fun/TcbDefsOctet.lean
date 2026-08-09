import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

noncomputable def tcb_defs_octet (a'₂ : Int) : Prop :=
  ((a'₂ % 8) = 0)


end F
