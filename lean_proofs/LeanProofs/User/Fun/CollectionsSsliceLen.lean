import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Slc
open Classical
set_option linter.unusedVariables false


namespace F

@[grind]
noncomputable def collections_sslice_len : {t0 : Type} -> [Inhabited t0] -> (Slc t0) -> Int :=
  fun slc => slc.length


end F
