import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Slc
import LeanProofs.User.Struct.Slc
open Classical
set_option linter.unusedVariables false


namespace F

@[grind]
noncomputable def collections_sslice_pop_front : {t0 : Type} -> [Inhabited t0] -> (Slc t0) -> (Slc t0) :=
  fun l => l.drop 1

end F
