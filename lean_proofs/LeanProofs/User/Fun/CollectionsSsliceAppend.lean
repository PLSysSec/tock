import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Slc
import LeanProofs.User.Struct.Slc
import LeanProofs.User.Struct.Slc
open Classical
set_option linter.unusedVariables false


namespace F

@[grind]
noncomputable def collections_sslice_append : {t0 : Type} -> [Inhabited t0] -> (Slc t0) -> (Slc t0) -> (Slc t0) :=
  fun x y => x ++ y


end F
