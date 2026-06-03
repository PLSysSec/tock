import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Slc
import LeanProofs.User.Struct.Slc
import LeanProofs.User.Struct.Slc
open Classical

namespace F

@[grind]
noncomputable def collections_sslice_append : {t0 : Type} -> [Inhabited t0] -> (Slc t0) -> (Slc t0) -> (Slc t0) :=
  fun l1 l2 => l1 ++ l2


end F
