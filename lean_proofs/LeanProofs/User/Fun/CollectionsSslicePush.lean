import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Slc
import LeanProofs.User.Struct.Slc
open Classical

namespace F

@[grind]
noncomputable def collections_sslice_push : {t0 : Type} -> [Inhabited t0] -> (Slc t0) -> t0 -> (Slc t0) :=
  fun l e => l ++ [e]


end F
