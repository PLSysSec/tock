import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Slc
import LeanProofs.User.Struct.Slc
open Classical

namespace F

@[grind]
noncomputable def collections_sslice_set : {t0 : Type} -> [Inhabited t0] -> (Slc t0) -> Int -> t0 -> (Slc t0) :=
  fun slc pos val => slc.set pos.toNat val


end F
