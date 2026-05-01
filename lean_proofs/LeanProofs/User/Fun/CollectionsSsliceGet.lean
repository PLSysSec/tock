import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Slc
open Classical

namespace F

@[grind]
noncomputable def collections_sslice_get : {t0 : Type} -> [Inhabited t0] -> (Slc t0) -> Int -> t0 :=
  fun slc pos => slc[pos.toNat]!


end F
