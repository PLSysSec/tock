import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Slc
import LeanProofs.User.Struct.Slc
open Classical
set_option linter.unusedVariables false


namespace F

@[grind]
def collections_sslice_subslice : {t0 : Type} -> [Inhabited t0] -> (Slc t0) -> Int -> Int -> (Slc t0) :=
  fun s l r => (s.drop l.toNat).take (r.toNat - l.toNat)

end F
