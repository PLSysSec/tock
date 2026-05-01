import LeanProofs.Flux.Prelude
open Classical

namespace F

@[ext]
structure FluxPairPair (t0 : Type) [Inhabited t0] (t1 : Type) [Inhabited t1] where
  mkFluxPairPair₀ ::
    fst : t0 
    snd : t1 


end F
