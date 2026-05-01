import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.CollectionsRingBufferImpl__AsSslices
open Classical

namespace F

open CollectionsRingBufferImplAsSslicesKVarSolutions

def CollectionsRingBufferImpl__AsSslices_proof : CollectionsRingBufferImpl__AsSslices := by
  unfold CollectionsRingBufferImpl__AsSslices
  exists k0 ; exists k1 ; exists k2
  exists k3 ; exists k4 ; exists k5
  unfold k0 k1 k2 k3 k4 k5
  repeat' (
    first
      | (intro)
      | apply And.intro
      | grind
  )

end F
