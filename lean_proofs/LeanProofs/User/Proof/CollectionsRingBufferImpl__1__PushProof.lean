import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.CollectionsRingBufferImpl__1__Push
open Classical

namespace F

open CollectionsRingBufferImpl1PushKVarSolutions

def CollectionsRingBufferImpl__1__Push_proof : CollectionsRingBufferImpl__1__Push := by
  unfold CollectionsRingBufferImpl__1__Push
  exists k0 ; exists k1 ; exists k2 ; exists k3
  unfold k0 k1 k2 k3
  repeat (any_goals
    first
      | (intro)
      | apply And.intro
      | apply Int.emod_lt_of_pos ; omega
      | apply Int.emod_nonneg ; omega
      | grind
  )

end F
