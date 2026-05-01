import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.CollectionsRingBufferImpl__Enqueue
open Classical

namespace F

def CollectionsRingBufferImpl__Enqueue_proof : CollectionsRingBufferImpl__Enqueue := by
  unfold CollectionsRingBufferImpl__Enqueue
  repeat (any_goals
    first
      | (intro)
      | apply And.intro
      | grind
  )
  apply Int.emod_lt_of_pos ; omega
  apply Int.emod_nonneg ; omega
  apply Int.emod_lt_of_pos ; omega

end F
