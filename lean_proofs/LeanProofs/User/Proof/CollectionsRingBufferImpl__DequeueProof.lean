import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.CollectionsRingBufferImpl__Dequeue
open Classical

namespace F

open CollectionsRingBufferImplDequeueKVarSolutions

def CollectionsRingBufferImpl__Dequeue_proof : CollectionsRingBufferImpl__Dequeue := by
  unfold CollectionsRingBufferImpl__Dequeue
  exists k0 ; exists k1 ; unfold k0 k1
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
