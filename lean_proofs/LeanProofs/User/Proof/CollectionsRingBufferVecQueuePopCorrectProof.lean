import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.CollectionsRingBufferVecQueuePopCorrect
open Classical

namespace F

def CollectionsRingBufferVecQueuePopCorrect_proof : CollectionsRingBufferVecQueuePopCorrect := by
  unfold CollectionsRingBufferVecQueuePopCorrect
  intro rb vq c1 c2 _ _ _ _ _ res
  intro nrb _ _ _ _ _ _ ifs ifns
  and_intros
  · intro hdgttl
    rcases Classical.em res with hrt | hrf
    · sorry
    · grind
  · intro hdletl
    rcases Classical.em res with hrt | hrf
    · sorry
    · grind

end F
