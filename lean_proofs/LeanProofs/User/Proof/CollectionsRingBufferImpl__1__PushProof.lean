import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.CollectionsRingBufferImpl__1__Push
import LeanFixpoint
open Classical
set_option linter.unusedVariables false


namespace F

def CollectionsRingBufferImpl__1__Push_proof : CollectionsRingBufferImpl__1__Push := by
  unfold CollectionsRingBufferImpl__1__Push
  fusion ; zap
  repeat' (first | apply Int.emod_lt_of_pos | apply Int.emod_nonneg | omega)


end F
