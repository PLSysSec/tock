import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.CollectionsRingBufferRingBuffer
import LeanProofs.Flux.VC.CollectionsRingBufferImpl__New
open Classical

namespace F

def CollectionsRingBufferImpl__New_proof : CollectionsRingBufferImpl__New := by
  unfold CollectionsRingBufferImpl__New
  grind

end F
