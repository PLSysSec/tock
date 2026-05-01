import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImplMAX
open Classical

namespace F



def FluxRegisterInterfaceImpl__IsSet := 
 ∀ (value₀ : BitVec 32),
  ∀ (mask₀ : BitVec 32),
   ∀ (shift₀ : BitVec 32),
    (BitVec.ule value₀ (BitVec.ofInt 32 num_impl__MAX)) ->
     (BitVec.ule mask₀ (BitVec.ofInt 32 num_impl__MAX)) ->
      ((BitVec.toNat value₀) ≥ 0) ->
       ((BitVec.toNat value₀) ≤ 255) ->
        (((BitVec.and (BitVec.ofInt 32 (BitVec.toNat value₀)) (BitVec_shiftLeft mask₀ shift₀)) ≠ 0#32) = ((BitVec.and value₀ (BitVec_shiftLeft mask₀ shift₀)) ≠ 0#32))
end F
