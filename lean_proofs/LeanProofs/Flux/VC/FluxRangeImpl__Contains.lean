import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.FluxRangeFluxRange
open Classical

namespace F



def FluxRangeImpl__Contains := 
 ∀ (r₀ : FluxRangeFluxRange),
  ∀ (item₀ : Int),
   (item₀ ≥ 0) ->
    (item₀ ≤ 18446744073709551615) ->
     ((FluxRangeFluxRange.start r₀) ≥ 0) ->
      ((FluxRangeFluxRange.start r₀) ≤ 18446744073709551615) ->
       ((FluxRangeFluxRange.end r₀) ≥ 0) ->
        ((FluxRangeFluxRange.end r₀) ≤ 18446744073709551615) ->
         (¬((FluxRangeFluxRange.start r₀) ≤ item₀)) ->
          (False = (((FluxRangeFluxRange.start r₀) ≤ item₀) ∧ (item₀ < (FluxRangeFluxRange.end r₀))))
end F
