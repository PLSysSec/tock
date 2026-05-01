import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.OpsRangeRange
open Classical

namespace F



def HilCanImpl__BitTimingForBitrate := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> (a17 : Int) -> (a18 : Int) -> (a19 : Int) -> (a20 : Int) -> (a21 : Int) -> (a22 : Int) -> (a23 : Int) -> (a24 : Int) -> (a25 : Int) -> (a26 : Int) -> (a27 : Int) -> (a28 : Int) -> (a29 : Int) -> (a30 : Int) -> (a31 : Int) -> (a32 : Int) -> (a33 : Int) -> (a34 : Int) -> (a35 : Int) -> (a36 : Int) -> (a37 : Int) -> (a38 : Int) -> (a39 : Int) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> (a17 : Int) -> (a18 : Int) -> (a19 : Int) -> (a20 : Int) -> (a21 : Int) -> (a22 : Int) -> (a23 : Int) -> (a24 : Int) -> (a25 : Int) -> (a26 : Int) -> (a27 : Int) -> (a28 : Int) -> (a29 : Int) -> (a30 : Int) -> (a31 : Int) -> (a32 : Int) -> (a33 : Int) -> (a34 : Int) -> (a35 : Int) -> (a36 : Int) -> (a37 : Int) -> (a38 : Int) -> (a39 : Int) -> (a40 : Int) -> (a41 : Int) -> (a42 : Int) -> (a43 : Int) -> (a44 : Int) -> (a45 : Int) -> (a46 : Prop) -> (a47 : Int) -> (a48 : Int) -> (a49 : Int) -> (a50 : Int) -> (a51 : Int) -> (a52 : Int) -> Prop, ∃ k6 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> (a17 : Int) -> (a18 : Int) -> (a19 : Int) -> (a20 : Int) -> (a21 : Int) -> (a22 : Int) -> (a23 : Int) -> (a24 : Int) -> (a25 : Int) -> (a26 : Int) -> (a27 : Int) -> (a28 : Int) -> (a29 : Int) -> (a30 : Int) -> (a31 : Int) -> (a32 : Int) -> (a33 : Int) -> (a34 : Int) -> (a35 : Int) -> (a36 : Int) -> (a37 : Int) -> (a38 : Int) -> (a39 : Int) -> (a40 : Int) -> (a41 : Int) -> (a42 : Int) -> (a43 : Int) -> (a44 : Int) -> (a45 : Int) -> (a46 : Prop) -> (a47 : Int) -> (a48 : Int) -> (a49 : Int) -> (a50 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = 0) ->
   (k0 a'₀)) ∧
 (∀ (a'₁ : Int),
  (a'₁ = 0) ->
   (k1 a'₁)) ∧
 (∀ (clock_rate₀ : Int),
  ∀ (bitrate₀ : Int),
   (clock_rate₀ ≥ 0) ->
    (clock_rate₀ ≤ 4294967295) ->
     (bitrate₀ ≥ 0) ->
      (bitrate₀ ≤ 4294967295) ->
       (bitrate₀ > 0) ->
        (¬(bitrate₀ > 8000000)) ->
         ((¬(bitrate₀ > 800000)) ->
          ((¬(bitrate₀ > 500000)) ->
           ((k2 875 clock_rate₀ bitrate₀))) ∧
          ((bitrate₀ > 500000) ->
           ((k2 800 clock_rate₀ bitrate₀))) ∧
          (∀ (sp₀ : Int),
           ((k2 sp₀ clock_rate₀ bitrate₀)) ->
            ((k3 sp₀ clock_rate₀ bitrate₀)))
          ) ∧
         ((bitrate₀ > 800000) ->
          ((k3 750 clock_rate₀ bitrate₀))) ∧
         (∀ (sp₁ : Int),
          ((k3 sp₁ clock_rate₀ bitrate₀)) ->
           ∀ (a'₆ : Int),
            (a'₆ ≥ 0) ->
             (a'₆ ≤ 255) ->
              ∀ (a'₇ : Int),
               (a'₇ ≥ 0) ->
                (a'₇ ≤ 255) ->
                 ∀ (a'₈ : Int),
                  (a'₈ ≥ 0) ->
                   (a'₈ ≤ 255) ->
                    ∀ (a'₉ : Int),
                     (a'₉ ≥ 0) ->
                      (a'₉ ≤ 4294967295) ->
                       ∀ (a'₁₀ : Int),
                        (a'₁₀ ≥ 0) ->
                         (a'₁₀ ≤ 4294967295) ->
                          ∀ (a'₁₁ : Int),
                           (a'₁₁ ≥ 0) ->
                            (a'₁₁ ≤ 255) ->
                             ∀ (a'₁₂ : Int),
                              (a'₁₂ ≥ 0) ->
                               (a'₁₂ ≤ 255) ->
                                ∀ (a'₁₃ : Int),
                                 (a'₁₃ ≥ 0) ->
                                  (a'₁₃ ≤ 255) ->
                                   ∀ (a'₁₄ : Int),
                                    (a'₁₄ ≥ 0) ->
                                     (a'₁₄ ≤ 4294967295) ->
                                      ∀ (a'₁₅ : Int),
                                       (a'₁₅ ≥ 0) ->
                                        (a'₁₅ ≤ 4294967295) ->
                                         ∀ (a'₁₆ : Int),
                                          (a'₁₆ ≥ 0) ->
                                           (a'₁₆ ≤ 255) ->
                                            ((((a'₈ + a'₁₁) ≥ 0) ∧ ((a'₈ + a'₁₁) ≤ 255)) -> (a'₁₆ = (a'₈ + a'₁₁))) ->
                                             ∀ (a'₁₇ : Int),
                                              (a'₁₇ ≥ 0) ->
                                               (a'₁₇ ≤ 255) ->
                                                ∀ (a'₁₈ : Int),
                                                 (a'₁₈ ≥ 0) ->
                                                  (a'₁₈ ≤ 255) ->
                                                   ∀ (a'₁₉ : Int),
                                                    (a'₁₉ ≥ 0) ->
                                                     (a'₁₉ ≤ 255) ->
                                                      ∀ (a'₂₀ : Int),
                                                       (a'₂₀ ≥ 0) ->
                                                        (a'₂₀ ≤ 4294967295) ->
                                                         ∀ (a'₂₁ : Int),
                                                          (a'₂₁ ≥ 0) ->
                                                           (a'₂₁ ≤ 4294967295) ->
                                                            ∀ (a'₂₂ : Int),
                                                             (a'₂₂ ≥ 0) ->
                                                              (a'₂₂ ≤ 255) ->
                                                               ((((a'₁₆ + a'₁₈) ≥ 0) ∧ ((a'₁₆ + a'₁₈) ≤ 255)) -> (a'₂₂ = (a'₁₆ + a'₁₈))) ->
                                                                ∀ (a'₂₃ : Int),
                                                                 (a'₂₃ ≥ 0) ->
                                                                  (a'₂₃ ≤ 255) ->
                                                                   ∀ (a'₂₄ : Int),
                                                                    (a'₂₄ ≥ 0) ->
                                                                     (a'₂₄ ≤ 255) ->
                                                                      ((((a'₂₂ + a'₂₃) ≥ 0) ∧ ((a'₂₂ + a'₂₃) ≤ 255)) -> (a'₂₄ = (a'₂₂ + a'₂₃))) ->
                                                                       (a'₂₄ > 0) ->
                                                                        ∀ (a'₂₅ : Int),
                                                                         (a'₂₅ ≥ 0) ->
                                                                          (a'₂₅ ≤ 4294967295) ->
                                                                           ((((a'₂₄ * bitrate₀) ≥ 0) ∧ ((a'₂₄ * bitrate₀) ≤ 4294967295)) -> (a'₂₅ = (a'₂₄ * bitrate₀))) ->
                                                                            ((a'₂₅ ≠ 0)) ∧
                                                                            ((a'₂₅ ≠ 0) ->
                                                                             ∀ (r₀ : Int),
                                                                              ((((clock_rate₀ / a'₂₅) ≥ 1) -> (r₀ = (clock_rate₀ / a'₂₅))) ∧ ((1 > (clock_rate₀ / a'₂₅)) -> (r₀ = 1))) ->
                                                                               (r₀ ≥ 0) ->
                                                                                (r₀ ≤ 4294967295) ->
                                                                                 ∀ (a'₂₇ : Int),
                                                                                  (a'₂₇ ≥ 0) ->
                                                                                   (a'₂₇ ≤ 255) ->
                                                                                    ∀ (a'₂₈ : Int),
                                                                                     (a'₂₈ ≥ 0) ->
                                                                                      (a'₂₈ ≤ 255) ->
                                                                                       ∀ (a'₂₉ : Int),
                                                                                        (a'₂₉ ≥ 0) ->
                                                                                         (a'₂₉ ≤ 255) ->
                                                                                          ∀ (a'₃₀ : Int),
                                                                                           (a'₃₀ ≥ 0) ->
                                                                                            (a'₃₀ ≤ 4294967295) ->
                                                                                             ∀ (a'₃₁ : Int),
                                                                                              (a'₃₁ ≥ 0) ->
                                                                                               (a'₃₁ ≤ 4294967295) ->
                                                                                                ∀ (a'₃₂ : (OpsRangeRange Int)),
                                                                                                 (∀ (a'₃₃ : Int),
                                                                                                  (a'₃₃ ≥ 0) ->
                                                                                                   (a'₃₃ ≤ 255) ->
                                                                                                    ∀ (a'₃₄ : Int),
                                                                                                     (a'₃₄ ≥ 0) ->
                                                                                                      (a'₃₄ ≤ 255) ->
                                                                                                       ∀ (a'₃₅ : Int),
                                                                                                        (a'₃₅ ≥ 0) ->
                                                                                                         (a'₃₅ ≤ 255) ->
                                                                                                          ∀ (a'₃₆ : Int),
                                                                                                           (a'₃₆ ≥ 0) ->
                                                                                                            (a'₃₆ ≤ 4294967295) ->
                                                                                                             ∀ (a'₃₇ : Int),
                                                                                                              (a'₃₇ ≥ 0) ->
                                                                                                               (a'₃₇ ≤ 4294967295) ->
                                                                                                                ((k4 (OpsRangeRange.start a'₃₂) (OpsRangeRange.end a'₃₂) a'₂₄ 65535 a'₃₃ a'₃₄ a'₃₅ a'₃₆ a'₃₇ clock_rate₀ bitrate₀ sp₁ a'₆ a'₇ a'₈ a'₉ a'₁₀ a'₁₁ a'₁₂ a'₁₃ a'₁₄ a'₁₅ a'₁₆ a'₁₇ a'₁₈ a'₁₉ a'₂₀ a'₂₁ a'₂₂ a'₂₃ a'₂₄ a'₂₅ r₀ a'₂₇ a'₂₈ a'₂₉ a'₃₀ a'₃₁ (OpsRangeRange.start a'₃₂) (OpsRangeRange.end a'₃₂)))) ∧
                                                                                                 (∀ (iter₀ : (OpsRangeRange Int)),
                                                                                                  ∀ (ts₀ : Int),
                                                                                                   ∀ (sample_point_err_min₀ : Int),
                                                                                                    ∀ (res_timing₀ : Int),
                                                                                                     ∀ (res_timing₁ : Int),
                                                                                                      ∀ (res_timing₂ : Int),
                                                                                                       ∀ (res_timing₃ : Int),
                                                                                                        ∀ (res_timing₄ : Int),
                                                                                                         ((k4 (OpsRangeRange.start iter₀) (OpsRangeRange.end iter₀) ts₀ sample_point_err_min₀ res_timing₀ res_timing₁ res_timing₂ res_timing₃ res_timing₄ clock_rate₀ bitrate₀ sp₁ a'₆ a'₇ a'₈ a'₉ a'₁₀ a'₁₁ a'₁₂ a'₁₃ a'₁₄ a'₁₅ a'₁₆ a'₁₇ a'₁₈ a'₁₉ a'₂₀ a'₂₁ a'₂₂ a'₂₃ a'₂₄ a'₂₅ r₀ a'₂₇ a'₂₈ a'₂₉ a'₃₀ a'₃₁ (OpsRangeRange.start a'₃₂) (OpsRangeRange.end a'₃₂))) ->
                                                                                                          ∀ (a'₄₆ : Prop),
                                                                                                           ∀ (a'₄₇ : (OpsRangeRange Int)),
                                                                                                            (a'₄₆ = True) ->
                                                                                                             ∀ (a'₄₈ : Int),
                                                                                                              (a'₄₈ ≥ 0) ->
                                                                                                               (a'₄₈ ≤ 4294967295) ->
                                                                                                                ∀ (a'₄₉ : Int),
                                                                                                                 (a'₄₉ ≥ 0) ->
                                                                                                                  (a'₄₉ ≤ 4294967295) ->
                                                                                                                   ((((a'₄₈ * bitrate₀) ≥ 0) ∧ ((a'₄₈ * bitrate₀) ≤ 4294967295)) -> (a'₄₉ = (a'₄₈ * bitrate₀))) ->
                                                                                                                    (a'₄₉ > 0) ->
                                                                                                                     ((a'₄₉ ≠ 0)) ∧
                                                                                                                     ((a'₄₉ ≠ 0) ->
                                                                                                                      ((¬((clock_rate₀ % a'₄₉) ≠ 0)) ->
                                                                                                                       ((a'₄₉ ≠ 0)) ∧
                                                                                                                       ((a'₄₉ ≠ 0) ->
                                                                                                                        ((clock_rate₀ / a'₄₉) > 0) ->
                                                                                                                         ∀ (a'₅₀ : Int),
                                                                                                                          (a'₅₀ = 0) ->
                                                                                                                           (k0 a'₅₀) ->
                                                                                                                            ∀ (a'₅₁ : Int),
                                                                                                                             (a'₅₁ = 0) ->
                                                                                                                              (k1 a'₅₁) ->
                                                                                                                               ∀ (a'₅₂ : Int),
                                                                                                                                (a'₅₂ ≥ 0) ->
                                                                                                                                 (a'₅₂ ≤ 255) ->
                                                                                                                                  ∀ (a'₅₃ : Int),
                                                                                                                                   (a'₅₃ ≥ (-2147483648)) ->
                                                                                                                                    (a'₅₃ ≤ 2147483647) ->
                                                                                                                                     ((¬(a'₅₃ < 0)) ->
                                                                                                                                      ((¬(a'₅₃ < sample_point_err_min₀)) ->
                                                                                                                                       ∀ (a'₅₄ : Int),
                                                                                                                                        (a'₅₄ ≥ 0) ->
                                                                                                                                         (a'₅₄ ≤ 255) ->
                                                                                                                                          ∀ (a'₅₅ : Int),
                                                                                                                                           (a'₅₅ ≥ 0) ->
                                                                                                                                            (a'₅₅ ≤ 255) ->
                                                                                                                                             ∀ (a'₅₆ : Int),
                                                                                                                                              (a'₅₆ ≥ 0) ->
                                                                                                                                               (a'₅₆ ≤ 255) ->
                                                                                                                                                ∀ (a'₅₇ : Int),
                                                                                                                                                 (a'₅₇ ≥ 0) ->
                                                                                                                                                  (a'₅₇ ≤ 4294967295) ->
                                                                                                                                                   ∀ (a'₅₈ : Int),
                                                                                                                                                    (a'₅₈ ≥ 0) ->
                                                                                                                                                     (a'₅₈ ≤ 4294967295) ->
                                                                                                                                                      ((k5 sample_point_err_min₀ a'₅₄ a'₅₅ a'₅₆ a'₅₇ a'₅₈ clock_rate₀ bitrate₀ sp₁ a'₆ a'₇ a'₈ a'₉ a'₁₀ a'₁₁ a'₁₂ a'₁₃ a'₁₄ a'₁₅ a'₁₆ a'₁₇ a'₁₈ a'₁₉ a'₂₀ a'₂₁ a'₂₂ a'₂₃ a'₂₄ a'₂₅ r₀ a'₂₇ a'₂₈ a'₂₉ a'₃₀ a'₃₁ (OpsRangeRange.start a'₃₂) (OpsRangeRange.end a'₃₂) (OpsRangeRange.start iter₀) (OpsRangeRange.end iter₀) ts₀ sample_point_err_min₀ res_timing₀ res_timing₁ res_timing₂ res_timing₃ res_timing₄ a'₄₆ (OpsRangeRange.start a'₄₇) (OpsRangeRange.end a'₄₇) a'₄₈ a'₄₉ a'₅₂ a'₅₃))) ∧
                                                                                                                                      ((a'₅₃ < sample_point_err_min₀) ->
                                                                                                                                       ∀ (a'₅₉ : Int),
                                                                                                                                        (a'₅₉ ≥ 0) ->
                                                                                                                                         (a'₅₉ ≤ 65535) ->
                                                                                                                                          ∀ (a'₆₀ : Int),
                                                                                                                                           (a'₆₀ ≥ 0) ->
                                                                                                                                            (a'₆₀ ≤ 255) ->
                                                                                                                                             ∀ (a'₆₁ : Int),
                                                                                                                                              (a'₆₁ ≥ 0) ->
                                                                                                                                               (a'₆₁ ≤ 255) ->
                                                                                                                                                ∀ (a'₆₂ : Int),
                                                                                                                                                 (a'₆₂ ≥ 0) ->
                                                                                                                                                  (a'₆₂ ≤ 255) ->
                                                                                                                                                   ∀ (a'₆₃ : Int),
                                                                                                                                                    (a'₆₃ ≥ 0) ->
                                                                                                                                                     (a'₆₃ ≤ 4294967295) ->
                                                                                                                                                      ∀ (a'₆₄ : Int),
                                                                                                                                                       (a'₆₄ ≥ 0) ->
                                                                                                                                                        (a'₆₄ ≤ 4294967295) ->
                                                                                                                                                         (a'₅₃ ≠ 0) ->
                                                                                                                                                          ((k5 a'₅₉ a'₆₀ a'₆₁ a'₆₂ a'₆₃ a'₄₈ clock_rate₀ bitrate₀ sp₁ a'₆ a'₇ a'₈ a'₉ a'₁₀ a'₁₁ a'₁₂ a'₁₃ a'₁₄ a'₁₅ a'₁₆ a'₁₇ a'₁₈ a'₁₉ a'₂₀ a'₂₁ a'₂₂ a'₂₃ a'₂₄ a'₂₅ r₀ a'₂₇ a'₂₈ a'₂₉ a'₃₀ a'₃₁ (OpsRangeRange.start a'₃₂) (OpsRangeRange.end a'₃₂) (OpsRangeRange.start iter₀) (OpsRangeRange.end iter₀) ts₀ sample_point_err_min₀ res_timing₀ res_timing₁ res_timing₂ res_timing₃ res_timing₄ a'₄₆ (OpsRangeRange.start a'₄₇) (OpsRangeRange.end a'₄₇) a'₄₈ a'₄₉ a'₅₂ a'₅₃))) ∧
                                                                                                                                      (∀ (sample_point_err_min₁ : Int),
                                                                                                                                       ∀ (res_timing₅ : Int),
                                                                                                                                        ∀ (res_timing₆ : Int),
                                                                                                                                         ∀ (res_timing₇ : Int),
                                                                                                                                          ∀ (res_timing₈ : Int),
                                                                                                                                           ∀ (res_timing₉ : Int),
                                                                                                                                            ((k5 sample_point_err_min₁ res_timing₅ res_timing₆ res_timing₇ res_timing₈ res_timing₉ clock_rate₀ bitrate₀ sp₁ a'₆ a'₇ a'₈ a'₉ a'₁₀ a'₁₁ a'₁₂ a'₁₃ a'₁₄ a'₁₅ a'₁₆ a'₁₇ a'₁₈ a'₁₉ a'₂₀ a'₂₁ a'₂₂ a'₂₃ a'₂₄ a'₂₅ r₀ a'₂₇ a'₂₈ a'₂₉ a'₃₀ a'₃₁ (OpsRangeRange.start a'₃₂) (OpsRangeRange.end a'₃₂) (OpsRangeRange.start iter₀) (OpsRangeRange.end iter₀) ts₀ sample_point_err_min₀ res_timing₀ res_timing₁ res_timing₂ res_timing₃ res_timing₄ a'₄₆ (OpsRangeRange.start a'₄₇) (OpsRangeRange.end a'₄₇) a'₄₈ a'₄₉ a'₅₂ a'₅₃)) ->
                                                                                                                                             ((k4 (OpsRangeRange.start a'₄₇) (OpsRangeRange.end a'₄₇) (clock_rate₀ / a'₄₉) sample_point_err_min₁ res_timing₅ res_timing₆ res_timing₇ res_timing₈ res_timing₉ clock_rate₀ bitrate₀ sp₁ a'₆ a'₇ a'₈ a'₉ a'₁₀ a'₁₁ a'₁₂ a'₁₃ a'₁₄ a'₁₅ a'₁₆ a'₁₇ a'₁₈ a'₁₉ a'₂₀ a'₂₁ a'₂₂ a'₂₃ a'₂₄ a'₂₅ r₀ a'₂₇ a'₂₈ a'₂₉ a'₃₀ a'₃₁ (OpsRangeRange.start a'₃₂) (OpsRangeRange.end a'₃₂))))
                                                                                                                                      ) ∧
                                                                                                                                     ((a'₅₃ < 0) ->
                                                                                                                                      ∀ (a'₇₁ : Int),
                                                                                                                                       (a'₇₁ ≥ 0) ->
                                                                                                                                        (a'₇₁ ≤ 255) ->
                                                                                                                                         ∀ (a'₇₂ : Int),
                                                                                                                                          (a'₇₂ ≥ 0) ->
                                                                                                                                           (a'₇₂ ≤ 255) ->
                                                                                                                                            ∀ (a'₇₃ : Int),
                                                                                                                                             (a'₇₃ ≥ 0) ->
                                                                                                                                              (a'₇₃ ≤ 255) ->
                                                                                                                                               ∀ (a'₇₄ : Int),
                                                                                                                                                (a'₇₄ ≥ 0) ->
                                                                                                                                                 (a'₇₄ ≤ 4294967295) ->
                                                                                                                                                  ∀ (a'₇₅ : Int),
                                                                                                                                                   (a'₇₅ ≥ 0) ->
                                                                                                                                                    (a'₇₅ ≤ 4294967295) ->
                                                                                                                                                     ((k6 (clock_rate₀ / a'₄₉) a'₇₁ a'₇₂ a'₇₃ a'₇₄ a'₇₅ clock_rate₀ bitrate₀ sp₁ a'₆ a'₇ a'₈ a'₉ a'₁₀ a'₁₁ a'₁₂ a'₁₃ a'₁₄ a'₁₅ a'₁₆ a'₁₇ a'₁₈ a'₁₉ a'₂₀ a'₂₁ a'₂₂ a'₂₃ a'₂₄ a'₂₅ r₀ a'₂₇ a'₂₈ a'₂₉ a'₃₀ a'₃₁ (OpsRangeRange.start a'₃₂) (OpsRangeRange.end a'₃₂) (OpsRangeRange.start iter₀) (OpsRangeRange.end iter₀) ts₀ sample_point_err_min₀ res_timing₀ res_timing₁ res_timing₂ res_timing₃ res_timing₄ a'₄₆ (OpsRangeRange.start a'₄₇) (OpsRangeRange.end a'₄₇) a'₄₈ a'₄₉)))
                                                                                                                                     )
                                                                                                                       ) ∧
                                                                                                                      (((clock_rate₀ % a'₄₉) ≠ 0) ->
                                                                                                                       ((k6 ts₀ res_timing₀ res_timing₁ res_timing₂ res_timing₃ res_timing₄ clock_rate₀ bitrate₀ sp₁ a'₆ a'₇ a'₈ a'₉ a'₁₀ a'₁₁ a'₁₂ a'₁₃ a'₁₄ a'₁₅ a'₁₆ a'₁₇ a'₁₈ a'₁₉ a'₂₀ a'₂₁ a'₂₂ a'₂₃ a'₂₄ a'₂₅ r₀ a'₂₇ a'₂₈ a'₂₉ a'₃₀ a'₃₁ (OpsRangeRange.start a'₃₂) (OpsRangeRange.end a'₃₂) (OpsRangeRange.start iter₀) (OpsRangeRange.end iter₀) ts₀ sample_point_err_min₀ res_timing₀ res_timing₁ res_timing₂ res_timing₃ res_timing₄ a'₄₆ (OpsRangeRange.start a'₄₇) (OpsRangeRange.end a'₄₇) a'₄₈ a'₄₉))) ∧
                                                                                                                      (∀ (ts₁ : Int),
                                                                                                                       ∀ (res_timing₁₀ : Int),
                                                                                                                        ∀ (res_timing₁₁ : Int),
                                                                                                                         ∀ (res_timing₁₂ : Int),
                                                                                                                          ∀ (res_timing₁₃ : Int),
                                                                                                                           ∀ (res_timing₁₄ : Int),
                                                                                                                            ((k6 ts₁ res_timing₁₀ res_timing₁₁ res_timing₁₂ res_timing₁₃ res_timing₁₄ clock_rate₀ bitrate₀ sp₁ a'₆ a'₇ a'₈ a'₉ a'₁₀ a'₁₁ a'₁₂ a'₁₃ a'₁₄ a'₁₅ a'₁₆ a'₁₇ a'₁₈ a'₁₉ a'₂₀ a'₂₁ a'₂₂ a'₂₃ a'₂₄ a'₂₅ r₀ a'₂₇ a'₂₈ a'₂₉ a'₃₀ a'₃₁ (OpsRangeRange.start a'₃₂) (OpsRangeRange.end a'₃₂) (OpsRangeRange.start iter₀) (OpsRangeRange.end iter₀) ts₀ sample_point_err_min₀ res_timing₀ res_timing₁ res_timing₂ res_timing₃ res_timing₄ a'₄₆ (OpsRangeRange.start a'₄₇) (OpsRangeRange.end a'₄₇) a'₄₈ a'₄₉)) ->
                                                                                                                             ((k4 (OpsRangeRange.start a'₄₇) (OpsRangeRange.end a'₄₇) ts₁ sample_point_err_min₀ res_timing₁₀ res_timing₁₁ res_timing₁₂ res_timing₁₃ res_timing₁₄ clock_rate₀ bitrate₀ sp₁ a'₆ a'₇ a'₈ a'₉ a'₁₀ a'₁₁ a'₁₂ a'₁₃ a'₁₄ a'₁₅ a'₁₆ a'₁₇ a'₁₈ a'₁₉ a'₂₀ a'₂₁ a'₂₂ a'₂₃ a'₂₄ a'₂₅ r₀ a'₂₇ a'₂₈ a'₂₉ a'₃₀ a'₃₁ (OpsRangeRange.start a'₃₂) (OpsRangeRange.end a'₃₂))))
                                                                                                                      )
                                                                                                                     )
                                                                                                 )
                                                                            )
         )
 
end F
