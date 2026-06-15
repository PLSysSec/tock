import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TcbTheoremsTheoremAlignedValueGe32LowestFiveBits0
import LeanProofs.SharedLemmas
import Init.Data.BitVec.Lemmas
open Classical
set_option linter.unusedVariables false

namespace F

def TcbTheoremsTheoremAlignedValueGe32LowestFiveBits0_proof : TcbTheoremsTheoremAlignedValueGe32LowestFiveBits0 := by
  unfold TcbTheoremsTheoremAlignedValueGe32LowestFiveBits0
  intro x₀ y₀ ⟨y_ge32, y_pow2, x_aligned_y⟩ x_ge0 x_in_bounds y_ge0 y_in_bounds
  unfold tcb_defs_aligned at x_aligned_y
  rw [
    ← Int.toNat_of_nonneg x_ge0,
    BitVec.ofInt_natCast,
    BitVec.and_eq,
    ← BitVec.ofNat_and
  ]
  simp [Nat.and_two_pow_sub_one_eq_mod _ 5]
  have xnat_aligned_ynat : x₀.toNat % y₀.toNat = 0 := by
    rw [← Int.toNat_emod x_ge0 y_ge0, x_aligned_y]
    simp
  rw [← Int.toNat_of_nonneg y_ge0] at y_pow2
  have ynat_pow2 := (tcb_defs_pow2_0_is_power_of_2 y₀.toNat (by omega)).mp y_pow2
  rcases ynat_pow2 with ⟨k, hk⟩
  rw [hk] at xnat_aligned_ynat
  have ynat_dvd_xnat := Nat.dvd_of_mod_eq_zero xnat_aligned_ynat
  have thirty_two_dvd_x : 32 ∣ x₀.toNat := by
    apply @Nat.pow_dvd_of_le_of_pow_dvd 2 5 k
    · apply (@Nat.pow_le_pow_iff_right 2 5 k (by omega)).mp
      rw [← hk]
      omega
    · assumption
  have x_mod_32_eq_0 := Nat.mod_eq_zero_of_dvd thirty_two_dvd_x
  rw [x_mod_32_eq_0]

end F
