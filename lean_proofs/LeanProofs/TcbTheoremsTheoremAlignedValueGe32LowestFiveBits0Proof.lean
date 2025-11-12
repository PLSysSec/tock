import LeanProofs.TcbTheoremsTheoremAlignedValueGe32LowestFiveBits0
import LeanProofs.SharedLemmas
import Init.Data.BitVec.Lemmas


theorem f_pow2_0_eq_i_pow2 : f_pow2_0 = i_pow2 := by
  funext x ; unfold f_pow2_0 i_pow2 ; simp

def tcb_theorems_theorem_aligned_value_ge32_lowest_five_bits0_proof : tcb_theorems_theorem_aligned_value_ge32_lowest_five_bits0 := by
  unfold tcb_theorems_theorem_aligned_value_ge32_lowest_five_bits0
  intro x y _ h _ x_ge0 _ x_in_bounds _ y_ge0 _ y_in_bounds
  obtain ⟨y_ge32, y_pow2, x_aligned_y⟩ := h
  rw [f_pow2_0_eq_i_pow2] at *
  unfold f_aligned_1 at x_aligned_y; simp at x_aligned_y
  rw [
    ← Int.toNat_of_nonneg x_ge0,
    BitVec.ofInt_natCast,
    BitVec.and_eq,
    ←BitVec.ofNat_and
  ]
  simp [Nat.and_two_pow_sub_one_eq_mod _ 5]
  have xnat_aligned_ynat : x.toNat % y.toNat = 0 := by
    rw [← Int.toNat_emod x_ge0 y_ge0, x_aligned_y]
    simp
  rw [← Int.toNat_of_nonneg y_ge0] at y_pow2
  have ynat_pow2 := (i_pow2_0_is_power_of_2 y.toNat (by omega)).mp y_pow2
  rcases ynat_pow2 with ⟨k, hk⟩
  rw [hk] at xnat_aligned_ynat
  have ynat_dvd_xnat := Nat.dvd_of_mod_eq_zero xnat_aligned_ynat
  have thirty_two_dvd_x : 32 ∣ x.toNat := by
    apply @Nat.pow_dvd_of_le_of_pow_dvd 2 5 k
    · apply (@Nat.pow_le_pow_iff_right 2 5 k (by omega)).mp
      rw [← hk]
      omega
    · assumption
  have x_mod_32_eq_0 := Nat.mod_eq_zero_of_dvd thirty_two_dvd_x
  rw [x_mod_32_eq_0]
