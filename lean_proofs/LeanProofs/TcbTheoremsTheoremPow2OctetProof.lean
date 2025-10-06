import LeanProofs.TcbTheoremsTheoremPow2Octet
import LeanProofs.SharedLemmas

theorem f_pow2_1_eq_i_pow2 : f_pow2_0 = i_pow2 := by
  funext x; unfold f_pow2_0 i_pow2; simp

theorem power_of_2_ge_8_octet (x: Nat) : x.isPowerOfTwo -> x ≥ 8 -> x % 8 = 0 := by
  intro x_pow2 x_ge8
  apply Nat.mod_eq_zero_of_dvd
  unfold Nat.isPowerOfTwo at x_pow2
  cases x_pow2 with
  | intro k hk =>
    have h : (8 = 2 ^ 3) := by simp
    rw [hk, h,  Nat.pow_dvd_pow_iff_le_right]
    case _ =>
      rw [hk, h] at x_ge8
      rw [←(@Nat.pow_le_pow_iff_right 2 3 k)]
      exact x_ge8
      simp
    case _ => simp

def tcb_theorems_theorem_pow2_octet_proof : tcb_theorems_theorem_pow2_octet := by
  unfold tcb_theorems_theorem_pow2_octet
  intro r0 _ h1 _ r0_ge0 _ r0_in_bounds
  obtain ⟨r0_pow2, r0_ge8⟩ := h1
  rw [f_pow2_1_eq_i_pow2] at *
  unfold f_octet_1
  simp
  have nat_res : r0.toNat % 8 = 0 := by
    apply power_of_2_ge_8_octet
    case _ =>
      apply (i_pow2_0_is_power_of_2 r0.toNat _).mp
      case _ =>
        rw [Int.toNat_of_nonneg]
        assumption
        assumption
      case _ =>
        omega
    case _ =>
      omega
  omega
