import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TcbTheoremsTheoremPow2Div2Pow2
import LeanProofs.SharedLemmas
open Classical
set_option linter.unusedVariables false

private theorem pow_right_inj (ha : 1 < a) : a ^ m = a ^ n ↔ m = n := by
  simp [Nat.le_antisymm_iff, Nat.pow_le_pow_iff_right ha]

private theorem four_is_pow2 : pow2 4 := by simp

private theorem pow2_div2_pow2 (x : Nat) : pow2 x → x ≥ 4 → pow2 (x / 2) := by
  intros h1 h2
  rcases (pow2_isPowerOfTwo x).mp h1 with ⟨n, hy⟩
  rcases (pow2_isPowerOfTwo 4).mp four_is_pow2 with ⟨m, hz⟩
  apply (pow2_isPowerOfTwo (x / 2)).mpr
  simp_all
  simp [Nat.isPowerOfTwo]
  exists (n - 1)
  have hn : n ≥ 1 := by
    simp_all [Nat.pow_le_pow_iff_right]
    have h_eq : 2 ^ 2 = 2 ^ m := by rw [← hz]
    have hm : m = 2 := by
      rw [pow_right_inj] at h_eq; simp_all; omega
    simp_all; omega
  rw [Nat.div_eq_iff_eq_mul_left]
  rw [← Nat.pow_pred_mul] <;> omega
  omega
  have h3 : (2 ∣ 2 ^ n) = (2 ^ 1 ∣ 2 ^ n) := by simp
  simp [h3]
  apply Nat.pow_dvd_pow <;> omega

namespace F

def TcbTheoremsTheoremPow2Div2Pow2_proof : TcbTheoremsTheoremPow2Div2Pow2 := by
  unfold TcbTheoremsTheoremPow2Div2Pow2
  intro n ⟨n_pow2, n_ge4⟩ n_ge0 n_in_bounds
  have nnat_in_bounds : n.toNat < 2 ^ 32 := by omega
  have ntwo_in_bounds : n.toNat / 2 < 2 ^ 32 := by omega
  rw [← Int.toNat_of_nonneg n_ge0] at n_pow2
  have nnat_pow2 : pow2 n.toNat :=
    (tcb_defs_pow2_eq_pow2 n.toNat nnat_in_bounds).mp n_pow2
  have half_pow2 : pow2 (n.toNat / 2) :=
    pow2_div2_pow2 n.toNat nnat_pow2 (by omega)
  have half_i_pow2 : F.tcb_defs_pow2 (↑(n.toNat / 2)) :=
    (tcb_defs_pow2_eq_pow2 (n.toNat / 2) ntwo_in_bounds).mpr half_pow2
  have key : n / 2 = ↑(n.toNat / 2) := by
    have := Int.toNat_of_nonneg n_ge0
    omega
  rw [key]
  exact half_i_pow2

end F
