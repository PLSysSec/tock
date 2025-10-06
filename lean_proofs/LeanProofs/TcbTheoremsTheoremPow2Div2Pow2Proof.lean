import LeanProofs.TcbTheoremsTheoremPow2Div2Pow2
import LeanProofs.SharedLemmas

theorem f_pow2_eq_i_pow2 : f_pow2_0 = i_pow2 := by
  funext x; unfold f_pow2_0 i_pow2; simp

theorem pow_right_inj (ha : 1 < a) : a ^ m = a ^ n ↔ m = n := by
  simp [Nat.le_antisymm_iff, Nat.pow_le_pow_iff_right ha]

theorem four_is_pow2 : pow2 4 := by simp

theorem pow2_div2_pow2 (x : Nat) : pow2 x -> x >= 4 -> pow2 (x / 2) := by
  intros h1 h2
  rcases (pow2_isPowerOfTwo x).mp h1 with ⟨n, hy⟩
  rcases (pow2_isPowerOfTwo 4).mp four_is_pow2 with ⟨m, hz⟩
  apply (pow2_isPowerOfTwo (x / 2)).mpr
  simp_all
  simp [Nat.isPowerOfTwo]
  exists (n - 1)
  have hn: n ≥ 1 := by
    simp_all [Nat.pow_le_pow_iff_right]
    have h_eq : 2 ^ 2 = 2 ^ m := by rw [← hz]
    have hm: m = 2 := by
      rw [pow_right_inj] at h_eq ; simp_all ; omega
    simp_all; omega
  rw [Nat.div_eq_iff_eq_mul_left]
  rw [<- Nat.pow_pred_mul] <;> omega
  omega
  have h3 : (2 ∣ 2 ^ n) = (2 ^ 1 ∣ 2 ^ n) := by simp
  simp [h3]
  apply Nat.pow_dvd_pow <;> omega


def tcb_theorems_theorem_pow2_div2_pow2_proof : tcb_theorems_theorem_pow2_div2_pow2 := by
  unfold tcb_theorems_theorem_pow2_div2_pow2
  intro n _ h _ n_ge0 _ n_in_bounds
  obtain ⟨n_pow2, n_ge4⟩ := h
  rw [f_pow2_eq_i_pow2] at *
  have ntwo_in_bounds: (n.toNat / 2) < 2 ^ 32 := by omega
  have nnat_in_bounds: n.toNat < 2 ^ 32 := by omega
  have res_n: f_pow2_0 (n.toNat / 2) = true := by
    apply (i_pow2_eq_pow2 (n.toNat / 2) ntwo_in_bounds).mpr
    apply pow2_div2_pow2
    apply (i_pow2_eq_pow2 n.toNat nnat_in_bounds).mp
    rw [Int.toNat_of_nonneg]
    assumption
    assumption
    omega
  rw [Int.toNat_of_nonneg] at res_n
  assumption
  assumption
