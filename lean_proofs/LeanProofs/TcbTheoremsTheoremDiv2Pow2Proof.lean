import LeanProofs.TcbTheoremsTheoremDiv2Pow2
import LeanProofs.SharedLemmas

theorem f_pow2_0_eq_i_pow2 : f_pow2_0 = i_pow2 := by
  funext x; unfold f_pow2_0 i_pow2; simp

def tcb_theorems_theorem_div2_pow2_proof : tcb_theorems_theorem_div2_pow2 := by
  unfold tcb_theorems_theorem_div2_pow2
  intro n _ h _ n_ge0 _ n_in_bounds
  obtain ⟨n_pow2, n_ge2⟩ := h
  rw [f_pow2_0_eq_i_pow2] at *
  have res_nat : (n.toNat / 2) * 2 = n.toNat := by
    rw [Nat.div_mul_cancel]
    rw [←Int.toNat_of_nonneg n_ge0] at n_pow2
    have nnat_pow2 := (i_pow2_0_is_power_of_2 n.toNat (by omega)).mp n_pow2
    rcases nnat_pow2 with ⟨k, hy⟩
    cases k with
    | zero => omega
    | succ k' => omega
  omega
