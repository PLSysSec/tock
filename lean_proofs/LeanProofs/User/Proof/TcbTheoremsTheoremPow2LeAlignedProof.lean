import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TcbTheoremsTheoremPow2LeAligned
import LeanProofs.SharedLemmas
open Classical
set_option linter.unusedVariables false

private theorem mod_pow2_le {x n m : Nat} : m ≤ n → x % 2 ^ n = 0 → x % 2 ^ m = 0 := by
  intros h1 h2
  simp_all [Nat.mod_eq_iff]
  rcases h2 with ⟨a, ⟨k, _⟩⟩
  case _ =>
    apply And.intro
    · apply Nat.pow_pos; simp
    · exists (2 ^ (n - m) * k)
      conv => right; rw [← Nat.mul_assoc]; left; rw [Nat.mul_comm, Nat.pow_sub_mul_pow 2 h1]
      assumption

private theorem pow2_le_aligned (x y z : Nat) :
    x % y = 0 → z ≤ y → pow2 y → pow2 z → x % z = 0 := by
  intros h1 h2 h3 h4
  rcases (pow2_isPowerOfTwo y).mp h3 with ⟨n, hy⟩
  rcases (pow2_isPowerOfTwo z).mp h4 with ⟨m, hz⟩
  simp_all
  have h := (Nat.pow_le_pow_iff_right (a := 2) (by simp)).mp h2
  apply mod_pow2_le h
  assumption

namespace F

def TcbTheoremsTheoremPow2LeAligned_proof : TcbTheoremsTheoremPow2LeAligned := by
  unfold TcbTheoremsTheoremPow2LeAligned
  intro x₀ y₀ z₀ ⟨x_aligned_y, z_le_y, y_pow2, z_pow2⟩ x_ge0 x_in_bounds y_ge0 y_in_bounds z_ge0 z_in_bounds
  unfold tcb_defs_aligned at *
  have nat_res : x₀.toNat % z₀.toNat = 0 := by
    apply pow2_le_aligned x₀.toNat y₀.toNat z₀.toNat
    · rw [← Int.toNat_of_nonneg x_ge0, ← Int.toNat_of_nonneg y_ge0] at x_aligned_y
      omega
    · omega
    · apply (tcb_defs_pow2_eq_pow2 y₀.toNat (by omega)).mp
      rw [Int.toNat_of_nonneg y_ge0]; exact y_pow2
    · apply (tcb_defs_pow2_eq_pow2 z₀.toNat (by omega)).mp
      rw [Int.toNat_of_nonneg z_ge0]; exact z_pow2
  rw [← Int.toNat_of_nonneg x_ge0, ← Int.toNat_of_nonneg z_ge0]
  omega

end F
