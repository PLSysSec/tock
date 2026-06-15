import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TcbTheoremsTheoremPow2Octet
import LeanProofs.SharedLemmas
open Classical
set_option linter.unusedVariables false

private theorem power_of_2_ge_8_octet (x : Nat) : x.isPowerOfTwo → x ≥ 8 → x % 8 = 0 := by
  intro x_pow2 x_ge8
  apply Nat.mod_eq_zero_of_dvd
  unfold Nat.isPowerOfTwo at x_pow2
  cases x_pow2 with
  | intro k hk =>
    have h : (8 = 2 ^ 3) := by simp
    rw [hk, h, Nat.pow_dvd_pow_iff_le_right]
    case _ =>
      rw [hk, h] at x_ge8
      rw [← (@Nat.pow_le_pow_iff_right 2 3 k)]
      exact x_ge8
      simp
    case _ => simp

namespace F

def TcbTheoremsTheoremPow2Octet_proof : TcbTheoremsTheoremPow2Octet := by
  unfold TcbTheoremsTheoremPow2Octet
  intro r₀ ⟨r₀_pow2, r₀_ge8⟩ r₀_ge0 r₀_in_bounds
  unfold tcb_defs_octet
  have nnat_in_bounds : r₀.toNat < 2 ^ 32 := by omega
  rw [← Int.toNat_of_nonneg r₀_ge0] at r₀_pow2
  have nat_pow2 := (tcb_defs_pow2_0_is_power_of_2 r₀.toNat nnat_in_bounds).mp r₀_pow2
  have nat_res : r₀.toNat % 8 = 0 := power_of_2_ge_8_octet r₀.toNat nat_pow2 (by omega)
  omega

end F
