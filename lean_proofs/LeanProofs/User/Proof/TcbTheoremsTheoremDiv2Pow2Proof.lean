import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TcbTheoremsTheoremDiv2Pow2
import LeanProofs.SharedLemmas
open Classical
set_option linter.unusedVariables false

namespace F

def TcbTheoremsTheoremDiv2Pow2_proof : TcbTheoremsTheoremDiv2Pow2 := by
  unfold TcbTheoremsTheoremDiv2Pow2
  intro n ⟨n_pow2, n_ge2⟩ n_ge0 n_in_bounds
  have nnat_in_bounds : n.toNat < 2 ^ 32 := by omega
  rw [← Int.toNat_of_nonneg n_ge0] at n_pow2
  have nnat_pow2 := (tcb_defs_pow2_0_is_power_of_2 n.toNat nnat_in_bounds).mp n_pow2
  rcases nnat_pow2 with ⟨k, hy⟩
  cases k with
  | zero => omega
  | succ k' =>
    have hdvd : 2 ∣ n.toNat := ⟨2 ^ k', by omega⟩
    have hnat := Nat.div_mul_cancel hdvd
    omega

end F
