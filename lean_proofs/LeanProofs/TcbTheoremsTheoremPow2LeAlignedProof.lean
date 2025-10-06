import LeanProofs.TcbTheoremsTheoremPow2LeAligned
import LeanProofs.SharedLemmas

theorem f_pow2_1_eq_i_pow2 : f_pow2_1 = i_pow2 := by
  funext x; unfold f_pow2_1 i_pow2; simp

theorem mod_pow2_le {x n m : Nat} : m <= n -> x % 2 ^ n = 0 -> x % 2 ^ m = 0 := by
  intros h1 h2
  simp_all [Nat.mod_eq_iff]
  rcases h2 with ⟨a, ⟨k, _⟩⟩
  case _ =>
    apply And.intro
    · apply Nat.pow_pos ; simp
    · exists (2 ^ (n - m) * k)
      conv => right ; rw [←Nat.mul_assoc] ; left ; rw [Nat.mul_comm, Nat.pow_sub_mul_pow 2 h1]
      assumption

theorem pow2_le_aligned (x y z : Nat) :
  x % y = 0 ->
  z <= y ->
  pow2 y ->
  pow2 z ->
  x % z = 0 :=
by
  intros h1 h2 h3 h4
  rcases (pow2_isPowerOfTwo y).mp h3 with ⟨n, hy⟩
  rcases (pow2_isPowerOfTwo z).mp h4 with ⟨m, hz⟩
  simp_all
  have h := (Nat.pow_le_pow_iff_right (a := 2) (by simp)).mp h2
  apply mod_pow2_le h
  assumption

def tcb_theorems_theorem_pow2_le_aligned_proof : tcb_theorems_theorem_pow2_le_aligned := by
  unfold tcb_theorems_theorem_pow2_le_aligned
  intros x y z _ h _ x_ge0 _ x_in_bounds _ y_ge0 _ y_in_bounds _ z_ge0 _ z_in_bounds
  obtain ⟨x_aligned_y, ⟨z_le_y, ⟨y_pow2, z_pow2⟩⟩⟩ := h
  rw [f_pow2_1_eq_i_pow2] at *
  unfold f_aligned_0 at *
  simp at x_aligned_y
  simp
  have nat_res : x.toNat % z.toNat = 0 := by
    apply pow2_le_aligned x.toNat y.toNat z.toNat
    · rw [←Int.toNat_of_nonneg x_ge0, ←Int.toNat_of_nonneg y_ge0] at x_aligned_y
      omega
    · omega
    · apply (i_pow2_eq_pow2 y.toNat _).mp
      rw [Int.toNat_of_nonneg]
      assumption
      assumption
      omega
    · apply (i_pow2_eq_pow2 z.toNat _).mp
      rw [Int.toNat_of_nonneg]
      assumption
      assumption
      omega
  rw [←Int.toNat_of_nonneg x_ge0, ←Int.toNat_of_nonneg z_ge0]
  omega
