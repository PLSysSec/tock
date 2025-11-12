namespace Nat

def bit (b : Bool) : Nat → Nat := cond b (2 * · + 1) (2 * ·)

theorem shiftRight_one (n) : n >>> 1 = n / 2 := rfl

@[simp]
theorem bit_decide_mod_two_eq_one_shiftRight_one (n : Nat) : bit (n % 2 = 1) (n >>> 1) = n := by
  simp only [bit, shiftRight_one]
  cases mod_two_eq_zero_or_one n with | _ h => simpa [h] using Nat.div_add_mod n 2

theorem bit_testBit_zero_shiftRight_one (n : Nat) : bit (n.testBit 0) (n >>> 1) = n := by
  simp

/-- A recursion principle for `bit` representations of natural numbers.
  For a predicate `motive : Nat → Sort u`, if instances can be
  constructed for natural numbers of the form `bit b n`,
  they can be constructed for all natural numbers. -/
@[elab_as_elim, specialize]
def binaryRec {motive : Nat → Sort u} (z : motive 0) (f : ∀ b n, motive n → motive (bit b n))
    (n : Nat) : motive n :=
  if n0 : n = 0 then congrArg motive n0 ▸ z
  else
    let x := f (1 &&& n != 0) (n >>> 1) (binaryRec z f (n >>> 1))
    congrArg motive n.bit_testBit_zero_shiftRight_one ▸ x
decreasing_by exact bitwise_rec_lemma n0

end Nat

theorem le_max_of_nat_eq_of_nat {w : Nat} (x y : Nat) :
    x < 2 ^ w → y < 2 ^ w → (BitVec.ofNat w x = BitVec.ofNat w y ↔ x = y) := by
  intros hx hy
  apply Iff.intro
  case mp =>
    intro bv_eq
    have fin_eq := congrArg BitVec.toFin bv_eq
    simp [BitVec.toFin_ofNat, Fin.ofNat] at fin_eq
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] at fin_eq
    exact fin_eq
    exact hy
    exact hx
  case mpr =>
    intro eq
    rw [eq]

@[simp]
def pow2 (n : Nat) : Bool :=
  (n > 0) && ((n &&& (n - 1)) == 0)

def i_pow2 (n : Int) : Bool :=
  (let a3 := (BitVec.ofInt 32 n); ((n > 0) && ((BitVec.and a3 (BitVec.sub a3 1#32)) = 0#32)))

theorem i_pow2_eq_pow2 (x: Nat) : (x < 2 ^ 32) -> (i_pow2 x <-> pow2 x) := by
  unfold i_pow2 pow2
  simp
  intros x_in_bounds xgt0
  apply Iff.intro
  case mp =>
    intros bv_eq
    rw [
      BitVec.ofNat_sub_ofNat_of_le,
      ← BitVec.ofNat_and,
      le_max_of_nat_eq_of_nat
    ] at bv_eq
    exact bv_eq
    case _ =>
      apply Nat.lt_of_le_of_lt
      exact @Nat.and_le_right x (x - 1)
      apply Nat.lt_trans (by omega : (x - 1) < x)
      simp; exact x_in_bounds
    case _ =>
      simp
    case _ =>
      simp
    case _ =>
      exact xgt0
  case mpr =>
    intros bv_eq
    rw [
      BitVec.ofNat_sub_ofNat_of_le,
      ← BitVec.ofNat_and,
      le_max_of_nat_eq_of_nat
    ]
    exact bv_eq
    case _ =>
      apply Nat.lt_of_le_of_lt
      exact @Nat.and_le_right x (x - 1)
      apply Nat.lt_trans (by omega : (x - 1) < x)
      simp; exact x_in_bounds
    case _ => simp
    case _ => simp
    case _ => exact xgt0

theorem fold_land : (Nat.bitwise and x x) = x &&& x := by rfl

theorem pow2_isPowerOfTwo (x : Nat) : pow2 x <-> x.isPowerOfTwo := by
  apply Iff.intro
  case mp =>
    intro h
    induction x using Nat.binaryRec
    case z => simp_all!
    case f b n ih =>
      simp_all [Nat.bit]
      cases b
      · simp_all!
        rcases h with ⟨_, h⟩
        rw [Nat.mul_comm]
        apply Nat.isPowerOfTwo_mul_two_of_isPowerOfTwo
        apply ih
        simp_all [HAnd.hAnd, AndOp.and, Nat.land]
        unfold Nat.bitwise at h
        split at h ; omega
        split at h ; omega
        simp_all
        have p : (2 * n - 1) /2 = n - 1 := by cases n ; trivial ; simp +arith [Nat.left_distrib, Nat.mul_add_div]
        simp_all
      · simp_all
        simp [HAnd.hAnd, AndOp.and, Nat.land] at h
        unfold Nat.bitwise at h
        split at h ; simp_all
        split at h ; simp_all ; exists 0
        simp_all [Nat.mul_add_div, fold_land]
  case mpr =>
    intro h
    rcases h with ⟨n, h⟩
    simp
    and_intros
    · simp_all ; apply Nat.pow_pos ; simp
    · induction n generalizing x <;> simp_all

theorem i_pow2_0_is_power_of_2 (x: Nat) : (x < 2 ^ 32) -> (i_pow2 x <-> x.isPowerOfTwo) := by
  intro x_in_bounds
  apply Iff.intro
  case _ =>
    intro x_pow2
    rw [← pow2_isPowerOfTwo x]
    apply (i_pow2_eq_pow2 x x_in_bounds).mp
    exact x_pow2
  case _ =>
    intro x_pow2
    apply (i_pow2_eq_pow2 x x_in_bounds).mpr
    rw [pow2_isPowerOfTwo]
    exact x_pow2
