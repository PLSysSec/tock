-- GENERATED; DO NOT EDIT --
-- FUNCTIONS --
def f_pow2_0 (a0 : Int) : Bool :=
  (let a1 := (BitVec.ofInt 32 a0); ((a0 > 0) && ((BitVec.and a1 (BitVec.sub a1 1#32)) = 0#32)))

-- THEOREM --
def tcb_theorems_theorem_div2_pow2 : Prop := (∀ (reftgen_n_0 : Int), (∀ (__ : Int), (((f_pow2_0 reftgen_n_0) ∧ (reftgen_n_0 ≥ 2)) -> (∀ (__ : Int), ((reftgen_n_0 ≥ 0) -> (∀ (__ : Int), ((reftgen_n_0 ≤ 18446744073709551615) -> (((reftgen_n_0 / 2) * 2) = reftgen_n_0))))))))

