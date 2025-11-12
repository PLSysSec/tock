-- GENERATED; DO NOT EDIT --
-- FUNCTIONS --
def f_octet_1 (a2 : Int) : Bool :=
  ((a2 % 8) = 0)

def f_pow2_0 (a0 : Int) : Bool :=
  (let a1 := (BitVec.ofInt 32 a0); ((a0 > 0) && ((BitVec.and a1 (BitVec.sub a1 1#32)) = 0#32)))

-- THEOREM --
def tcb_theorems_theorem_pow2_octet : Prop := (∀ (reftgen_r_0 : Int), (∀ (__ : Int), (((f_pow2_0 reftgen_r_0) ∧ (reftgen_r_0 ≥ 8)) -> (∀ (__ : Int), ((reftgen_r_0 ≥ 0) -> (∀ (__ : Int), ((reftgen_r_0 ≤ 4294967295) -> (f_octet_1 reftgen_r_0))))))))

