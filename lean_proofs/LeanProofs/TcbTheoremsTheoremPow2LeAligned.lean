-- GENERATED; DO NOT EDIT --
-- FUNCTIONS --
def f_aligned_0 (a0 : Int) (a1 : Int) : Bool :=
  ((a0 % a1) = 0)

def f_pow2_1 (a2 : Int) : Bool :=
  (let a3 := (BitVec.ofInt 32 a2); ((a2 > 0) && ((BitVec.and a3 (BitVec.sub a3 1#32)) = 0#32)))

-- THEOREM --
def tcb_theorems_theorem_pow2_le_aligned : Prop := (∀ (reftgen_x_0 : Int), (∀ (reftgen_y_1 : Int), (∀ (reftgen_z_2 : Int), (∀ (__ : Int), (((f_aligned_0 reftgen_x_0 reftgen_y_1) ∧ (reftgen_z_2 ≤ reftgen_y_1) ∧ (f_pow2_1 reftgen_y_1) ∧ (f_pow2_1 reftgen_z_2)) -> (∀ (__ : Int), ((reftgen_x_0 ≥ 0) -> (∀ (__ : Int), ((reftgen_x_0 ≤ 4294967295) -> (∀ (__ : Int), ((reftgen_y_1 ≥ 0) -> (∀ (__ : Int), ((reftgen_y_1 ≤ 4294967295) -> (∀ (__ : Int), ((reftgen_z_2 ≥ 0) -> (∀ (__ : Int), ((reftgen_z_2 ≤ 4294967295) -> (f_aligned_0 reftgen_x_0 reftgen_z_2))))))))))))))))))

