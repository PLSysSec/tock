-- GENERATED; DO NOT EDIT --
-- FUNCTIONS --
def f_aligned_1 (a2 : Int) (a3 : Int) : Bool :=
  ((a2 % a3) = 0)

def f_pow2_0 (a0 : Int) : Bool :=
  (let a1 := (BitVec.ofInt 32 a0); ((a0 > 0) && ((BitVec.and a1 (BitVec.sub a1 1#32)) = 0#32)))

-- THEOREM --
def tcb_theorems_theorem_aligned_value_ge32_lowest_five_bits0 : Prop := (∀ (reftgen_x_0 : Int), (∀ (reftgen_y_1 : Int), (∀ (__ : Int), (((reftgen_y_1 ≥ 32) ∧ (f_pow2_0 reftgen_y_1) ∧ (f_aligned_1 reftgen_x_0 reftgen_y_1)) -> (∀ (__ : Int), ((reftgen_x_0 ≥ 0) -> (∀ (__ : Int), ((reftgen_x_0 ≤ 4294967295) -> (∀ (__ : Int), ((reftgen_y_1 ≥ 0) -> (∀ (__ : Int), ((reftgen_y_1 ≤ 4294967295) -> ((BitVec.and (BitVec.ofInt 32 reftgen_x_0) 31#32) = 0#32)))))))))))))

