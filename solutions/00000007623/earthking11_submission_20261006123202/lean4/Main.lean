import Std

namespace Tlmc7623

/-- Four-dimensional integer coordinate space. -/
structure Vec4 where
  x1 : Int
  x2 : Int
  x3 : Int
  x4 : Int
deriving DecidableEq, Repr

def zero : Vec4 := ⟨0, 0, 0, 0⟩

/-- The nilpotent Jordan shift `J(a,b,c,d) = (b,c,d,0)`. -/
def J (v : Vec4) : Vec4 := ⟨v.x2, v.x3, v.x4, 0⟩

def e4 : Vec4 := ⟨0, 0, 0, 1⟩

theorem fourth_iterate_zero (v : Vec4) : J (J (J (J v))) = zero := by
  rfl

theorem third_iterate_e4 : J (J (J e4)) = ⟨1, 0, 0, 0⟩ := by
  rfl

theorem third_iterate_nonzero : J (J (J e4)) ≠ zero := by
  decide

theorem second_iterate_nonzero : J (J e4) ≠ zero := by
  decide

/-- `J^4 = 0` but `J^3 != 0`: the nilpotency index is exactly four. -/
theorem nilpotency_index_four :
    (∀ v, J (J (J (J v))) = zero) ∧ ∃ v, J (J (J v)) ≠ zero :=
  ⟨fourth_iterate_zero, ⟨e4, third_iterate_nonzero⟩⟩

end Tlmc7623
