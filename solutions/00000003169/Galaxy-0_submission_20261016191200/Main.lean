import Algebra
import Geometry
open Lean.Grind Std
attribute [local instance] Semiring.natCast Ring.intCast
namespace TLMC3169
section RootCount
variable {R : Type} [CommRing R]
def rootList : List (R × R) := [(1,-2)]
theorem rootList_complete (x y : R) : CommonZero x y ↔ (x,y) ∈ (rootList : List (R × R)) := by
  rw [roots_exact]
  simp [rootList, Prod.mk.injEq]
theorem rootList_nodup : (rootList : List (R × R)).Nodup := by simp [rootList]
theorem rootList_length : (rootList : List (R × R)).length=1 := rfl
end RootCount
section Conclusion
variable {R : Type} [Field R] [LE R] [LT R] [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R]
-- The count is the length of the proved complete, repetition-free root enumeration.
-- The RHS is the area polarization for the proved Newton triangles and their sum.
def countedRoots (K : Type) [CommRing K] : R := @NatCast.natCast R (Semiring.natCast (α := R))
  (rootList : List (K × K)).length
def bkkMixedArea : R := triangleArea (4:R)-triangleArea (1:R)-triangleArea (3:R)
def classicalMixedArea : R := bkkMixedArea / 2
omit [LE R] [LT R] [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R] in
theorem count_eq_one (K : Type) [CommRing K] : countedRoots (R := R) K=1 := by
  change (@NatCast.natCast R (Semiring.natCast (α := R)) 1)=1
  exact (Semiring.ofNat_eq_natCast 1).symm
theorem conjecture_00000003169_counterexample (K : Type) [CommRing K] :
  countedRoots (R := R) K ≠ bkkMixedArea (R := R) ∧
  countedRoots (R := R) K ≠ classicalMixedArea (R := R) := by
  have h := both_mixed_values_differ_from_one (R := R)
  rw [count_eq_one]
  unfold classicalMixedArea bkkMixedArea
  grind
end Conclusion
end TLMC3169
