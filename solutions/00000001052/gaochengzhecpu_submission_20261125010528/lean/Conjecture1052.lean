import Std

namespace Conjecture1052

/-- The coordinates of a + b i in F₃[i], where i² = -1. -/
structure F9 where
  real : Fin 3
  imag : Fin 3
  deriving DecidableEq

instance : OfNat F9 0 := ⟨⟨0, 0⟩⟩
instance : OfNat F9 1 := ⟨⟨1, 0⟩⟩
instance : Add F9 := ⟨fun x y => ⟨x.real + y.real, x.imag + y.imag⟩⟩
instance : Sub F9 := ⟨fun x y => ⟨x.real - y.real, x.imag - y.imag⟩⟩
instance : Mul F9 := ⟨fun x y =>
  ⟨x.real * y.real - x.imag * y.imag, x.real * y.imag + x.imag * y.real⟩⟩

def square (x : F9) : F9 := x * x
def cube (x : F9) : F9 := square x * x
def fourth (x : F9) : F9 := square (square x)

def fieldElements : List F9 :=
  (List.finRange 3).flatMap fun a => (List.finRange 3).map fun b => ⟨a, b⟩

private theorem mem_finRange {n : Nat} (i : Fin n) : i ∈ List.finRange n := by
  have indexBound : i.val < (List.finRange n).length := by
    rw [List.length_finRange]
    exact i.isLt
  have element : (List.finRange n)[i.val]'indexBound = i := by
    apply Fin.ext
    simp
  rw [← element]
  exact List.getElem_mem _

theorem field_elements_complete (value : F9) : value ∈ fieldElements := by
  cases value with
  | mk a b =>
    exact List.mem_flatMap.mpr ⟨a, mem_finRange a, List.mem_map.mpr ⟨b, mem_finRange b, rfl⟩⟩

/-- The three disjoint normalized charts [x:y:1], [1:y:0], and [0:1:0]. -/
inductive ProjectivePoint where
  | affine (x y : F9)
  | horizontalInfinity (y : F9)
  | verticalInfinity
  deriving DecidableEq

def affinePoints : List ProjectivePoint :=
  fieldElements.flatMap fun x => fieldElements.map fun y => .affine x y

def pointsAtInfinity : List ProjectivePoint :=
  fieldElements.map ProjectivePoint.horizontalInfinity ++ [.verticalInfinity]

def projectivePoints : List ProjectivePoint := affinePoints ++ pointsAtInfinity

theorem projective_points_complete (point : ProjectivePoint) : point ∈ projectivePoints := by
  unfold projectivePoints affinePoints pointsAtInfinity
  cases point with
  | affine x y =>
    apply List.mem_append_left
    exact List.mem_flatMap.mpr
      ⟨x, field_elements_complete x, List.mem_map.mpr ⟨y, field_elements_complete y, rfl⟩⟩
  | horizontalInfinity y =>
    apply List.mem_append_right
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨y, field_elements_complete y, rfl⟩
  | verticalInfinity =>
    exact List.mem_append_right _ (List.mem_append_right _ List.mem_cons_self)

set_option maxRecDepth 4096 in
theorem projective_points_distinct : projectivePoints.Nodup := by decide

def coordinates (point : ProjectivePoint) : F9 × F9 × F9 :=
  match point with
  | .affine x y => (x, y, 1)
  | .horizontalInfinity y => (1, y, 0)
  | .verticalInfinity => (0, 1, 0)

/-- Homogeneous form Y²Z = X³ - XZ². -/
def ellipticEquation (point : ProjectivePoint) : Bool :=
  let (x, y, z) := coordinates point
  decide (square y * z = cube x - x * square z)

/-- Homogeneous form Y³Z + YZ³ = X⁴. -/
def hermitianEquation (point : ProjectivePoint) : Bool :=
  let (x, y, z) := coordinates point
  decide (cube y * z + y * cube z = fourth x)

theorem affine_point_counts :
    (affinePoints.filter ellipticEquation).length = 15 ∧
    (affinePoints.filter hermitianEquation).length = 27 := by decide

theorem points_at_infinity :
    pointsAtInfinity.filter ellipticEquation = [.verticalInfinity] ∧
    pointsAtInfinity.filter hermitianEquation = [.verticalInfinity] := by decide

def pointCount (equation : ProjectivePoint → Bool) : Nat :=
  (projectivePoints.filter equation).length

def hasseWeilUpperBound (q genus : Nat) : Nat := q * q + 1 + 2 * genus * q

def smoothPlaneGenus (degree : Nat) : Nat := (degree - 1) * (degree - 2) / 2

def conjecturedGenus (q : Nat) : Nat := (q - 1) * (q - 1) / 4

theorem counterexample_data :
    smoothPlaneGenus 3 = conjecturedGenus 3 ∧
    smoothPlaneGenus 3 = 1 ∧ smoothPlaneGenus 4 = 3 ∧
    pointCount ellipticEquation = 16 ∧
    pointCount ellipticEquation = hasseWeilUpperBound 3 (smoothPlaneGenus 3) ∧
    pointCount hermitianEquation = 28 ∧
    pointCount ellipticEquation ≠ pointCount hermitianEquation := by decide

end Conjecture1052

#print axioms Conjecture1052.projective_points_complete
#print axioms Conjecture1052.projective_points_distinct
#print axioms Conjecture1052.affine_point_counts
#print axioms Conjecture1052.points_at_infinity
#print axioms Conjecture1052.counterexample_data
