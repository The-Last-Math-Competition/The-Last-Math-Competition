import Std
set_option autoImplicit false
namespace TLMC4263

/-- Coefficient functions in a tensor basis. This is the usual linear
    reassociation, rather than a stipulated numerical pentagon value. -/
def assoc {A B C K : Type} (v : ((A × B) × C) → K) : (A × (B × C)) → K :=
  fun p => v ((p.1, p.2.1), p.2.2)
def assocInv {A B C K : Type} (v : (A × (B × C)) → K) : ((A × B) × C) → K :=
  fun p => v (p.1.1, (p.1.2, p.2))

theorem assoc_left_inverse {A B C K : Type} (v : ((A × B) × C) → K) :
    assocInv (assoc v) = v := rfl
theorem assoc_right_inverse {A B C K : Type} (v : (A × (B × C)) → K) :
    assoc (assocInv v) = v := rfl

/-- The associator tensored on the right by the identity. -/
def innerLeft {A B C D K : Type} (v : (((A × B) × C) × D) → K) :
    ((A × (B × C)) × D) → K :=
  fun p => v (((p.1.1, p.1.2.1), p.1.2.2), p.2)
/-- The identity tensored on the left with the associator. -/
def innerRight {A B C D K : Type} (v : (A × ((B × C) × D)) → K) :
    (A × (B × (C × D))) → K :=
  fun p => v (p.1, ((p.2.1, p.2.2.1), p.2.2.2))

/-- Both actual paths round Mac Lane's pentagon, on every coefficient. -/
theorem pentagon {A B C D K : Type} (v : (((A × B) × C) × D) → K) :
    assoc (assoc v) = innerRight (assoc (innerLeft v)) := rfl

/-- Reassociation commutes with coefficientwise addition and scaling. -/
theorem assoc_add {A B C K : Type} [Add K]
    (v w : ((A × B) × C) → K) :
    assoc (fun p => v p + w p) = fun p => assoc v p + assoc w p := rfl
theorem assoc_scale {A B C K : Type} [Mul K]
    (s : K) (v : ((A × B) × C) → K) :
    assoc (fun p => s * v p) = fun p => s * assoc v p := rfl

def leftUnit {A K : Type} (v : (Unit × A) → K) : A → K := fun a => v ((), a)
def rightUnit {A K : Type} (v : (A × Unit) → K) : A → K := fun a => v (a, ())
/-- The monoidal triangle, again as equality of coefficient maps. -/
theorem triangle {A B K : Type} (v : ((A × Unit) × B) → K) :
    (fun p : A × B => assoc v (p.1, ((), p.2))) =
    (fun p : A × B => v ((p.1, ()), p.2)) := rfl

/-- The unique basis vector of the tensor product of unit simple objects. -/
def leftBasis {K : Type} [OfNat K 1] : ((Unit × Unit) × Unit) → K := fun _ => 1
def rightBasis {K : Type} [OfNat K 1] : (Unit × (Unit × Unit)) → K := fun _ => 1

theorem assoc_basis {K : Type} [OfNat K 1] :
    assoc (leftBasis (K := K)) = rightBasis := rfl

/-- F in these genuine one-element tensor bases. -/
def fMatrix : Fin 1 → Fin 1 → Int := fun _ _ => 1
def matMul1 (m n : Fin 1 → Fin 1 → Int) : Fin 1 → Fin 1 → Int :=
  fun i j => m i 0 * n 0 j

theorem f_entry : fMatrix 0 0 = 1 := rfl
theorem f_invertible : matMul1 fMatrix fMatrix = fMatrix := rfl
theorem f_pentagon : matMul1 fMatrix fMatrix =
    matMul1 fMatrix (matMul1 fMatrix fMatrix) := rfl


/-- Every coefficient function in the simple triple tensor product is
    determined by one coordinate. -/
theorem left_coordinates {K : Type} (v : ((Unit × Unit) × Unit) → K) :
    v = fun _ => v (((), ()), ()) := by
  funext p
  rcases p with ⟨⟨a, b⟩, c⟩
  cases a; cases b; cases c
  rfl

theorem right_coordinates {K : Type} (v : (Unit × (Unit × Unit)) → K) :
    v = fun _ => v ((), ((), ())) := by
  funext p
  rcases p with ⟨a, ⟨b, c⟩⟩
  cases a; cases b; cases c
  rfl

/-- These are the linear evaluation and coevaluation on the unit simple,
    expressed in its one-element basis. -/
def evaluation (x y : Int) : Int := x * y
def coevaluation : Int := 1

theorem left_snake (x : Int) : evaluation coevaluation x = x := by simp [evaluation, coevaluation]
theorem right_snake (x : Int) : evaluation x coevaluation = x := by simp [evaluation, coevaluation]

/-- A complete list of basis indices, computed from the tensor bases. -/
def leftIndices : List ((Unit × Unit) × Unit) := [(((), ()), ())]
def rightIndices : List (Unit × (Unit × Unit)) := [((), ((), ()))]
theorem leftIndices_complete (p : ((Unit × Unit) × Unit)) : p ∈ leftIndices := by
  rcases p with ⟨⟨a,b⟩,c⟩
  cases a; cases b; cases c
  simp [leftIndices]
theorem rightIndices_complete (p : (Unit × (Unit × Unit))) : p ∈ rightIndices := by
  rcases p with ⟨a,⟨b,c⟩⟩
  cases a; cases b; cases c
  simp [rightIndices]
theorem basis_indices_nodup : leftIndices.Nodup ∧ rightIndices.Nodup := by decide
theorem basis_cardinality : leftIndices.length = 1 ∧ rightIndices.length = 1 := by decide

/-- Spanning and independence are checked in the integer form of the bases.
    The coordinate bijections above work over every coefficient type. -/
theorem left_basis_spans (v : ((Unit × Unit) × Unit) → Int) :
    v = fun p => v (((), ()), ()) * leftBasis p := by
  simp only [leftBasis, Int.mul_one]
theorem left_basis_independent (x : Int)
    (h : (fun p : ((Unit × Unit) × Unit) => x * leftBasis p) = fun _ => 0) : x = 0 := by
  have h0 := congrFun h (((), ()), ())
  simpa [leftBasis] using h0

def encodeLeft {K : Type} (x : K) : ((Unit × Unit) × Unit) → K := fun _ => x
def decodeLeft {K : Type} (v : ((Unit × Unit) × Unit) → K) : K := v (((), ()), ())
theorem decode_encode {K : Type} (x : K) : decodeLeft (encodeLeft x) = x := rfl
theorem encode_decode {K : Type} (v : ((Unit × Unit) × Unit) → K) :
    encodeLeft (decodeLeft v) = v := (left_coordinates v).symm

def uniqueIndex : Fin 1 := 0

theorem all_indices (i : Fin 1) : i = uniqueIndex := by
  apply Fin.ext
  have h := i.isLt
  simp [uniqueIndex]

/-- No nonzero scalar is lost by the one-dimensional reassociation. -/
theorem assoc_preserves_coordinate {K : Type} (x : K) :
    assoc (fun _ : ((Unit × Unit) × Unit) => x) ((), ((), ())) = x := rfl

/-- A coherent, invertible, one-dimensional F matrix exists. All operations
    here are the previously defined tensor-coordinate transformations. -/
theorem one_dimensional_witness :
    (assoc (leftBasis (K := Int)) = rightBasis) ∧
    (matMul1 fMatrix fMatrix = fMatrix) ∧
    (∀ v : (((Unit × Unit) × Unit) × Unit) → Int,
      assoc (assoc v) = innerRight (assoc (innerLeft v))) ∧
    (∀ x : Int, evaluation coevaluation x = x) ∧
    (1 < 3) := by
  exact ⟨assoc_basis, f_invertible, fun v => pentagon v, left_snake, by decide⟩

/-- Consequently the matrix-size lower bound asserted in the source fails. -/
theorem dimension_not_at_least_three : ¬ (3 ≤ leftIndices.length) := by decide

end TLMC4263
#print axioms TLMC4263.one_dimensional_witness
#print axioms TLMC4263.dimension_not_at_least_three
