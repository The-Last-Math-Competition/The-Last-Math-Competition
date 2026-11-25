import Std

namespace Conjecture905

abbrev Matrix (n : Nat) := Fin n → Fin n → Int
abbrev Vector (n : Nat) := Fin n → Int

def multiply {n : Nat} (left right : Matrix n) : Matrix n := fun i j =>
  ((List.finRange n).map fun k => left i k * right k j).sum

def applyMatrix {n : Nat} (matrix : Matrix n) (v : Vector n) : Vector n := fun i =>
  ((List.finRange n).map fun j => matrix i j * v j).sum

/-- D₄ with center 0 and leaves 1, 2, 3. -/
def starAdjacency : Matrix 4 := fun i j =>
  if (i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0) then 1 else 0

def squaredAdjacency : Matrix 4 := multiply starAdjacency starAdjacency

/-- Exact distance two means different vertices with a two-step walk
    and no direct edge. -/
def distanceTwoAdjacency : Matrix 4 := fun i j =>
  if i ≠ j ∧ starAdjacency i j = 0 ∧ 0 < squaredAdjacency i j then 1 else 0

def squaredBlockForm : Matrix 4 := fun i j =>
  if i = 0 then (if j = 0 then 3 else 0) else (if j = 0 then 0 else 1)

def distanceTwoBlockForm : Matrix 4 := fun i j =>
  if i ≠ 0 ∧ j ≠ 0 ∧ i ≠ j then 1 else 0

private theorem vertex_cases (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have bound := i.isLt
  have values : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases values with zero | one | two | three
  · exact Or.inl (Fin.ext zero)
  · exact Or.inr (Or.inl (Fin.ext one))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext two)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext three)))

private theorem leaf_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  have bound := i.isLt
  have values : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases values with zero | one | two
  · exact Or.inl (Fin.ext zero)
  · exact Or.inr (Or.inl (Fin.ext one))
  · exact Or.inr (Or.inr (Fin.ext two))

theorem squared_block_form (i j : Fin 4) :
    squaredAdjacency i j = squaredBlockForm i j := by
  rcases vertex_cases i with rfl | rfl | rfl | rfl <;>
    rcases vertex_cases j with rfl | rfl | rfl | rfl <;> decide

theorem distance_two_block_form (i j : Fin 4) :
    distanceTwoAdjacency i j = distanceTwoBlockForm i j := by
  rcases vertex_cases i with rfl | rfl | rfl | rfl <;>
    rcases vertex_cases j with rfl | rfl | rfl | rfl <;> decide

def leafIndex (i : Fin 3) : Fin 4 := ⟨i.val + 1, by
  have bound := i.isLt
  omega⟩

def leafBlock (matrix : Matrix 4) : Matrix 3 := fun i j =>
  matrix (leafIndex i) (leafIndex j)

def leafToCenter : Vector 3 := fun i => starAdjacency (leafIndex i) 0

theorem squared_leaf_block (i j : Fin 3) :
    leafBlock squaredAdjacency i j = leafToCenter i * leafToCenter j := by
  rcases leaf_cases i with rfl | rfl | rfl <;>
    rcases leaf_cases j with rfl | rfl | rfl <;> decide

def IsEigenvector {n : Nat} (matrix : Matrix n) (eigenvalue : Int) (v : Vector n) : Prop :=
  (∃ i, v i ≠ 0) ∧ ∀ i, applyMatrix matrix v i = eigenvalue * v i

def leafOnes : Vector 4 := fun i => if i = 0 then 0 else 1
def allOnes : Vector 3 := fun _ => 1

theorem squared_eigenvector : IsEigenvector squaredAdjacency 3 leafOnes := by
  refine ⟨⟨1, by decide⟩, ?_⟩
  intro i
  rcases vertex_cases i with rfl | rfl | rfl | rfl <;> decide

theorem distance_two_eigenvector : IsEigenvector distanceTwoAdjacency 2 leafOnes := by
  refine ⟨⟨1, by decide⟩, ?_⟩
  intro i
  rcases vertex_cases i with rfl | rfl | rfl | rfl <;> decide

theorem squared_leaf_eigenvector : IsEigenvector (leafBlock squaredAdjacency) 3 allOnes := by
  refine ⟨⟨0, by decide⟩, ?_⟩
  intro i
  rcases leaf_cases i with rfl | rfl | rfl <;> decide

theorem distance_two_leaf_eigenvector :
    IsEigenvector (leafBlock distanceTwoAdjacency) 2 allOnes := by
  refine ⟨⟨0, by decide⟩, ?_⟩
  intro i
  rcases leaf_cases i with rfl | rfl | rfl <;> decide

theorem no_positive_power_eq_one {value exponent : Nat} (large : 2 ≤ value)
    (positive : 0 < exponent) : value ^ exponent ≠ 1 := by
  have bound : value ^ 1 ≤ value ^ exponent :=
    Nat.pow_le_pow_right (by omega) positive
  rw [Nat.pow_one] at bound
  omega

theorem two_and_three_are_not_roots_of_unity (exponent : Nat) (positive : 0 < exponent) :
    (2 : Nat) ^ exponent ≠ 1 ∧ (3 : Nat) ^ exponent ≠ 1 :=
  ⟨no_positive_power_eq_one (by decide) positive, no_positive_power_eq_one (by decide) positive⟩

/-- Polynomial coefficients in increasing order of degree. -/
abbrev Polynomial := List Int

def addCoefficients : Polynomial → Polynomial → Polynomial
  | [], right => right
  | left, [] => left
  | a :: left, b :: right => (a + b) :: addCoefficients left right

def scaleCoefficients (scalar : Int) (p : Polynomial) : Polynomial :=
  p.map fun coefficient => scalar * coefficient

def multiplyCoefficients : Polynomial → Polynomial → Polynomial
  | [], _ => []
  | a :: left, right =>
    addCoefficients (scaleCoefficients a right) (0 :: multiplyCoefficients left right)

def normalized (p : Polynomial) : Polynomial := (p.reverse.dropWhile (· == 0)).reverse

/-- Laplace expansion along the first row over the coefficient lists.
    At every recursive call one row is removed, so n steps suffice for n rows. -/
def determinant : Nat → List (List Polynomial) → Polynomial
  | _, [] => [1]
  | 0, _ :: _ => []
  | depth + 1, row :: rest =>
    row.zipIdx.foldr (fun (entry, column) sum =>
      let sign : Int := if column % 2 = 0 then 1 else -1
      let minor := rest.map fun other => other.eraseIdx column
      addCoefficients
        (multiplyCoefficients (scaleCoefficients sign entry) (determinant depth minor)) sum) []

def characteristicPolynomial {n : Nat} (matrix : Matrix n) : Polynomial :=
  normalized (determinant n ((List.finRange n).map fun i =>
    (List.finRange n).map fun j =>
      if i = j then [-(matrix i j), 1] else [-(matrix i j)]))

set_option maxRecDepth 4096 in
theorem characteristic_polynomials :
    characteristicPolynomial squaredAdjacency = [0, 0, 9, -6, 1] ∧
    characteristicPolynomial distanceTwoAdjacency = [0, -2, -3, 0, 1] ∧
    characteristicPolynomial (leafBlock squaredAdjacency) = [0, 0, -3, 1] ∧
    characteristicPolynomial (leafBlock distanceTwoAdjacency) = [-2, -3, 0, 1] := by
  decide

def evaluatePolynomial (p : Polynomial) (value : Int) : Int :=
  p.foldr (fun coefficient suffix => coefficient + value * suffix) 0

theorem characteristic_polynomial_roots :
    evaluatePolynomial (characteristicPolynomial squaredAdjacency) 3 = 0 ∧
    evaluatePolynomial (characteristicPolynomial distanceTwoAdjacency) 2 = 0 ∧
    evaluatePolynomial (characteristicPolynomial (leafBlock squaredAdjacency)) 3 = 0 ∧
    evaluatePolynomial (characteristicPolynomial (leafBlock distanceTwoAdjacency)) 2 = 0 := by
  obtain ⟨fullSquare, fullDistance, leafSquare, leafDistance⟩ := characteristic_polynomials
  rw [fullSquare, fullDistance, leafSquare, leafDistance]
  decide

end Conjecture905

#print axioms Conjecture905.squared_block_form
#print axioms Conjecture905.distance_two_block_form
#print axioms Conjecture905.squared_leaf_block
#print axioms Conjecture905.squared_eigenvector
#print axioms Conjecture905.distance_two_eigenvector
#print axioms Conjecture905.squared_leaf_eigenvector
#print axioms Conjecture905.distance_two_leaf_eigenvector
#print axioms Conjecture905.two_and_three_are_not_roots_of_unity
#print axioms Conjecture905.characteristic_polynomials
#print axioms Conjecture905.characteristic_polynomial_roots
