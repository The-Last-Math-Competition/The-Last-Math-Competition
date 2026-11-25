import Std

namespace CentralPolynomial

abbrev Vertex := Fin 3

/-- The coefficients of a², ab, b², in that order. -/
structure Quadratic where
  aa : Int
  ab : Int
  bb : Int
  deriving DecidableEq, Repr

def Quadratic.zero : Quadratic := ⟨0, 0, 0⟩

def Quadratic.add (p q : Quadratic) : Quadratic :=
  ⟨p.aa + q.aa, p.ab + q.ab, p.bb + q.bb⟩

def Quadratic.scale (n : Int) (p : Quadratic) : Quadratic :=
  ⟨n * p.aa, n * p.ab, n * p.bb⟩

def Quadratic.eval (p : Quadratic) (a b : Int) : Int :=
  p.aa * a * a + p.ab * a * b + p.bb * b * b

/-- The two coordinates of a diagonal entry of diag(a,b,−a−b). -/
def diagonalLinear (i : Vertex) : Int × Int :=
  if i = 0 then (1, 0) else if i = 1 then (0, 1) else (-1, -1)

def diagonalProduct (i j : Vertex) : Quadratic :=
  let (a, b) := diagonalLinear i
  let (c, d) := diagonalLinear j
  ⟨a*c, a*d+b*c, b*d⟩

structure Path where
  start : Vertex
  first : Vertex
  second : Vertex
  third : Vertex
  finish : Vertex

def Path.vertices (p : Path) : List Vertex :=
  [p.start, p.first, p.second, p.third, p.finish]

def unitIndex (i j : Vertex) : Nat := 3*i.val + j.val

def Path.edges (p : Path) : List Nat :=
  [unitIndex p.start p.first, unitIndex p.first p.second,
   unitIndex p.second p.third, unitIndex p.third p.finish]

def inversionCount (word : List Nat) : Nat :=
  match word with
  | [] => 0
  | x :: xs => xs.countP (· < x) + inversionCount xs

def alternatingSign (word : List Nat) : Int :=
  if inversionCount word % 2 = 0 then 1 else -1

/-- The two diagonal factors appear after r and s matrix units. -/
def insertionSign (r s : Nat) : Int :=
  if r % 2 = 1 && s % 2 = 1 then -1 else 1

def Path.weight (p : Path) : Quadratic :=
  (List.range 5).foldl (fun sum r =>
    (List.range (5-r)).foldl (fun total d =>
      let s := r+d
      let factor := diagonalProduct p.vertices[r]! p.vertices[s]!
      total.add (factor.scale (insertionSign r s))) sum) Quadratic.zero

abbrev Term := List Nat × Quadratic

def insertUnit (u : Nat) : List Nat → List Nat
  | [] => [u]
  | v :: rest => if u ≤ v then u :: v :: rest else v :: insertUnit u rest

def ascendingUnits (units : List Nat) : List Nat :=
  units.foldr insertUnit []

def strictlyAscendingFrom (u : Nat) : List Nat → Bool
  | [] => true
  | v :: rest => u < v && strictlyAscendingFrom v rest

def distinctAscending : List Nat → Bool
  | [] => true
  | u :: rest => strictlyAscendingFrom u rest

def tupleNumber (units : List Nat) : Nat :=
  units.foldl (fun key u => 9*key + u) 0

def insertContribution (units : List Nat) (q : Quadratic) : List Term → List Term
  | [] => [(units, q)]
  | (key, value) :: rest =>
      if units = key then (key, q.add value) :: rest
      else if tupleNumber units < tupleNumber key then (units, q) :: (key, value) :: rest
      else (key, value) :: insertContribution units q rest

/-- A path contributes exactly its signed weight to its ascending edge tuple.
    A repeated edge is outside the support of an alternating polynomial. -/
def addPath (table : List Term) (p : Path) : List Term :=
  let sorted := ascendingUnits p.edges
  if distinctAscending sorted then
    insertContribution sorted (p.weight.scale (alternatingSign p.edges)) table
  else table

def paths (i j : Vertex) : List Path :=
  (List.finRange 3).flatMap fun a =>
    (List.finRange 3).flatMap fun b =>
      (List.finRange 3).map fun c => ⟨i, a, b, c, j⟩

/-- The complete sorted quadratic coefficient table for one output entry. -/
def coefficientTable (i j : Vertex) : List Term :=
  ((paths i j).foldl addPath []).filter (fun t => t.2 != Quadratic.zero)

def scalarTable : List Term :=
  [([1,2,3,6], ⟨-4, 2, 2⟩),
   ([1,3,5,7], ⟨2, 2, -4⟩),
   ([2,5,6,7], ⟨-4, -10, -4⟩)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem all_diagonal_basis_coefficients : ∀ i j : Vertex,
    coefficientTable i j = if i = j then scalarTable else [] := by decide

def lookupQuad (table : List Term) (units : List Nat) : Quadratic :=
  match table.find? (fun t => t.1 == units) with
  | some (_, q) => q
  | none => Quadratic.zero

/-- Evaluation on distinct basis units with the indicated order. -/
def diagonalBasisValue (i j : Vertex) (units : List Nat) (a b : Int) : Int :=
  let sorted := ascendingUnits units
  let contribution := lookupQuad (coefficientTable i j) sorted
  alternatingSign units * contribution.eval a b

theorem all_diagonal_basis_values_scalar (units : List Nat) (a b : Int) (i j : Vertex) :
    diagonalBasisValue i j units a b =
      if i = j then diagonalBasisValue 0 0 units a b else 0 := by
  by_cases h : i = j
  · simp [diagonalBasisValue, all_diagonal_basis_coefficients, h]
  · simp [diagonalBasisValue, all_diagonal_basis_coefficients, h,
      lookupQuad, Quadratic.zero, Quadratic.eval]

abbrev Matrix := Vertex → Vertex → Int

def unit (i j : Vertex) : Matrix := fun a b => if a = i ∧ b = j then 1 else 0

def matrixProduct (A B : Matrix) : Matrix := fun i j =>
  A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j

def commutator (A B : Matrix) : Matrix := fun i j =>
  matrixProduct A B i j - matrixProduct B A i j

def traceZeroDiagonal (a b : Int) : Matrix := fun i j =>
  if i = j then (diagonalLinear i).1 * a + (diagonalLinear i).2 * b else 0

theorem witness_commutator : ∀ i j : Vertex,
    commutator (unit 0 1) (unit 1 0) i j = traceZeroDiagonal 1 (-1) i j := by decide

theorem witness_evaluation : ∀ i j : Vertex,
    diagonalBasisValue i j
      [unitIndex 0 1, unitIndex 1 0, unitIndex 0 2, unitIndex 2 0] 1 (-1) =
      if i = j then 4 else 0 := by
  intro i j
  by_cases h : i = j
  · simp only [diagonalBasisValue, all_diagonal_basis_coefficients, if_pos h]
    decide
  · simp only [diagonalBasisValue, all_diagonal_basis_coefficients, if_neg h]
    decide

theorem degree_beats_square : 4 + 2 * 2 < (3 : Nat)^2 := by decide

#print axioms all_diagonal_basis_coefficients
#print axioms all_diagonal_basis_values_scalar
#print axioms witness_commutator
#print axioms witness_evaluation
#print axioms degree_beats_square

end CentralPolynomial
