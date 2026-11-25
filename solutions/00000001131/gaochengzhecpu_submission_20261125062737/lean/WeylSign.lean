import Std

namespace C1131

/-- Coefficients in ascending exponent order. Coefficients outside the list are zero. -/
abbrev Polynomial := List Nat

def coefficient (p : Polynomial) (i : Nat) : Nat := p[i]?.getD 0

def addCoefficients : Polynomial → Polynomial → Polynomial
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: addCoefficients p q

/-- Multiply by coefficient convolution: the contribution of the tail is shifted by one. -/
def convolution : Polynomial → Polynomial → Polynomial
  | [], _ => []
  | _, [] => []
  | a :: p, b :: q =>
    addCoefficients ((b :: q).map fun c => a * c) (0 :: convolution p (b :: q))

def factor (d : Nat) : Polynomial := List.replicate d 1

def lengthPolynomial (degrees : List Nat) : Polynomial :=
  degrees.foldl (fun p d => convolution p (factor d)) [1]

/-- The two components count coefficients at even and odd powers, respectively. -/
def signDistribution : Polynomial → Nat × Nat
  | [] => (0, 0)
  | c :: rest =>
    let tail := signDistribution rest
    (c + tail.2, tail.1)

def chiYCoefficient (degrees : List Nat) (i : Nat) : Int :=
  let c : Int := coefficient (lengthPolynomial degrees) i
  if i % 2 = 0 then c else -c

def firstDegrees : List Nat := [2, 2, 2, 2, 4, 6, 6, 6]
def secondDegrees : List Nat := [2, 2, 2, 3, 3, 4, 6, 8]

structure Invariants where
  rank : Nat
  flagDimension : Nat
  groupOrder : Nat
  signCounts : Nat × Nat
  deriving DecidableEq

def invariants (degrees : List Nat) : Invariants :=
  let p := lengthPolynomial degrees
  ⟨degrees.length, (degrees.map fun d => d - 1).sum, p.sum, signDistribution p⟩

def commonInvariants : Invariants := ⟨8, 22, 13824, (6912, 6912)⟩

theorem matching_invariants :
    invariants firstDegrees = commonInvariants ∧ invariants secondDegrees = commonInvariants := by
  decide

theorem different_second_coefficients :
    chiYCoefficient firstDegrees 2 = 32 ∧ chiYCoefficient secondDegrees 2 = 33 := by
  decide

/-- Even a rule given the rank, dimension, and order alongside the signs cannot recover χ_y. -/
theorem no_rule_from_invariants :
    ¬ ∃ rule : Invariants → Nat → Int,
      (∀ i, rule (invariants firstDegrees) i = chiYCoefficient firstDegrees i) ∧
      (∀ i, rule (invariants secondDegrees) i = chiYCoefficient secondDegrees i) := by
  rintro ⟨rule, first, second⟩
  have eqFirst := first 2
  have eqSecond := second 2
  rw [matching_invariants.1, different_second_coefficients.1] at eqFirst
  rw [matching_invariants.2, different_second_coefficients.2] at eqSecond
  have impossible : (32 : Int) = 33 := eqFirst.symm.trans eqSecond
  contradiction

#print axioms matching_invariants
#print axioms different_second_coefficients
#print axioms no_rule_from_invariants

end C1131
