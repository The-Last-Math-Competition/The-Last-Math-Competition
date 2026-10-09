import Std
import Init.Data.Rat.Basic

/-!
# Counterexample to conjecture 00000000564

All computations use core Lean 4, with no Mathlib dependency.  The coefficient
variables are evaluated in the natural numbers.  A polynomial function is
enough here: the first mutation is constructed explicitly from monomials,
products and a sum, and its equality to `1 + y_1` is proved for EVERY assignment.

The final theorem refutes the A2 restriction of the conjecture.  The theorem
`refutesEveryClaimCoveringA2` makes the semantic bridge explicit: any global
claim implying this required A2 instance is false.
-/

namespace Conjecture564

abbrev Matrix (m n : Nat) := Fin m → Fin n → Int
abbrev Assignment (n : Nat) := Fin n → Nat
abbrev PolynomialFunction (n : Nat) := Assignment n → Nat

/-- The mutable block and coefficient block of an extended exchange matrix. -/
structure ExtendedExchange (n : Nat) where
  mutable : Matrix n n
  coefficient : Matrix n n

/-- Stack the two blocks, with coefficient rows below mutable rows. -/
def ExtendedExchange.stacked {n : Nat} (E : ExtendedExchange n) : Matrix (n + n) n :=
  fun i j =>
    if hi : i.val < n then E.mutable ⟨i.val, hi⟩ j
    else E.coefficient ⟨i.val - n, by omega⟩ j

/-- Principal coefficients mean the bottom block is the identity matrix. -/
def principalExtension {n : Nat} (B : Matrix n n) : ExtendedExchange n where
  mutable := B
  coefficient := fun i j => if i = j then 1 else 0

/-- Positive and negative exponent parts; these are natural numbers. -/
def positivePart (a : Int) : Nat := a.toNat
def negativePart (a : Int) : Nat := (-a).toNat

/-- A product over all indices, including the empty product at rank zero. -/
def finiteProduct {n : Nat} (f : Fin n → Nat) : Nat :=
  (List.finRange n).foldr (fun i acc => f i * acc) 1

/-- Every initial F-polynomial is the constant polynomial 1. -/
def initialF {n : Nat} (_i : Fin n) : PolynomialFunction n := fun _y => 1

/--
The numerator in the F-polynomial mutation recurrence.  The first term uses
the positive entries of the extended exchange column, and the second uses
its negative entries.  Both mutable F factors and coefficient y factors are
present, rather than building in the answer `1 + y_k`.
-/
def mutationNumerator {n : Nat} (E : ExtendedExchange n)
    (F : Fin n → PolynomialFunction n) (k : Fin n) : PolynomialFunction n :=
  fun y =>
    finiteProduct (fun i => y i ^ positivePart (E.coefficient i k)) *
      finiteProduct (fun i => F i y ^ positivePart (E.mutable i k)) +
    finiteProduct (fun i => y i ^ negativePart (E.coefficient i k)) *
      finiteProduct (fun i => F i y ^ negativePart (E.mutable i k))

/--
For the first mutation, the recurrence divisor is `initialF k = 1`.
The numerator therefore is exactly the resulting F-polynomial.
-/
def firstMutationF {n : Nat} (E : ExtendedExchange n) (k : Fin n) :
    PolynomialFunction n := mutationNumerator E initialF k

/-- One orientation of the rank-two type-A2 exchange matrix. -/
def a2Exchange : Matrix 2 2 := fun i j =>
  if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then -1 else 0

/-- The standard type-A2 Cartan matrix. -/
def a2Cartan : Matrix 2 2 := fun i j => if i = j then 2 else -1

/-- The Cartan companion of an exchange matrix. -/
def cartanCompanion {n : Nat} (B : Matrix n n) : Matrix n n :=
  fun i j => if i = j then 2 else -(Int.ofNat (B i j).natAbs)

/-- In rank two, these entries are the standard type-A2 Cartan diagram. -/
def IsTypeA2 (B : Matrix 2 2) : Prop :=
  (∀ i j, B i j = -B j i) ∧ (∀ i j, cartanCompanion B i j = a2Cartan i j)

theorem a2Exchange_isTypeA2 : IsTypeA2 a2Exchange := by
  unfold IsTypeA2
  decide

theorem a2Cartan_determinant :
    a2Cartan 0 0 * a2Cartan 1 1 - a2Cartan 0 1 * a2Cartan 1 0 = 3 := by decide

/-- The Cartan companion has positive leading principal minors, 2 and 3. -/
theorem a2Cartan_positive_principal_minors :
    a2Cartan 0 0 > 0 ∧
      a2Cartan 0 0 * a2Cartan 1 1 - a2Cartan 0 1 * a2Cartan 1 0 > 0 := by decide

/-- Multiplication and identity for the concrete two-dimensional root basis. -/
def matrixMul2 (A B : Matrix 2 2) : Matrix 2 2 :=
  fun i j => A i 0 * B 0 j + A i 1 * B 1 j

def identity2 : Matrix 2 2 := fun i j => if i = j then 1 else 0

/--
The simple reflection derived from the Cartan matrix, acting on coordinates
in the simple-root basis: only row k differs from the identity.
-/
def simpleReflection2 (A : Matrix 2 2) (k : Fin 2) : Matrix 2 2 :=
  fun i j => if i = k then identity2 i j - A k j else identity2 i j

def a2CoxeterElement : Matrix 2 2 :=
  matrixMul2 (simpleReflection2 a2Cartan 0) (simpleReflection2 a2Cartan 1)

theorem a2_simple_reflections_are_involutions :
    (∀ i j, matrixMul2 (simpleReflection2 a2Cartan 0)
      (simpleReflection2 a2Cartan 0) i j = identity2 i j) ∧
    (∀ i j, matrixMul2 (simpleReflection2 a2Cartan 1)
      (simpleReflection2 a2Cartan 1) i j = identity2 i j) := by decide

/-- Its cube is I; its first and second powers are not I, so its order is 3. -/
theorem a2_coxeter_order_three :
    (∀ i j, matrixMul2 (matrixMul2 a2CoxeterElement a2CoxeterElement)
      a2CoxeterElement i j = identity2 i j) ∧
    a2CoxeterElement 0 0 ≠ identity2 0 0 ∧
    matrixMul2 a2CoxeterElement a2CoxeterElement 0 0 ≠ identity2 0 0 := by decide

/-- Constant, linear, quadratic coefficients of det(t I - C). -/
def characteristicCoefficients2 (C : Matrix 2 2) : List Int :=
  [C 0 0 * C 1 1 - C 0 1 * C 1 0, -(C 0 0 + C 1 1), 1]

theorem a2_coxeter_characteristic :
    characteristicCoefficients2 a2CoxeterElement = [1, 1, 1] := by decide

/-- Coefficient-list addition and multiplication for the cyclotomic check. -/
def addCoefficients : List Int → List Int → List Int
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs => (a + b) :: addCoefficients as bs

def multiplyCoefficients : List Int → List Int → List Int
  | [], _ => []
  | a :: as, b => addCoefficients (b.map (fun x => a * x))
      (0 :: multiplyCoefficients as b)

/-- (t - 1)(t^2 + t + 1) = t^3 - 1, checked coefficient by coefficient. -/
theorem a2_coxeter_cyclotomic_factorization :
    multiplyCoefficients [-1, 1] (characteristicCoefficients2 a2CoxeterElement) =
      [-1, 0, 0, 1] := by decide

/-- Check all eight entries of the actual 4-by-2 principal extension. -/
theorem a2_principal_extended_entries :
    (∀ j, (principalExtension a2Exchange).stacked 0 j = a2Exchange 0 j) ∧
    (∀ j, (principalExtension a2Exchange).stacked 1 j = a2Exchange 1 j) ∧
    (∀ j, (principalExtension a2Exchange).stacked 2 j = if j = 0 then 1 else 0) ∧
    (∀ j, (principalExtension a2Exchange).stacked 3 j = if j = 1 then 1 else 0) := by
  decide

/-- First mutation at vertex 1 gives the polynomial `1 + y_1`. -/
theorem a2_first_mutation_polynomial :
    firstMutationF (principalExtension a2Exchange) 0 = (fun y => 1 + y 0) := by
  funext y
  simp [firstMutationF, mutationNumerator, finiteProduct, initialF,
    principalExtension, a2Exchange, positivePart, negativePart,
    List.finRange_succ, Nat.add_comm]

def allOnes {n : Nat} : Assignment n := fun _ => 1

theorem a2_first_mutation_at_one :
    firstMutationF (principalExtension a2Exchange) 0 allOnes = 2 := by
  rw [a2_first_mutation_polynomial]
  rfl

/--
The generalized Catalan product for Coxeter number h and exponents e_i.
Rat division is exact; this does not use truncated natural-number division.
-/
def generalizedCatalan (h : Nat) (exponents : List Nat) : Rat :=
  (exponents.map (fun e => ((h + e + 1 : Nat) : Rat) / ((e + 1 : Nat) : Rat))).foldr
    (fun factor acc => factor * acc) 1

/--
Standard type-A2 data. The Coxeter matrix above has order 3 and characteristic
polynomial t^2+t+1, so its eigenvalues are the two nontrivial cube roots of
unity, indexed by exponents 1 and 2.
-/
def a2CoxeterNumber : Nat := 3
def a2Exponents : List Nat := [1, 2]

theorem a2_generalizedCatalan : generalizedCatalan a2CoxeterNumber a2Exponents = 5 := by
  decide +kernel

/-- The two nonintegral/integral factors are 5/2 and 2. -/
theorem a2_catalan_factors :
    (((a2CoxeterNumber + 1 + 1 : Nat) : Rat) / ((1 + 1 : Nat) : Rat) = (5 : Rat) / 2) ∧
    (((a2CoxeterNumber + 2 + 1 : Nat) : Rat) / ((2 + 1 : Nat) : Rat) = 2) := by
  decide +kernel

theorem two_not_dvd_five : ¬ (2 ∣ 5) := by decide

/-- The complete counterexample certificate, including its semantic input data. -/
theorem a2_counterexample :
    IsTypeA2 a2Exchange ∧
    firstMutationF (principalExtension a2Exchange) 0 allOnes = 2 ∧
    generalizedCatalan a2CoxeterNumber a2Exponents = 5 ∧
    ¬ (firstMutationF (principalExtension a2Exchange) 0 allOnes ∣ 5) := by
  refine ⟨a2Exchange_isTypeA2, a2_first_mutation_at_one, a2_generalizedCatalan, ?_⟩
  rw [a2_first_mutation_at_one]
  exact two_not_dvd_five

/--
The mandatory A2 instance of the conjecture: for every standard A2 exchange
matrix and every first-mutated variable, the F-value must divide the integer
equal to the generalized Catalan product.  Representing that integer by an
existential also proves it agrees exactly with the rational product.
-/
def A2DivisibilityClaim : Prop :=
  ∀ (B : Matrix 2 2), IsTypeA2 B → ∀ (k : Fin 2),
    ∃ c : Nat,
      (c : Rat) = generalizedCatalan a2CoxeterNumber a2Exponents ∧
      firstMutationF (principalExtension B) k allOnes ∣ c

theorem not_A2DivisibilityClaim : ¬ A2DivisibilityClaim := by
  intro h
  obtain ⟨c, hc, hdvd⟩ := h a2Exchange a2Exchange_isTypeA2 0
  rw [a2_generalizedCatalan] at hc
  have hc5 : c = 5 := by
    have hn := congrArg Rat.num hc
    exact Int.ofNat.inj hn
  rw [a2_first_mutation_at_one, hc5] at hdvd
  exact two_not_dvd_five hdvd

/--
Semantic bridge: the conjecture quantifies over all its legitimate F
polynomials, hence must imply this A2 restriction.  This theorem refutes any
formulation that includes that necessary instance, without axiomatizing any
unformalized cluster algebra results.
-/
theorem refutesEveryClaimCoveringA2 (GlobalClaim : Prop)
    (containsA2 : GlobalClaim → A2DivisibilityClaim) : ¬ GlobalClaim := by
  intro h
  exact not_A2DivisibilityClaim (containsA2 h)

end Conjecture564

#print axioms Conjecture564.a2_first_mutation_polynomial
#print axioms Conjecture564.a2_coxeter_order_three
#print axioms Conjecture564.a2_coxeter_characteristic
#print axioms Conjecture564.a2_generalizedCatalan
#print axioms Conjecture564.a2_counterexample
#print axioms Conjecture564.not_A2DivisibilityClaim
#print axioms Conjecture564.refutesEveryClaimCoveringA2
