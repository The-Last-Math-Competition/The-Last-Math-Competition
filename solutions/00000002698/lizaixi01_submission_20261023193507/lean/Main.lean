import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Tactic.NormNum

open Function Polynomial Tropical Set
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace TLMC2698

section Translation
variable {K : Type*} [Ring K] [CharZero K]

def translate (x : K) : K := x + 1

theorem translate_iterate (n : ℕ) (x : K) : (translate : K → K)^[n] x = x + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [Function.iterate_succ_apply', translate, ih, Nat.cast_add, add_assoc]

theorem translate_no_periodic : periodicPts (translate : K → K) = ∅ := by
  ext x
  constructor
  · rintro ⟨n, hn, hp⟩
    have he : x + (n : K) = x := by
      simpa only [IsPeriodicPt, IsFixedPt, translate_iterate] using hp
    have hz : (n : K) = 0 := add_left_cancel (he.trans (add_zero x).symm)
    exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) hz
  · simp
end Translation

instance prime_five : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev Q5 := ℚ_[5]
abbrev Value := WithTop ℤ
abbrev TropValue := Tropical Value

def val : Q5 → Value := Padic.addValuation

theorem val_zero : val 0 = ⊤ := by simp [val]
theorem val_one : val 1 = 0 := by simp [val]

/-- The standard coefficientwise tropicalization, including the zero coefficient. -/
def tropicalize (p : Polynomial Q5) : Polynomial TropValue :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff
    (Finsupp.mapRange (fun a => trop (val a)) (by simp [val]) p.toFinsupp.coeff))

theorem tropicalize_coeff (p : Polynomial Q5) (n : ℕ) :
    (tropicalize p).coeff n = trop (val (p.coeff n)) := by
  rfl

theorem tropicalize_X_add_C (c : Q5) :
    tropicalize (X + C c) = (X + C (trop (val c)) : Polynomial TropValue) := by
  ext n
  rw [tropicalize_coeff]
  by_cases h0 : n = 0
  · subst n
    simp [Polynomial.coeff_C]
  by_cases h1 : n = 1
  · subst n
    simp [val]
  · simp [Polynomial.coeff_X, Polynomial.coeff_C, h0, h1, eq_comm, val]

def polynomial : Polynomial Q5 := X + 1
def fieldMap : Q5 → Q5 := polynomial.eval

theorem polynomial_coeff_zero : polynomial.coeff 0 = 1 := by simp [polynomial, Polynomial.coeff_one]
theorem polynomial_coeff_one : polynomial.coeff 1 = 1 := by simp [polynomial, Polynomial.coeff_one]

theorem polynomial_support : polynomial.support = {0, 1} := by
  ext n
  by_cases h0 : n = 0
  · subst n
    simp [Polynomial.mem_support_iff, polynomial, Polynomial.coeff_one]
  by_cases h1 : n = 1
  · subst n
    simp [Polynomial.mem_support_iff, polynomial, Polynomial.coeff_one]
  · simp [Polynomial.mem_support_iff, polynomial, Polynomial.coeff_X, Polynomial.coeff_one,
      h0, h1, eq_comm]

theorem polynomial_nonzero : polynomial ≠ 0 := by
  intro h
  have hc := congrArg (fun q : Polynomial Q5 => q.coeff 1) h
  simp [polynomial_coeff_one] at hc

theorem polynomial_eval (x : Q5) : fieldMap x = x + 1 := by
  simp [fieldMap, polynomial]

theorem fieldMap_eq_translate : fieldMap = translate := by
  funext x
  exact polynomial_eval x

theorem field_iterates (n : ℕ) (x : Q5) : fieldMap^[n] x = x + n := by
  rw [fieldMap_eq_translate, translate_iterate]

theorem field_no_periodic : periodicPts fieldMap = ∅ := by
  rw [fieldMap_eq_translate, translate_no_periodic]

theorem polynomial_derivative : polynomial.derivative = 1 := by
  simp [polynomial]

theorem no_critical_point (x : Q5) : polynomial.derivative.eval x ≠ 0 := by
  rw [polynomial_derivative]
  simp

def inverseMap (x : Q5) : Q5 := x - 1

theorem left_inverse : LeftInverse inverseMap fieldMap := by
  intro x
  simp [inverseMap, polynomial_eval]

theorem right_inverse : RightInverse inverseMap fieldMap := by
  intro x
  simp [inverseMap, polynomial_eval]

def tropicalMap (w : Value) : Value :=
  untrop ((tropicalize polynomial).eval (trop w))

theorem tropical_polynomial : tropicalize polynomial = (X + 1 : Polynomial TropValue) := by
  simpa [polynomial, val] using tropicalize_X_add_C (1 : Q5)

theorem tropicalMap_formula (w : Value) : tropicalMap w = min w 0 := by
  simp [tropicalMap, tropical_polynomial, Tropical.untrop_add]

theorem tropical_fixed_negative : IsFixedPt tropicalMap (-1 : Value) := by
  change tropicalMap (-1) = -1
  rw [tropicalMap_formula, min_eq_left (by decide)]

theorem tropical_periodic_negative : (-1 : Value) ∈ periodicPts tropicalMap :=
  ⟨1, by decide, by simpa only [IsPeriodicPt, Function.iterate_one] using tropical_fixed_negative⟩

theorem val_five : val (5 : Q5) = 1 := by
  rw [val, Padic.addValuation.apply (by norm_num)]
  exact congrArg (fun n : ℤ => (n : Value)) (Padic.valuation_p (p := 5))

theorem val_inverse_five : val ((5 : Q5)⁻¹) = (-1 : Value) := by
  rw [val, AddValuation.map_inv]
  change -val (5 : Q5) = -1
  rw [val_five]

theorem negative_in_value_range : (-1 : Value) ∈ range val :=
  ⟨(5 : Q5)⁻¹, val_inverse_five⟩

theorem val_nat_nonnegative (n : ℕ) : 0 ≤ val (n : Q5) := by
  induction n with
  | zero => simp [val]
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one]
    exact le_trans (le_min ih (by simp)) (Padic.addValuation.map_add _ _)

/-- Composition is formed in the actual polynomial ring before tropicalizing. -/
def iteratedPolynomial (n : ℕ) : Polynomial Q5 :=
  (fun p : Polynomial Q5 => polynomial.comp p)^[n] X

theorem iteratedPolynomial_formula (n : ℕ) :
    iteratedPolynomial n = X + C (n : Q5) := by
  induction n with
  | zero => simp [iteratedPolynomial]
  | succ n ih =>
    have hs : iteratedPolynomial (n + 1) = polynomial.comp (iteratedPolynomial n) := by
      exact Function.iterate_succ_apply' _ _ _
    rw [hs, ih]
    simp [polynomial, Polynomial.add_comp, Nat.cast_add, Nat.cast_one, add_assoc]

theorem iteratedPolynomial_eval (n : ℕ) (x : Q5) :
    (iteratedPolynomial n).eval x = fieldMap^[n] x := by
  rw [iteratedPolynomial_formula, field_iterates]
  simp

theorem positive_iteratedPolynomial_support (n : ℕ) (hn : 0 < n) :
    (iteratedPolynomial n).support = {0, 1} := by
  rw [iteratedPolynomial_formula]
  ext k
  by_cases h0 : k = 0
  · subst k
    simp [Polynomial.mem_support_iff, Nat.ne_of_gt hn]
  by_cases h1 : k = 1
  · subst k
    simp [Polynomial.mem_support_iff]
  · simp [Polynomial.mem_support_iff, Polynomial.coeff_X,
      h0, h1, eq_comm]

theorem iteratedPolynomial_derivative (n : ℕ) :
    (iteratedPolynomial n).derivative = 1 := by
  rw [iteratedPolynomial_formula]
  simp

def tropicalIteratedMap (n : ℕ) (w : Value) : Value :=
  untrop ((tropicalize (iteratedPolynomial n)).eval (trop w))

theorem tropicalIteratedMap_formula (n : ℕ) (w : Value) :
    tropicalIteratedMap n w = min w (val (n : Q5)) := by
  unfold tropicalIteratedMap
  rw [iteratedPolynomial_formula, tropicalize_X_add_C]
  simp [Tropical.untrop_add]

theorem all_tropical_iterates_fix_negative (n : ℕ) :
    IsFixedPt (tropicalIteratedMap n) (-1 : Value) := by
  change tropicalIteratedMap n (-1) = -1
  rw [tropicalIteratedMap_formula, min_eq_left]
  exact le_trans (by decide) (val_nat_nonnegative n)

theorem positive_field_iterate_no_periodic (n : ℕ) (hn : 0 < n) :
    periodicPts (fieldMap^[n]) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  rcases hx with ⟨k, hk, hp⟩
  have hper : x ∈ periodicPts fieldMap := by
    refine ⟨n * k, Nat.mul_pos hn hk, ?_⟩
    simpa only [IsPeriodicPt, Function.iterate_mul] using hp
  simp [field_no_periodic] at hper

theorem strict_branch_no_cancellation (x : Q5) (hx : val x = (-1 : Value)) (n : ℕ) :
    val (fieldMap^[n] x) = val x := by
  rw [field_iterates]
  apply AddValuation.map_add_eq_of_lt_left
  change val x < val (n : Q5)
  rw [hx]
  exact lt_of_lt_of_le (by decide) (val_nat_nonnegative n)

theorem valuation_of_classical_periodic_empty : val '' periodicPts fieldMap = ∅ := by
  rw [field_no_periodic, image_empty]

theorem periodic_correspondence_false :
    periodicPts tropicalMap ≠ val '' periodicPts fieldMap := by
  rw [valuation_of_classical_periodic_empty]
  exact Set.nonempty_iff_ne_empty.mp ⟨-1, tropical_periodic_negative⟩

theorem all_positive_iterate_correspondences_false (n : ℕ) (hn : 0 < n) :
    periodicPts (tropicalIteratedMap n) ≠ val '' periodicPts (fieldMap^[n]) := by
  rw [positive_field_iterate_no_periodic n hn, image_empty]
  apply Set.nonempty_iff_ne_empty.mp
  refine ⟨-1, 1, by decide, ?_⟩
  simpa only [IsPeriodicPt, Function.iterate_one] using all_tropical_iterates_fix_negative n

theorem concrete_counterexample :
    (-1 : Value) ∈ range val ∧ IsFixedPt tropicalMap (-1 : Value) ∧
    periodicPts fieldMap = ∅ ∧
    (∀ x : Q5, polynomial.derivative.eval x ≠ 0) ∧
    periodicPts tropicalMap ≠ val '' periodicPts fieldMap :=
  ⟨negative_in_value_range, tropical_fixed_negative, field_no_periodic,
    no_critical_point, periodic_correspondence_false⟩

end TLMC2698
