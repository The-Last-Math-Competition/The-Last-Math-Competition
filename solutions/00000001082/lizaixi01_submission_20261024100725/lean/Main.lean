import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! The standard extension-field-linear MRD count at (m,n,k)=(3,2,2).
The code universe is the full class of actual two-dimensional subspaces,
with genuine coordinate-span rank distance and Singleton cardinality equality.
No Gabidulin-only classification or nontrivial-parameter count is claimed. -/

noncomputable section
open Module Filter Asymptotics
open scoped Topology

namespace TLMC1082

variable (p : ℕ) [Fact p.Prime]

abbrev Base := ZMod p
abbrev Extension := GaloisField p 3
abbrev Word := Fin 2 → Extension p

theorem extension_degree : finrank (Base p) (Extension p) = 3 :=
  GaloisField.finrank p (by decide)

theorem extension_card : Nat.card (Extension p) = p ^ 3 :=
  GaloisField.card p 3 (by decide)

theorem word_dimension : finrank (Extension p) (Word p) = 2 := by
  simp [Word]

/-- The actual base-field span of the two coordinates. -/
def coordinateSpan (v : Word p) : Submodule (Base p) (Extension p) :=
  Submodule.span (Base p) (Set.range v)

def rankWeight (v : Word p) : ℕ := finrank (Base p) (coordinateSpan p v)

def rankDistance (x y : Word p) : ℕ := rankWeight p (x - y)

theorem rankWeight_zero_iff (v : Word p) : rankWeight p v = 0 ↔ v = 0 := by
  change finrank (Base p) (coordinateSpan p v) = 0 ↔ v = 0
  rw [Submodule.finrank_eq_zero]
  constructor
  · intro h
    funext i
    have hi : v i ∈ coordinateSpan p v := Submodule.subset_span ⟨i, rfl⟩
    rw [h] at hi
    simpa using hi
  · intro h
    subst v
    simp [coordinateSpan]

theorem positive_rankWeight {v : Word p} (hv : v ≠ 0) : 1 ≤ rankWeight p v :=
  Nat.one_le_iff_ne_zero.mpr (fun h => hv ((rankWeight_zero_iff p v).mp h))

def unitWord : Word p := fun i => if i = 0 then 1 else 0

theorem unitWord_ne_zero : unitWord p ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [unitWord] at this

theorem coordinateSpan_unit : coordinateSpan p (unitWord p) =
    Submodule.span (Base p) ({1} : Set (Extension p)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    by_cases hi : i = 0
    · simp [unitWord, hi]
    · simp [unitWord, hi]
  · apply Submodule.span_mono
    intro x hx
    have hx1 : x = 1 := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨0, by simp [unitWord]⟩

theorem rankWeight_unit : rankWeight p (unitWord p) = 1 := by
  rw [rankWeight, coordinateSpan_unit]
  exact finrank_span_singleton (one_ne_zero : (1 : Extension p) ≠ 0)

/-- All actual distances between distinct codewords. -/
def distanceValues (C : Submodule (Extension p) (Word p)) : Set ℕ :=
  {d | ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ rankDistance p x y = d}

def minimumDistance (C : Submodule (Extension p) (Word p)) : ℕ :=
  sInf (distanceValues p C)

theorem one_mem_top_distances : 1 ∈ distanceValues p ⊤ := by
  refine ⟨unitWord p, Submodule.mem_top, 0, Submodule.mem_top,
    unitWord_ne_zero p, ?_⟩
  simpa [rankDistance] using rankWeight_unit p

theorem full_minimumDistance : minimumDistance p ⊤ = 1 := by
  apply le_antisymm
  · exact csInf_le (OrderBot.bddBelow _) (one_mem_top_distances p)
  · apply le_csInf ⟨1, one_mem_top_distances p⟩
    rintro d ⟨x, _, y, _, hxy, hd⟩
    rw [← hd]
    exact positive_rankWeight p (sub_ne_zero.mpr hxy)

theorem full_distance_attained : minimumDistance p ⊤ ∈ distanceValues p ⊤ := by
  rw [full_minimumDistance]
  exact one_mem_top_distances p

theorem code_card_formula (C : Submodule (Extension p) (Word p)) :
    Nat.card C = p ^ (3 * finrank (Extension p) C) := by
  rw [Module.natCard_eq_pow_finrank (K := Extension p), extension_card, ← pow_mul]

theorem full_card : Nat.card (⊤ : Submodule (Extension p) (Word p)) = p ^ 6 := by
  rw [code_card_formula, finrank_top, word_dimension]

/-- The genuine rank-metric Singleton equality, with m=3 and n=2. -/
def IsMRD (C : Submodule (Extension p) (Word p)) : Prop :=
  Nat.card C = p ^ (3 * (2 - minimumDistance p C + 1))

theorem full_isMRD : IsMRD p ⊤ := by
  rw [IsMRD, full_minimumDistance, full_card]

/-- All actual extension-field-linear [2,2] MRD codes, not a list of examples. -/
def Code := {C : Submodule (Extension p) (Word p) //
  finrank (Extension p) C = 2 ∧ IsMRD p C}

def fullCode : Code p := ⟨⊤, by simp, full_isMRD p⟩

theorem code_eq_top (C : Code p) : C.val = ⊤ :=
  Submodule.eq_top_of_finrank_eq (C.property.1.trans (word_dimension p).symm)

instance code_subsingleton : Subsingleton (Code p) where
  allEq C D := Subtype.ext ((code_eq_top p C).trans (code_eq_top p D).symm)

instance code_unique : Unique (Code p) where
  default := fullCode p
  uniq _ := Subsingleton.elim _ _

theorem code_minimumDistance (C : Code p) : minimumDistance p C.val = 1 := by
  rw [code_eq_top, full_minimumDistance]

theorem code_distance_values_nonempty (C : Code p) : (distanceValues p C.val).Nonempty := by
  rw [code_eq_top]
  exact ⟨1, one_mem_top_distances p⟩

theorem code_distance_attained (C : Code p) :
    minimumDistance p C.val ∈ distanceValues p C.val := by
  rw [code_eq_top]
  exact full_distance_attained p

/-- Morrison DefinitionIII.4: ambient extension-field-linear equivalences
preserving actual rank weight and mapping the entire code onto the other. -/
def RankEquivalent (C D : Code p) : Prop :=
  ∃ e : Word p ≃ₗ[Extension p] Word p,
    (∀ v, rankWeight p (e v) = rankWeight p v) ∧
    e '' (C.val : Set (Word p)) = (D.val : Set (Word p))

theorem rankEquivalent_refl (C : Code p) : RankEquivalent p C C := by
  refine ⟨LinearEquiv.refl _ _, fun _ => rfl, ?_⟩
  change id '' (C.val : Set (Word p)) = (C.val : Set (Word p))
  simp

theorem rankEquivalent_symm {C D : Code p} (h : RankEquivalent p C D) :
    RankEquivalent p D C := by
  obtain ⟨e, he, hCD⟩ := h
  refine ⟨e.symm, ?_, ?_⟩
  · intro v
    simpa using (he (e.symm v)).symm
  · rw [← hCD, Set.image_image]
    simp

theorem rankEquivalent_trans {C D E : Code p}
    (h : RankEquivalent p C D) (h' : RankEquivalent p D E) :
    RankEquivalent p C E := by
  obtain ⟨e, he, hCD⟩ := h
  obtain ⟨f, hf, hDE⟩ := h'
  refine ⟨e.trans f, ?_, ?_⟩
  · intro v
    exact (hf (e v)).trans (he v)
  · rw [← hDE, ← hCD, Set.image_image]
    rfl

def rankSetoid : Setoid (Code p) where
  r := RankEquivalent p
  iseqv := ⟨rankEquivalent_refl p, rankEquivalent_symm p, rankEquivalent_trans p⟩

def Classes := Quotient (rankSetoid p)

instance classes_subsingleton : Subsingleton (Classes p) where
  allEq a b := Quotient.inductionOn₂ a b fun C D => by
    have h : C = D := Subsingleton.elim _ _
    subst D
    rfl

instance classes_unique : Unique (Classes p) where
  default := Quotient.mk (rankSetoid p) (fullCode p)
  uniq _ := Subsingleton.elim _ _

def classCount : ℕ := Nat.card (Classes p)

theorem classCount_one : classCount p = 1 := by
  simp [classCount]

theorem actual_parameters :
    finrank (Base p) (Extension p) = 3 ∧
    finrank (Extension p) (Word p) = 2 ∧
    finrank (Extension p) (fullCode p).val = 2 ∧
    minimumDistance p (fullCode p).val = 1 ∧
    Nat.card (fullCode p).val = p ^ 6 ∧
    classCount p = 1 := by
  exact ⟨extension_degree p, word_dimension p, (fullCode p).property.1,
    code_minimumDistance p _, full_card p, classCount_one p⟩

end TLMC1082

namespace TLMC1082

abbrev PrimeIndex := {p : ℕ // p.Prime}

instance primeIndex_nonempty : Nonempty PrimeIndex := ⟨⟨2, by decide⟩⟩

def primeCount (q : PrimeIndex) : ℝ :=
  letI : Fact q.val.Prime := ⟨q.property⟩
  (classCount q.val : ℝ)

theorem primeCount_one (q : PrimeIndex) : primeCount q = 1 := by
  let : Fact q.val.Prime := ⟨q.property⟩
  simp [primeCount, classCount_one]

/-- The printed exponent, evaluated at the actual parameters n=k=2. -/
def predictedMainTerm (q : PrimeIndex) : ℝ :=
  (q.val : ℝ) ^ ((2 - 1) * (2 - 2 + 1) : ℕ)

theorem predictedMainTerm_eq (q : PrimeIndex) : predictedMainTerm q = (q.val : ℝ) := by
  norm_num [predictedMainTerm]

def relativeError (q : PrimeIndex) : ℝ :=
  primeCount q / predictedMainTerm q - 1

theorem relativeError_eq (q : PrimeIndex) : relativeError q = 1 / (q.val : ℝ) - 1 := by
  rw [relativeError, primeCount_one, predictedMainTerm_eq]

theorem relativeError_abs (q : PrimeIndex) :
    |relativeError q| = ((q.val : ℝ) - 1) / q.val := by
  have hpos : 0 < (q.val : ℝ) := by exact_mod_cast q.property.pos
  have hgt : (1 : ℝ) < q.val := by exact_mod_cast q.property.one_lt
  have hsmall : 1 / (q.val : ℝ) < 1 := (div_lt_one hpos).mpr hgt
  rw [relativeError_eq, abs_of_neg (sub_neg.mpr hsmall)]
  field_simp
  ring

/-- Every proposed constant and every cutoff fail at an actual larger prime. -/
theorem arbitrarily_large_prime_failure (C : ℝ) (N : ℕ) :
    ∃ q : PrimeIndex, N ≤ q.val ∧
      C * ‖(q.val : ℝ)⁻¹‖ < ‖relativeError q‖ := by
  obtain ⟨B, hB⟩ := exists_nat_gt (max (N : ℝ) (C + 1))
  obtain ⟨p, hBp, hp⟩ := Nat.exists_infinite_primes B
  have hBpR : (B : ℝ) ≤ p := by exact_mod_cast hBp
  have hN : (N : ℝ) < p := lt_of_le_of_lt (le_max_left _ _) (hB.trans_le hBpR)
  have hC : C + 1 < (p : ℝ) := lt_of_le_of_lt (le_max_right _ _) (hB.trans_le hBpR)
  let q : PrimeIndex := ⟨p, hp⟩
  have hpos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  refine ⟨q, by exact_mod_cast hN.le, ?_⟩
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), ← div_eq_mul_inv,
    Real.norm_eq_abs, relativeError_abs]
  exact (div_lt_div_iff_of_pos_right hpos).mpr (by dsimp [q]; linarith)

theorem relativeError_not_bigO :
    ¬ relativeError =O[atTop] (fun q : PrimeIndex => (q.val : ℝ)⁻¹) := by
  intro h
  obtain ⟨C, hC⟩ := isBigO_iff.mp h
  obtain ⟨q₀, hq₀⟩ := eventually_atTop.mp hC
  obtain ⟨q, hq, hfail⟩ := arbitrarily_large_prime_failure C q₀.val
  exact (not_lt_of_ge (hq₀ q hq)) hfail

/-- This is precisely the multiplicative 1+O(1/q) formulation, not only
a discrepancy at one finite field. -/
theorem printed_asymptotic_false :
    ¬ ∃ error : PrimeIndex → ℝ,
      error =O[atTop] (fun q : PrimeIndex => (q.val : ℝ)⁻¹) ∧
      ∀ᶠ q in atTop, primeCount q = predictedMainTerm q * (1 + error q) := by
  rintro ⟨error, hO, heq⟩
  apply relativeError_not_bigO
  apply hO.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [heq] with q hq
  have hne : predictedMainTerm q ≠ 0 := by
    rw [predictedMainTerm_eq]
    exact_mod_cast q.property.ne_zero
  rw [relativeError, hq]
  field_simp
  ring

theorem complete_counterexample :
    (∀ q : PrimeIndex, primeCount q = 1) ∧
    (∀ C : ℝ, ∀ N : ℕ, ∃ q : PrimeIndex, N ≤ q.val ∧
      C * ‖(q.val : ℝ)⁻¹‖ < ‖relativeError q‖) ∧
    (¬ relativeError =O[atTop] (fun q : PrimeIndex => (q.val : ℝ)⁻¹)) ∧
    (¬ ∃ error : PrimeIndex → ℝ,
      error =O[atTop] (fun q : PrimeIndex => (q.val : ℝ)⁻¹) ∧
      ∀ᶠ q in atTop, primeCount q = predictedMainTerm q * (1 + error q)) :=
  ⟨primeCount_one, arbitrarily_large_prime_failure,
    relativeError_not_bigO, printed_asymptotic_false⟩

end TLMC1082
