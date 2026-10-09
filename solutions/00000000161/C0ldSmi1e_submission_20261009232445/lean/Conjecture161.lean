import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic
import Conjecture161.Arithmetic

/-!
# Conjecture 00000000161

The sample space is the actual general linear group over the prime field.
The probability is cardinality of the stated event divided by sample-space
cardinality, namely the uniform distribution on this finite group.
-/

namespace Conjecture161

abbrev PrimeIndex := {p : ℕ // p.Prime}

instance primeIndexInhabited : Inhabited PrimeIndex := ⟨⟨2, Nat.prime_two⟩⟩

open Filter Topology

abbrev GeneralLinear (n : ℕ) (p : PrimeIndex) :=
  Matrix.GeneralLinearGroup (Fin n) (ZMod (p : ℕ))

/-- The exact event in the conjecture for a positive denominator `C`. -/
def LargePrimeFactor (n : ℕ) (C : ℝ) (p : PrimeIndex)
    (A : GeneralLinear n p) : Prop :=
  ∃ r : ℕ, r.Prime ∧ r ∣ orderOf A ∧ (p : ℝ) ^ (n - 1) / C < (r : ℝ)

/-- Uniform probability of the event, as a real number. -/
noncomputable def successProbability (n : ℕ) (C : ℝ) (p : PrimeIndex) : ℝ :=
  (Nat.card {A : GeneralLinear n p // LargePrimeFactor n C p A} : ℝ) /
    (Nat.card (GeneralLinear n p) : ℝ)

/-- A precise existential-polynomial reading of the source's `poly(n)`. -/
def OriginalClaim : Prop :=
  ∃ P : Polynomial ℝ,
    (∀ n : ℕ, 2 ≤ n → 0 < P.eval (n : ℝ)) ∧
    ∀ n : ℕ, 2 ≤ n →
      Tendsto (successProbability n (P.eval (n : ℝ))) atTop (𝓝 1)

/-- Primes tend to infinity under their usual order.  This explicitly uses
Euclid's theorem, so the prime-indexed limiting assertion is not vacuous. -/
theorem primes_tendsto_nat_atTop :
    Tendsto (fun p : PrimeIndex => (p : ℕ)) atTop atTop := by
  refine tendsto_atTop.2 fun N => ?_
  obtain ⟨q, hNq, hq⟩ := Nat.exists_infinite_primes N
  exact (eventually_ge_atTop (⟨q, hq⟩ : PrimeIndex)).mono
    fun _ hp => hNq.trans hp

/-- The index filter is nontrivial, as required for uniqueness of real limits. -/
theorem prime_index_neBot : NeBot (atTop : Filter PrimeIndex) := inferInstance

/-- The sample space is finite and nonempty. -/
theorem sampleSpace_card_pos (n : ℕ) (p : PrimeIndex) :
    0 < Nat.card (GeneralLinear n p) := by
  letI : Fact (Nat.Prime (p : ℕ)) := ⟨p.property⟩
  exact Nat.card_pos

/-- The counting formula is a probability: it belongs to the unit interval. -/
theorem successProbability_mem_Icc (n : ℕ) (C : ℝ) (p : PrimeIndex) :
    successProbability n C p ∈ Set.Icc (0 : ℝ) 1 := by
  letI : Fact (Nat.Prime (p : ℕ)) := ⟨p.property⟩
  have hden : (0 : ℝ) < Nat.card (GeneralLinear n p) := by
    exact_mod_cast sampleSpace_card_pos n p
  have hcard := Nat.card_le_card_of_injective
    (fun A : {A : GeneralLinear n p // LargePrimeFactor n C p A} => A.val)
    Subtype.val_injective
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hden.le
  · apply (div_le_one hden).2
    exact_mod_cast hcard

/-- Lagrange's theorem and the actual cardinality of the matrix group turn
the arithmetic bound into a bound on every prime divisor of every order. -/
theorem prime_divisor_order_le (p : PrimeIndex) (A : GeneralLinear 4 p)
    {r : ℕ} (hr : r.Prime) (hdvd : r ∣ orderOf A) :
    r ≤ (p : ℕ) ^ 2 + (p : ℕ) + 1 := by
  letI : Fact (Nat.Prime (p : ℕ)) := ⟨p.property⟩
  apply prime_le_of_dvd_gl4_card_product p.property.two_le hr
  have h := hdvd.trans (orderOf_dvd_natCard A)
  rw [Matrix.card_GL_field, ZMod.card] at h
  exact h

/-- An explicit sufficient size condition for the threshold to dominate
the universal prime-divisor bound. -/
theorem threshold_dominates {C x : ℝ} (hC : 0 < C) (hx : 1 ≤ x)
    (hCx : 3 * C ≤ x) : x ^ 2 + x + 1 ≤ x ^ 3 / C := by
  apply (le_div_iff₀ hC).2
  have hsmall : x ^ 2 + x + 1 ≤ 3 * x ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hsmall hC.le
  have hlarge := mul_le_mul_of_nonneg_right hCx (sq_nonneg x)
  nlinarith

/-- Once `p ≥ 3C`, no element of `GL₄(Fₚ)` belongs to the source event. -/
theorem no_largePrimeFactor_four {C : ℝ} (hC : 0 < C) (p : PrimeIndex)
    (hp : 3 * C ≤ (p : ℝ)) (A : GeneralLinear 4 p) :
    ¬ LargePrimeFactor 4 C p A := by
  rintro ⟨r, hr, hdvd, hlarge⟩
  have hbound := prime_divisor_order_le p A hr hdvd
  have hboundReal : (r : ℝ) ≤ (p : ℝ) ^ 2 + (p : ℝ) + 1 := by
    exact_mod_cast hbound
  have hpOne : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.one_lt.le
  have hthreshold := threshold_dominates hC hpOne hp
  norm_num only at hlarge
  exact (not_lt_of_ge (hboundReal.trans hthreshold)) hlarge

/-- The uniform probability is exactly zero under the same explicit bound. -/
theorem successProbability_four_eq_zero {C : ℝ} (hC : 0 < C) (p : PrimeIndex)
    (hp : 3 * C ≤ (p : ℝ)) : successProbability 4 C p = 0 := by
  letI : IsEmpty {A : GeneralLinear 4 p // LargePrimeFactor 4 C p A} :=
    ⟨fun A => no_largePrimeFactor_four hC p hp A.val A.property⟩
  simp [successProbability]

/-- For each fixed positive denominator, the probability is eventually zero
as the prime tends to infinity. -/
theorem successProbability_four_eventually_zero {C : ℝ} (hC : 0 < C) :
    ∀ᶠ p : PrimeIndex in atTop, successProbability 4 C p = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_ge (3 * C)
  filter_upwards [primes_tendsto_nat_atTop.eventually (eventually_ge_atTop N)] with p hp
  apply successProbability_four_eq_zero hC p
  exact hN.trans (by exact_mod_cast hp)

/-- The probability tends to zero, for every possible positive constant
value of `poly(4)`. -/
theorem successProbability_four_tendsto_zero {C : ℝ} (hC : 0 < C) :
    Tendsto (successProbability 4 C) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  exact (successProbability_four_eventually_zero hC).mono fun _ hp => hp.symm

/-- Consequently it cannot tend to one on the nontrivial prime filter. -/
theorem successProbability_four_not_tendsto_one {C : ℝ} (hC : 0 < C) :
    ¬ Tendsto (successProbability 4 C) atTop (𝓝 1) := by
  intro h
  have h01 : (0 : ℝ) = 1 :=
    tendsto_nhds_unique (successProbability_four_tendsto_zero hC) h
  exact zero_ne_one h01

/-- This rules out even an arbitrary positive denominator depending on the
fixed dimension, a broader class than polynomial denominators. -/
theorem no_positive_denominator_function :
    ¬ ∃ D : ℕ → ℝ, (∀ n : ℕ, 2 ≤ n → 0 < D n) ∧
      ∀ n : ℕ, 2 ≤ n → Tendsto (successProbability n (D n)) atTop (𝓝 1) := by
  rintro ⟨D, hD, hlim⟩
  exact successProbability_four_not_tendsto_one (hD 4 (by omega)) (hlim 4 (by omega))

/-- Negation of the original existential-polynomial reading. -/
theorem conjecture_false : ¬ OriginalClaim := by
  rintro ⟨P, hP, hlim⟩
  exact successProbability_four_not_tendsto_one (hP 4 (by omega)) (hlim 4 (by omega))

end Conjecture161
