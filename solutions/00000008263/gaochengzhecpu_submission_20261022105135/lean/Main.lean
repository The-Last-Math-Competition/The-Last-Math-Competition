import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open Finset
namespace Conjecture8263

/-- A finite probability law, using exact rational masses. -/
structure FiniteLaw (Ω : Type) [Fintype Ω] where
  mass : Ω → ℚ
  nonnegative : ∀ x, 0 ≤ mass x
  total : ∑ x, mass x = 1

def expectation {Ω : Type} [Fintype Ω] (p : FiniteLaw Ω) (X : Ω → ℚ) : ℚ :=
  ∑ x, p.mass x * X x

def variance {Ω : Type} [Fintype Ω] (p : FiniteLaw Ω) (X : Ω → ℚ) : ℚ :=
  expectation p (fun x => (X x - expectation p X)^2)

def weights (K : Type) [Field K] (i : Fin 4) : K :=
  if i.val % 2 = 0 then 1/8 else 3/8
def observable (K : Type) [Field K] (i : Fin 4) : K :=
  if i.val % 2 = 0 then 1 else 0

/-- Inverse CDF for an ordered four-particle weighted population.
The final branch is the fourth particle; callers use an input in [0,1). -/
def inverseCDF {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (p : Fin 4 → K) (u : K) : Fin 4 :=
  if u < p 0 then 0 else
  if u < p 0 + p 1 then 1 else
  if u < p 0 + p 1 + p 2 then 2 else 3

def sampleMean {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (f : Fin 4 → K)
    (draw : Fin 4 → Fin 4) : K := (∑ i, f (draw i)) / 4

def systematic {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (p f : Fin 4 → K) (u : K) : K :=
  sampleMean f (fun i => inverseCDF p (u + (i.val : K)/4))

/-- The entire continuous systematic phase interval is evaluated,
including the actual labels selected by inverse CDF. -/
theorem phase_selections {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (u : K)
    (hu : 0 ≤ u) (hv : u < 1/4) (i : Fin 4) :
    inverseCDF (weights K) (u + (i.val : K)/4) =
      (if u < 1/8 then i else if i.val < 2 then 1 else 3) := by
  fin_cases i <;> norm_num [inverseCDF, weights] <;>
    split_ifs <;> norm_num [Fin.ext_iff, Fin.val_natCast, Fin.coe_ofNat_eq_mod] at * <;> linarith

theorem phase_formula {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (u : K)
    (hu : 0 ≤ u) (hv : u < 1/4) :
    systematic (weights K) (observable K) u = if u < 1/8 then 1/2 else 0 := by
  unfold systematic sampleMean
  simp_rw [phase_selections u hu hv]
  split_ifs <;> simp only [Fin.sum_univ_succ] <;>
    norm_num [observable, Fin.val_natCast, Fin.coe_ofNat_eq_mod]

def phaseLaw : FiniteLaw (Fin 2) where
  mass _ := 1/2
  nonnegative _ := by norm_num
  total := by norm_num [Fin.sum_univ_succ]

/-- Midpoints of the two equal-length phase strata, whose probabilities
are exactly 1/2 for a uniform phase in [0,1/4). -/
def phase (r : Fin 2) : ℚ := (2*(r.val : ℚ)+1)/16

def systematicEstimator (f : Fin 4 → ℚ) (r : Fin 2) : ℚ :=
  systematic (weights ℚ) f (phase r)

theorem systematicEstimator_formula (r : Fin 2) :
    systematicEstimator (observable ℚ) r = if r = 0 then 1/2 else 0 := by
  unfold systematicEstimator
  rw [phase_formula _ (by fin_cases r <;> norm_num [phase])
    (by fin_cases r <;> norm_num [phase])]
  fin_cases r <;> norm_num [phase]

abbrev Outcomes := Fin 4 × Fin 4 × Fin 4 × Fin 4

def multinomialLaw : FiniteLaw Outcomes where
  mass ω := weights ℚ ω.1 * weights ℚ ω.2.1 * weights ℚ ω.2.2.1 * weights ℚ ω.2.2.2
  nonnegative ω := by
    have hw (i : Fin 4) : 0 ≤ weights ℚ i := by fin_cases i <;> norm_num [weights]
    exact mul_nonneg (mul_nonneg (mul_nonneg (hw _) (hw _)) (hw _)) (hw _)
  total := by
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, weights]

def multinomialEstimator (f : Fin 4 → ℚ) (ω : Outcomes) : ℚ :=
  (f ω.1 + f ω.2.1 + f ω.2.2.1 + f ω.2.2.2) / 4

theorem systematic_mean : expectation phaseLaw (systematicEstimator (observable ℚ)) = 1/4 := by
  unfold expectation
  simp_rw [systematicEstimator_formula]
  norm_num [phaseLaw, Fin.sum_univ_succ]

theorem systematic_variance : variance phaseLaw (systematicEstimator (observable ℚ)) = 1/16 := by
  rw [variance, systematic_mean]
  unfold expectation
  simp_rw [systematicEstimator_formula]
  norm_num [phaseLaw, Fin.sum_univ_succ]

theorem multinomial_mean : expectation multinomialLaw (multinomialEstimator (observable ℚ)) = 1/4 := by
  norm_num [expectation, multinomialLaw, multinomialEstimator, observable, weights,
    Fintype.sum_prod_type, Fin.sum_univ_succ]

theorem multinomial_variance : variance multinomialLaw (multinomialEstimator (observable ℚ)) = 3/64 := by
  rw [variance, multinomial_mean]
  norm_num [expectation, multinomialLaw, multinomialEstimator, observable, weights,
    Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- The universal halving assertion must apply, in particular, to every
observable on this legal positive four-particle weighted population. -/
def HalvingClaim : Prop := ∀ f : Fin 4 → ℚ,
  variance phaseLaw (systematicEstimator f) ≤
    variance multinomialLaw (multinomialEstimator f) / 2

theorem systematic_worse : variance multinomialLaw (multinomialEstimator (observable ℚ)) <
    variance phaseLaw (systematicEstimator (observable ℚ)) := by
  rw [multinomial_variance, systematic_variance]
  norm_num

theorem conjecture8263_false : ¬ HalvingClaim := by
  intro h
  have hf := h (observable ℚ)
  rw [systematic_variance, multinomial_variance] at hf
  norm_num at hf

#print axioms phase_formula
#print axioms systematic_worse
#print axioms conjecture8263_false
end Conjecture8263
