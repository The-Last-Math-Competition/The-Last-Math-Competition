import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum

open Filter MeasureTheory

namespace Conjecture00000007842

def LowerBound {Ω : Type*} (theta : Nat → Ω → ℝ) : Prop :=
  ∀ n omega, (4 : ℝ) / 3 ≤ theta n omega

-- A necessary neighborhood-mass condition on the broader domain of all measures.
-- The probability/measurability wrapper below supplies the standard interpretation.
def ConcentratesTo {Ω : Type*} [MeasurableSpace Ω]
    (law : Nat → Measure Ω) (theta : Nat → Ω → ℝ) (a : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    Tendsto (fun n => (law n {omega | |theta n omega - a| < epsilon}).toReal)
      atTop (nhds (1 : ℝ))

def NumericClaims {Ω : Type*} [MeasurableSpace Ω]
    (law : Nat → Measure Ω) (theta : Nat → Ω → ℝ) (a : ℝ) : Prop :=
  LowerBound theta ∧ ConcentratesTo law theta a

theorem half_log_three_le_one : Real.log 3 / 2 ≤ (1 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (x := (3 : ℝ)) (by norm_num)
  linarith

theorem log_three_halves_le_one : Real.log ((3 : ℝ) / 2) ≤ (1 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (x := (3 : ℝ) / 2) (by norm_num)
  linarith

theorem empty_neighborhood {Ω : Type*} (theta : Nat → Ω → ℝ)
    (h : LowerBound theta) (a : ℝ) (ha : a ≤ 1) (n : Nat) :
    {omega | |theta n omega - a| < (1 : ℝ) / 6} = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro omega hm
  have htheta := h n omega
  have hsub : theta n omega - a < (1 : ℝ) / 6 :=
    lt_of_le_of_lt (le_abs_self (theta n omega - a)) hm
  linarith

theorem zero_neighborhood_probability {Ω : Type*} [MeasurableSpace Ω]
    (law : Nat → Measure Ω) (theta : Nat → Ω → ℝ)
    (h : LowerBound theta) (a : ℝ) (ha : a ≤ 1) (n : Nat) :
    (law n {omega | |theta n omega - a| < (1 : ℝ) / 6}).toReal = 0 := by
  rw [empty_neighborhood theta h a ha n]
  simp

theorem no_concentration_below_one {Ω : Type*} [MeasurableSpace Ω]
    (law : Nat → Measure Ω) (theta : Nat → Ω → ℝ)
    (h : LowerBound theta) (a : ℝ) (ha : a ≤ 1) : ¬ ConcentratesTo law theta a := by
  intro hcon
  have hlim := hcon ((1 : ℝ) / 6) (by norm_num)
  have hzero : (fun n => (law n {omega | |theta n omega - a| < (1 : ℝ) / 6}).toReal) =
      (fun _ : Nat => (0 : ℝ)) := by
    funext n
    exact zero_neighborhood_probability law theta h a ha n
  rw [hzero] at hlim
  have h01 : (0 : ℝ) = 1 := tendsto_nhds_unique tendsto_const_nhds hlim
  norm_num at h01

theorem numeric_claims_impossible {Ω : Type*} [MeasurableSpace Ω]
    (law : Nat → Measure Ω) (theta : Nat → Ω → ℝ)
    (a : ℝ) (ha : a ≤ 1) : ¬ NumericClaims law theta a := by
  intro h
  exact no_concentration_below_one law theta h.1 a ha h.2

-- Both conventional parses of 'log 3/2' are refuted, not merely approximated.
theorem conjecture_negation_half_log {Ω : Type*} [MeasurableSpace Ω]
    (law : Nat → Measure Ω) (theta : Nat → Ω → ℝ) :
    ¬ NumericClaims law theta (Real.log 3 / 2) :=
  numeric_claims_impossible law theta (Real.log 3 / 2) half_log_three_le_one

theorem conjecture_negation_log_quotient {Ω : Type*} [MeasurableSpace Ω]
    (law : Nat → Measure Ω) (theta : Nat → Ω → ℝ) :
    ¬ NumericClaims law theta (Real.log ((3 : ℝ) / 2)) :=
  numeric_claims_impossible law theta (Real.log ((3 : ℝ) / 2)) log_three_halves_le_one

-- Exact substitution bridge for ANY graph-indexed quantity, including the stated
-- ratio of expected blanket and cover times. No value of that ratio is assumed.
theorem graph_indexed_obstruction {Graph Ω : Type*} [MeasurableSpace Ω]
    (theta : Graph → ℝ) (sample : Nat → Ω → Graph) (law : Nat → Measure Ω)
    (hgraph : ∀ G, (4 : ℝ) / 3 ≤ theta G) :
    ¬ ConcentratesTo law (fun n omega => theta (sample n omega)) (Real.log 3 / 2) :=
  no_concentration_below_one law (fun n omega => theta (sample n omega))
    (fun n omega => hgraph (sample n omega)) (Real.log 3 / 2) half_log_three_le_one

theorem expected_time_ratio_obstruction {Graph Ω : Type*} [MeasurableSpace Ω]
    (expectedBlanket expectedCover : Graph → ℝ)
    (sample : Nat → Ω → Graph) (law : Nat → Measure Ω)
    (hgraph : ∀ G, (4 : ℝ) / 3 ≤ expectedBlanket G / expectedCover G) :
    ¬ ConcentratesTo law (fun n omega => expectedBlanket (sample n omega) /
      expectedCover (sample n omega)) (Real.log 3 / 2) :=
  graph_indexed_obstruction (fun G => expectedBlanket G / expectedCover G) sample law hgraph

theorem source_negation_half_log {Graph Ω : Type*} [MeasurableSpace Ω]
    (expectedBlanket expectedCover : Graph → ℝ)
    (sample : Nat → Ω → Graph) (law : Nat → Measure Ω) :
    ¬ ((∀ G, (4 : ℝ) / 3 ≤ expectedBlanket G / expectedCover G) ∧
      ConcentratesTo law (fun n omega => expectedBlanket (sample n omega) /
        expectedCover (sample n omega)) (Real.log 3 / 2)) := by
  intro h
  exact expected_time_ratio_obstruction expectedBlanket expectedCover sample law h.1 h.2

theorem source_negation_log_quotient {Graph Ω : Type*} [MeasurableSpace Ω]
    (expectedBlanket expectedCover : Graph → ℝ)
    (sample : Nat → Ω → Graph) (law : Nat → Measure Ω) :
    ¬ ((∀ G, (4 : ℝ) / 3 ≤ expectedBlanket G / expectedCover G) ∧
      ConcentratesTo law (fun n omega => expectedBlanket (sample n omega) /
        expectedCover (sample n omega)) (Real.log ((3 : ℝ) / 2))) := by
  intro h
  exact no_concentration_below_one law
    (fun n omega => expectedBlanket (sample n omega) / expectedCover (sample n omega))
    (fun n omega => h.1 (sample n omega)) (Real.log ((3 : ℝ) / 2))
    log_three_halves_le_one h.2

-- Standard neighborhood formulation of concentration in probability, with actual
-- normalized laws and measurable random variables. The broader core is a projection.
def ConcentratesInProbability {Ω : Type*} [MeasurableSpace Ω]
    (law : Nat → Measure Ω) (theta : Nat → Ω → ℝ) (a : ℝ) : Prop :=
  (∀ n, IsProbabilityMeasure (law n)) ∧ (∀ n, Measurable (theta n)) ∧
    ConcentratesTo law theta a

theorem probability_concentration_implies_neighborhood_mass {Ω : Type*} [MeasurableSpace Ω]
    (law : Nat → Measure Ω) (theta : Nat → Ω → ℝ) (a : ℝ)
    (h : ConcentratesInProbability law theta a) : ConcentratesTo law theta a := h.2.2

theorem source_probability_negation_half_log {Graph Ω : Type*} [MeasurableSpace Ω]
    (expectedBlanket expectedCover : Graph → ℝ)
    (sample : Nat → Ω → Graph) (law : Nat → Measure Ω) :
    ¬ ((∀ G, (4 : ℝ) / 3 ≤ expectedBlanket G / expectedCover G) ∧
      ConcentratesInProbability law (fun n omega => expectedBlanket (sample n omega) /
        expectedCover (sample n omega)) (Real.log 3 / 2)) := by
  intro h
  exact source_negation_half_log expectedBlanket expectedCover sample law ⟨h.1, h.2.2.2⟩

theorem source_probability_negation_log_quotient {Graph Ω : Type*} [MeasurableSpace Ω]
    (expectedBlanket expectedCover : Graph → ℝ)
    (sample : Nat → Ω → Graph) (law : Nat → Measure Ω) :
    ¬ ((∀ G, (4 : ℝ) / 3 ≤ expectedBlanket G / expectedCover G) ∧
      ConcentratesInProbability law (fun n omega => expectedBlanket (sample n omega) /
        expectedCover (sample n omega)) (Real.log ((3 : ℝ) / 2))) := by
  intro h
  exact source_negation_log_quotient expectedBlanket expectedCover sample law ⟨h.1, h.2.2.2⟩

end Conjecture00000007842
