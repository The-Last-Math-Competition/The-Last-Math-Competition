import Conjecture2821.Basic
import Conjecture2821.Limits
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! The usual open-set and closed-set large-deviation bounds with extended logarithms. -/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace Conjecture2821

/-- The speed is positive at every index and tends to infinity. -/
def IsSpeed (a : ℕ → ℝ) : Prop :=
  (∀ n, 0 < a n) ∧ Tendsto a atTop atTop

/-- The standard normalized extended logarithm; `ENNReal.log 0 = ⊥`. -/
def logProfile (μ : ℕ → Measure ℝ) (a : ℕ → ℝ) (A : Set ℝ) (n : ℕ) : EReal :=
  ((1 / a n : ℝ) : EReal) * ENNReal.log (μ n A)

/-- LDP in the usual open/closed-set form. Probabilities, speed, and lower
semicontinuity are included, rather than supplied as implicit conventions. -/
def HasLDP (μ : ℕ → Measure ℝ) (a : ℕ → ℝ) (I : ℝ → ℝ≥0∞) : Prop :=
  (∀ n, IsProbabilityMeasure (μ n)) ∧ IsSpeed a ∧ LowerSemicontinuous I ∧
  (∀ G : Set ℝ, IsOpen G →
    -((⨅ x ∈ G, I x : ℝ≥0∞) : EReal) ≤ liminf (logProfile μ a G) atTop) ∧
  (∀ F : Set ℝ, IsClosed F →
    limsup (logProfile μ a F) atTop ≤ -((⨅ x ∈ F, I x : ℝ≥0∞) : EReal))

/-- A good rate function has compact sublevels at every finite nonnegative level. -/
def GoodRate (I : ℝ → ℝ≥0∞) : Prop :=
  LowerSemicontinuous I ∧ ∀ r : ℝ≥0, IsCompact {x | I x ≤ (r : ℝ≥0∞)}

def speed (n : ℕ) : ℝ := (n : ℝ) + 1
def laws (_n : ℕ) : Measure ℝ := law

theorem speed_valid : IsSpeed speed := by
  constructor
  · intro n
    dsimp [speed]
    positivity
  · exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

/-- The full eventwise limit, stronger than either LDP bound, including empty sets. -/
theorem eventwise_limit (A : Set ℝ) :
    Tendsto (logProfile laws speed A) atTop
      (𝓝 (-((⨅ x ∈ A, rate x : ℝ≥0∞) : EReal))) := by
  change Tendsto (TwoPointLDP.normalizedLog (law A)) atTop _
  by_cases h : ∃ x ∈ A, x ∈ support
  · rw [rate_inf_of_hits h]
    simpa using TwoPointLDP.normalizedLog_tendsto_of_ne_zero
      ((law_pos_iff A).mpr h) (law_ne_top A)
  · have hz : law A = 0 := by
      by_contra hn
      exact h ((law_pos_iff A).mp hn)
    rw [rate_inf_of_misses h, hz]
    simpa using TwoPointLDP.normalizedLog_tendsto_zero

theorem laws_have_LDP : HasLDP laws speed rate := by
  refine ⟨fun _ => law_probability, speed_valid, rate_lowerSemicontinuous, ?_, ?_⟩
  · intro G _
    exact le_of_eq (eventwise_limit G).liminf_eq.symm
  · intro F _
    exact le_of_eq (eventwise_limit F).limsup_eq

theorem rate_is_good : GoodRate rate := ⟨rate_lowerSemicontinuous, rate_good⟩

/-- An explicit genuine LDP with a proper good rate and nonconvex sublevels
at every finite nonnegative level, and also a nonconvex exact zero level. -/
theorem counterexample :
    HasLDP laws speed rate ∧ GoodRate rate ∧ (∃ x, rate x < ⊤) ∧
      (∀ r : ℝ≥0, ¬ Convex ℝ {x | rate x ≤ (r : ℝ≥0∞)}) ∧
      ¬ Convex ℝ {x | rate x = 0} :=
  ⟨laws_have_LDP, rate_is_good, rate_proper,
    every_finite_sublevel_not_convex, zero_exact_level_not_convex⟩

/-- The universal compact-and-convex claim would imply this convexity statement;
the displayed good-rate LDP disproves that necessary consequence. -/
theorem not_all_good_ldp_sublevels_convex :
    ¬ (∀ (μ : ℕ → Measure ℝ) (a : ℕ → ℝ) (I : ℝ → ℝ≥0∞),
      HasLDP μ a I → GoodRate I → (∃ x, I x < ⊤) →
      ∀ r : ℝ≥0, Convex ℝ {x | I x ≤ (r : ℝ≥0∞)}) := by
  intro h
  exact every_finite_sublevel_not_convex 1
    (h laws speed rate laws_have_LDP rate_is_good rate_proper 1)

end Conjecture2821
