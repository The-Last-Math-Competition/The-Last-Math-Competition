import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Rank
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Tactic
import Mathlib.Data.Real.StarOrdered

noncomputable section
namespace PatakiCeilingContradiction
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def feasible {n m : ℕ} (A : Fin m → Mat n) (b : Fin m → ℝ) : Set (Mat n) :=
  {X | X.PosSemidef ∧ ∀ i, Matrix.trace (A i * X) = b i}

def ceilingBound (m : ℕ) : ℕ :=
  Nat.ceil ((Real.sqrt (8 * (m : ℝ) + 1) - 1) / 2)

/-- The actual displayed inequality, quantified over all SDP instances. -/
def RankLaw (m : ℕ) : Prop :=
  ∀ n (A : Fin m → Mat n) (b : Fin m → ℝ) (X : Mat n),
    X ∈ (feasible A b).extremePoints ℝ →
      (X.rank : ℝ) * ((X.rank : ℝ) + 1) / 2 ≤ m

/-- Pointwise sharpness of the stated ceiling formula, with genuine extreme points. -/
def CeilingAttained (m : ℕ) : Prop :=
  ∃ (n : ℕ) (A : Fin m → Mat n) (b : Fin m → ℝ) (X : Mat n),
    X ∈ (feasible A b).extremePoints ℝ ∧ X.rank = ceilingBound m

theorem ceiling_at_two : ceilingBound 2 = 2 := by
  unfold ceilingBound
  norm_num
  apply (Nat.ceil_eq_iff (by norm_num : (2 : ℕ) ≠ 0)).mpr
  have hs : 0 ≤ Real.sqrt 17 := Real.sqrt_nonneg _
  have hsq : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  constructor <;> norm_num <;> nlinarith

theorem rank_at_most_one {n : ℕ} (h : RankLaw 2) (A : Fin 2 → Mat n)
    (b : Fin 2 → ℝ) (X : Mat n) (hX : X ∈ (feasible A b).extremePoints ℝ) :
    X.rank ≤ 1 := by
  have hb := h n A b X hX
  by_contra hn
  have hn' : (2 : ℝ) ≤ X.rank := by exact_mod_cast (by omega : 2 ≤ X.rank)
  norm_num at hb
  nlinarith

theorem no_attainment_under_rank_law (h : RankLaw 2) : ¬ CeilingAttained 2 := by
  rintro ⟨n, A, b, X, hX, hr⟩
  have hl := rank_at_most_one h A b X hX
  rw [ceiling_at_two] at hr
  omega

theorem incompatible_at_two : ¬ (RankLaw 2 ∧ CeilingAttained 2) := by
  rintro ⟨h, ha⟩
  exact no_attainment_under_rank_law h ha

theorem source_conjunction_impossible :
    ¬ ((∀ m, RankLaw m) ∧ ∀ m, CeilingAttained m) := by
  rintro ⟨h, ha⟩
  exact incompatible_at_two ⟨h 2, ha 2⟩

/-- An actual feasible SDP, with two stated equalities, has a rank-one extreme point. -/
def exampleA : Fin 2 → Mat 1 := fun _ => 1
def exampleB : Fin 2 → ℝ := fun _ => 1

theorem example_feasible : feasible exampleA exampleB = {1} := by
  ext X
  constructor
  · rintro ⟨_, hx⟩
    have h0 := hx 0
    have hentry : X 0 0 = 1 := by
      simpa [exampleA, exampleB, Matrix.trace, Fin.sum_univ_one] using h0
    apply Set.mem_singleton_iff.mpr
    ext i j
    fin_cases i <;> fin_cases j
    simpa using hentry
  · rintro rfl
    refine ⟨Matrix.PosSemidef.one, ?_⟩
    intro i
    simp [exampleA, exampleB, Matrix.trace]

theorem genuine_rank_one_example :
    (1 : Mat 1) ∈ (feasible exampleA exampleB).extremePoints ℝ ∧
      (1 : Mat 1).rank = 1 := by
  rw [example_feasible, extremePoints_singleton]
  simp [Matrix.rank_one]
end PatakiCeilingContradiction
end
#print axioms PatakiCeilingContradiction.ceiling_at_two
#print axioms PatakiCeilingContradiction.rank_at_most_one
#print axioms PatakiCeilingContradiction.incompatible_at_two
#print axioms PatakiCeilingContradiction.source_conjunction_impossible
#print axioms PatakiCeilingContradiction.genuine_rank_one_example
