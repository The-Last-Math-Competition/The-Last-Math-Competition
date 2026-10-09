import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Disproof of conjecture 00000001569

Angles are ordinary, unoriented Euclidean angles in radians, at a vertex of an
ordered triple of pairwise distinct points in the real Euclidean plane.
The original imposes no noncollinearity assumption. An n-point subset of the
x-axis has at most two such angle values, for every n.
-/

noncomputable section
open EuclideanGeometry
open scoped Real

namespace Conjecture1569

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The genuine Euclidean angle set, represented as a finite set of real values.
All triples use three pairwise distinct points. -/
def angleSet (S : Finset Plane) : Finset ℝ := by
  classical
  exact ((S ×ˢ (S ×ˢ S)).filter
    (fun t => t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2)).image
    (fun t => ∠ t.1 t.2.1 t.2.2)

/-- This representation counts precisely all angles determined by the point set. -/
theorem mem_angleSet_iff (S : Finset Plane) (θ : ℝ) :
    θ ∈ angleSet S ↔ ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S,
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ ∠ a b c = θ := by
  classical
  simp only [angleSet, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨a, b, c⟩, ⟨⟨ha, hb, hc⟩, hab, hbc, hac⟩, hθ⟩
    exact ⟨a, ha, b, hb, c, hc, hab, hbc, hac, hθ⟩
  · rintro ⟨a, ha, b, hb, c, hc, hab, hbc, hac, hθ⟩
    exact ⟨(a, b, c), ⟨⟨ha, hb, hc⟩, hab, hbc, hac⟩, hθ⟩

/-- The real x-axis, expressed in the standard Euclidean plane. -/
noncomputable def axisPoint (x : ℝ) : Plane := !₂[x, 0]

theorem axisPoint_injective : Function.Injective axisPoint := by
  intro x y h
  have := congrArg (fun p : Plane => p 0) h
  simpa [axisPoint] using this

/-- An explicit n-point set, including the cases n = 0, 1, 2. -/
def configuration (n : ℕ) : Finset Plane := by
  classical
  exact (Finset.range n).image (fun j : ℕ => axisPoint (j : ℝ))

theorem configuration_card (n : ℕ) : (configuration n).card = n := by
  classical
  rw [configuration, Finset.card_image_of_injective]
  · exact Finset.card_range n
  · intro i j h
    exact_mod_cast axisPoint_injective h

theorem configuration_mem_axis {n : ℕ} {p : Plane} (hp : p ∈ configuration n) :
    p ∈ Set.range axisPoint := by
  classical
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
  exact ⟨(j : ℝ), rfl⟩

theorem axis_collinear : Collinear ℝ (Set.range axisPoint) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨0, axisPoint 1, ?_⟩
  rintro p ⟨x, rfl⟩
  refine ⟨x, ?_⟩
  ext i
  fin_cases i <;> simp [axisPoint]

/-- The geometric bridge: every angle in the configuration is 0 or pi. -/
theorem configuration_angle_zero_or_pi {n : ℕ} {a b c : Plane}
    (ha : a ∈ configuration n) (hb : b ∈ configuration n)
    (hc : c ∈ configuration n) (hab : a ≠ b) (hbc : b ≠ c) :
    ∠ a b c = 0 ∨ ∠ a b c = Real.pi := by
  have hcol : Collinear ℝ ({a, b, c} : Set Plane) := axis_collinear.subset (by
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact configuration_mem_axis ha
    · exact configuration_mem_axis hb
    · exact configuration_mem_axis hc)
  have h := collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.mp hcol
  exact h.resolve_left hab |>.resolve_left (Ne.symm hbc)

theorem configuration_angleSet_subset (n : ℕ) :
    angleSet (configuration n) ⊆ {0, Real.pi} := by
  intro θ hθ
  obtain ⟨a, ha, b, hb, c, hc, hab, hbc, _, rfl⟩ := (mem_angleSet_iff _ _).mp hθ
  simpa using configuration_angle_zero_or_pi ha hb hc hab hbc

theorem configuration_angleSet_card_le (n : ℕ) :
    (angleSet (configuration n)).card ≤ 2 := by
  classical
  calc
    (angleSet (configuration n)).card ≤ ({0, Real.pi} : Finset ℝ).card :=
      Finset.card_le_card (configuration_angleSet_subset n)
    _ ≤ 2 := by simp [Real.pi_ne_zero, Ne.symm Real.pi_ne_zero]

/-- The quantified uniform meaning of the claimed n² - O(n) lower bound. -/
def UniformQuadraticLowerBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ S : Finset Plane, S.card = n →
      (n : ℝ) ^ 2 - C * (n : ℝ) ≤ ((angleSet S).card : ℝ)

/-- For every real linear-loss constant and every threshold, an actual finite
planar point set violates the alleged lower bound. -/
theorem arbitrarily_large_counterexamples (C : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ∃ S : Finset Plane, S.card = n ∧
      ((angleSet S).card : ℝ) < (n : ℝ) ^ 2 - C * (n : ℝ) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max C 2)
  let n := max N m
  have hmn : m ≤ n := le_max_right N m
  have hNn : N ≤ n := le_max_left N m
  have hnC : C < (n : ℝ) := lt_of_le_of_lt (le_max_left C 2)
    (lt_of_lt_of_le hm (by exact_mod_cast hmn))
  have hn2 : (2 : ℝ) < n := lt_of_le_of_lt (le_max_right C 2)
    (lt_of_lt_of_le hm (by exact_mod_cast hmn))
  -- Choose one extra unit beyond n so the quadratic gap dominates two.
  refine ⟨n + 1, le_trans hNn (Nat.le_succ n), configuration (n + 1),
    configuration_card (n + 1), ?_⟩
  have hcard : ((angleSet (configuration (n + 1))).card : ℝ) ≤ 2 := by
    exact_mod_cast configuration_angleSet_card_le (n + 1)
  push_cast
  nlinarith

/-- The first necessary conjunct of the original conjecture is false. -/
theorem not_uniformQuadraticLowerBound : ¬ UniformQuadraticLowerBound := by
  rintro ⟨C, _, N, h⟩
  obtain ⟨n, hn, S, hS, hlt⟩ := arbitrarily_large_counterexamples C N
  exact (not_lt_of_ge (h n hn S hS)) hlt

/-- Therefore the full conjunction in the original is false, independently of
how its additional lattice-attainment clause is made precise. -/
theorem original_conjunction_false (LatticeAttainment : Prop) :
    ¬ (UniformQuadraticLowerBound ∧ LatticeAttainment) := by
  exact fun h => not_uniformQuadraticLowerBound h.1

end Conjecture1569
