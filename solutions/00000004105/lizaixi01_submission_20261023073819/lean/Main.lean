import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Filter Asymptotics

namespace TLMC4105

/-- The usual polynomial upper-growth property, using Mathlib's actual big O. -/
def PolynomialGrowth (f : ℕ → ℝ) : Prop :=
  ∃ d : ℕ, f =O[atTop] (fun n : ℕ => (n : ℝ) ^ d)

/-- An explicit eventual numerical polynomial envelope; norms handle arbitrary candidates. -/
def PolynomialEnvelope (f : ℕ → ℝ) : Prop :=
  ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
    ∀ n ≥ N, ‖f n‖ ≤ C * (n : ℝ) ^ d

/-- Arbitrarily late numerical violations of every polynomial upper envelope.
This is not defined by negating the preceding predicate, and does not impose
the stronger requirement of eventual domination at every subsequent index. -/
def SuperPolynomial (f : ℕ → ℝ) : Prop :=
  ∀ d : ℕ, ∀ C : ℝ, 0 < C → ∀ N : ℕ,
    ∃ n ≥ N, C * (n : ℝ) ^ d < f n

theorem norm_nat_power (n d : ℕ) : ‖(n : ℝ) ^ d‖ = (n : ℝ) ^ d := by
  exact Real.norm_of_nonneg (by positivity)

theorem polynomial_iff_envelope (f : ℕ → ℝ) :
    PolynomialGrowth f ↔ PolynomialEnvelope f := by
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨C, hC, hbound⟩ := hd.exists_pos
    obtain ⟨N, hN⟩ := eventually_atTop.mp hbound.bound
    exact ⟨d, C, hC, N, fun n hn => by simpa only [norm_nat_power] using hN n hn⟩
  · rintro ⟨d, C, _, N, hN⟩
    refine ⟨d, IsBigO.of_bound C ?_⟩
    exact eventually_atTop.mpr ⟨N, fun n hn => by simpa only [norm_nat_power] using hN n hn⟩

theorem envelope_incompatible (f : ℕ → ℝ) :
    ¬ (PolynomialEnvelope f ∧ SuperPolynomial f) := by
  rintro ⟨⟨d, C, hC, N, hN⟩, hsuper⟩
  obtain ⟨n, hn, hlarge⟩ := hsuper d C hC N
  have hsmall : f n ≤ C * (n : ℝ) ^ d :=
    (le_abs_self (f n)).trans (by simpa only [Real.norm_eq_abs] using hN n hn)
  exact (not_lt_of_ge hsmall) hlarge

theorem polynomial_incompatible (f : ℕ → ℝ) :
    ¬ (PolynomialGrowth f ∧ SuperPolynomial f) := by
  rintro ⟨hp, hs⟩
  exact envelope_incompatible f ⟨(polynomial_iff_envelope f).mp hp, hs⟩

/-- For nonnegative actual count functions the quantitative predicate is exactly
the absence of any polynomial big-O upper bound, including all cutoff constants. -/
theorem super_iff_not_polynomial (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    SuperPolynomial f ↔ ¬ PolynomialGrowth f := by
  constructor
  · intro hs hp
    exact polynomial_incompatible f ⟨hp, hs⟩
  · intro hp d C hC N
    apply Classical.byContradiction
    intro hnone
    have hbound : ∀ n ≥ N, ‖f n‖ ≤ C * (n : ℝ) ^ d := by
      intro n hn
      have hle : f n ≤ C * (n : ℝ) ^ d :=
        le_of_not_gt (fun hgt => hnone ⟨n, hn, hgt⟩)
      simpa only [Real.norm_of_nonneg (hf n)] using hle
    exact hp ((polynomial_iff_envelope f).mpr ⟨d, C, hC, N, hbound⟩)

/-- Every actual star, independent of its order or chosen center, already gives
the same obstruction. Finiteness is retained to match the graph-growth claim. -/
theorem no_assignment_at_any_star {V : Type*} [Finite V] (r : V)
    (growth : SimpleGraph V → ℕ → ℝ) :
    ¬ ((∀ G, G.IsTree → PolynomialGrowth (growth G)) ∧
      SuperPolynomial (growth (SimpleGraph.starGraph r))) := by
  rintro ⟨htree, hstar⟩
  exact polynomial_incompatible (growth (SimpleGraph.starGraph r))
    ⟨htree _ (SimpleGraph.isTree_starGraph r), hstar⟩

/-- The concrete four-vertex star, not a predicate given a graph's name. -/
abbrev Star := SimpleGraph.starGraph (0 : Fin 4)

theorem actual_star_is_tree : Star.IsTree :=
  SimpleGraph.isTree_starGraph (0 : Fin 4)

theorem actual_star_order : Fintype.card (Fin 4) = 4 := by simp

theorem actual_star_edges : Star.edgeFinset.card = 3 := by
  have h := actual_star_is_tree.card_edgeFinset
  norm_num at h ⊢
  omega

/-- Any assignment of candidate growth functions to actual four-vertex graphs
fails the two necessary source clauses on the very same star. No value of a
configuration-space fundamental group's growth is assigned or assumed. -/
theorem no_graph_growth_assignment
    (growth : SimpleGraph (Fin 4) → ℕ → ℝ) :
    ¬ ((∀ G, PolynomialGrowth (growth G) ↔ G.IsTree) ∧
      SuperPolynomial (growth Star)) := by
  rintro ⟨htree, hstar⟩
  exact polynomial_incompatible (growth Star)
    ⟨(htree Star).mpr actual_star_is_tree, hstar⟩

/-- Only the tree-to-polynomial implication is already incompatible with the
star's asserted super-polynomial growth; the reverse implication is not needed. -/
theorem no_necessary_upper_growth_assignment
    (growth : SimpleGraph (Fin 4) → ℕ → ℝ) :
    ¬ ((∀ G, G.IsTree → PolynomialGrowth (growth G)) ∧
      SuperPolynomial (growth Star)) := by
  rintro ⟨htree, hstar⟩
  exact polynomial_incompatible (growth Star) ⟨htree Star actual_star_is_tree, hstar⟩

/-- Explicitly includes assignments on every finite labelled graph order. -/
theorem no_all_finite_graph_assignment
    (growth : ∀ n : ℕ, SimpleGraph (Fin n) → ℕ → ℝ) :
    ¬ ((∀ n G, PolynomialGrowth (growth n G) ↔ G.IsTree) ∧
      SuperPolynomial (growth 4 Star)) := by
  rintro ⟨htree, hstar⟩
  exact no_graph_growth_assignment (growth 4) ⟨htree 4, hstar⟩

theorem no_natural_count_assignment
    (count : ∀ n : ℕ, SimpleGraph (Fin n) → ℕ → ℕ) :
    ¬ ((∀ n G, PolynomialGrowth (fun r => (count n G r : ℝ)) ↔ G.IsTree) ∧
      SuperPolynomial (fun r => (count 4 Star r : ℝ))) := by
  exact no_all_finite_graph_assignment (fun n G r => (count n G r : ℝ))

end TLMC4105
