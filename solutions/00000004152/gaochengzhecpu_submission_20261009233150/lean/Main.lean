import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum

noncomputable section
open Filter
open scoped BigOperators Topology

namespace Conjecture4152

/-- Actual residue tuples representing `a` as a sum of `s` kth powers modulo `q`.
The entries `Fin q` are the canonical representatives 0,...,q-1. -/
def WaringSolutions (k s a q : ℕ) :=
  {x : Fin s → Fin q // (∑ i, (x i).val ^ k) % q = a % q}

def solutionCount (k s a q : ℕ) : ℕ := Nat.card (WaringSolutions k s a q)

/-- The standard prime-power local-density approximants. For s ≥ 1 the
denominator is q^(s-1), where q=p^(e+1); the positive shift only omits e=0. -/
def density (k s a p e : ℕ) : ℝ :=
  (solutionCount k s a (p ^ (e + 1)) : ℝ) /
    ((p ^ (e + 1) : ℕ) : ℝ) ^ (s - 1)

theorem density_nonnegative (k s a p e : ℕ) : 0 ≤ density k s a p e := by
  unfold density
  positivity

/-- A local factor is specified by the actual residue-count limit, without
assuming any sign for that factor. -/
def IsLocalFactor (k s a p : ℕ) (L : ℝ) : Prop :=
  Tendsto (density k s a p) atTop (𝓝 L)

theorem local_factor_nonnegative {k s a p : ℕ} {L : ℝ}
    (h : IsLocalFactor k s a p L) : 0 ≤ L :=
  ge_of_tendsto h (Eventually.of_forall (density_nonnegative k s a p))

/-- The finite Euler product over primes not exceeding N. -/
def eulerPartial (localFactor : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime, localFactor p

theorem euler_partial_nonnegative {k s a : ℕ} {L : ℕ → ℝ}
    (h : ∀ p, p.Prime → IsLocalFactor k s a p (L p)) (N : ℕ) :
    0 ≤ eulerPartial L N := by
  apply Finset.prod_nonneg
  intro p hp
  exact local_factor_nonnegative (h p (Finset.mem_filter.mp hp).2)

/-- A defined Euler-product singular series consists of local-density limits
and the limit of their prime-ordered finite products. -/
def IsWaringSingularSeries (k s a : ℕ) (S : ℝ) : Prop :=
  ∃ L : ℕ → ℝ, (∀ p, p.Prime → IsLocalFactor k s a p (L p)) ∧
    Tendsto (eulerPartial L) atTop (𝓝 S)

theorem waring_singular_series_nonnegative {k s a : ℕ} {S : ℝ}
    (h : IsWaringSingularSeries k s a S) : 0 ≤ S := by
  obtain ⟨L, hL, hS⟩ := h
  exact ge_of_tendsto hS (Eventually.of_forall (euler_partial_nonnegative hL))

theorem no_negative_fourth_power_singular_series :
    ¬ ∃ s a : ℕ, ∃ S : ℝ, IsWaringSingularSeries 4 s a S ∧ S < 0 := by
  rintro ⟨s, a, S, hS, hneg⟩
  exact (not_lt_of_ge (waring_singular_series_nonnegative hS)) hneg

theorem no_negative_fourth_power_local_factor :
    ¬ ∃ s a p : ℕ, ∃ L : ℝ, p.Prime ∧ IsLocalFactor 4 s a p L ∧ L < 0 := by
  rintro ⟨s, a, p, L, _, hL, hneg⟩
  exact (not_lt_of_ge (local_factor_nonnegative hL)) hneg

end Conjecture4152

#print axioms Conjecture4152.waring_singular_series_nonnegative
#print axioms Conjecture4152.no_negative_fourth_power_singular_series
#print axioms Conjecture4152.no_negative_fourth_power_local_factor
