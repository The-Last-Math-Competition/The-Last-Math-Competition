import Mathlib
import Submission.Charpoly

set_option linter.unusedSectionVars false

/-!
# Conjecture 00000003718: the matching polynomial of a tree has only real roots

Combining `matchingPolynomial_eq_charpoly` (for forests the matching polynomial is the
characteristic polynomial of the adjacency matrix) with the spectral theorem for real symmetric
matrices, we obtain:

* `TLMC3718.matchingPolynomial_splits`: for a tree `T`, `μ(T; x) ∈ ℝ[x]` splits into linear
  factors over `ℝ`;
* `TLMC3718.card_roots_matchingPolynomial`: it has exactly `|V|` real roots with multiplicity;
* `TLMC3718.im_eq_zero_of_isRoot`: every complex root of `μ(T; x)` is real;
* `TLMC3718.sum_roots_pow_eq_card_closedWalks`: the `k`-th power sum of the roots equals the
  number of closed walks of length `k` in `T` — the root distribution is the (moment) transform of
  the closed-walk counts.
-/

open Polynomial Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem adjMatrix_isHermitian_real : (G.adjMatrix ℝ).IsHermitian := by
  rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]
  exact G.transpose_adjMatrix

theorem adjMatrix_isHermitian_complex : (G.adjMatrix ℂ).IsHermitian := by
  ext i j
  by_cases h : G.Adj i j
  · simp [conjTranspose_apply, adjMatrix_apply, h, h.symm]
  · have h' : ¬ G.Adj j i := fun hh => h hh.symm
    simp [conjTranspose_apply, adjMatrix_apply, h, h']

variable (R : Type*) [CommRing R]

/-- The matching polynomial is compatible with change of coefficient ring. -/
theorem matchingPolyIn_map {S : Type*} [CommRing S] (f : R →+* S) (s : Finset V) :
    (G.matchingPolyIn R s).map f = G.matchingPolyIn S s := by
  simp [matchingPolyIn, Polynomial.map_sum]

theorem matchingPolynomial_map {S : Type*} [CommRing S] (f : R →+* S) :
    (G.matchingPolynomial R).map f = G.matchingPolynomial S :=
  G.matchingPolyIn_map R f Finset.univ

end SimpleGraph

namespace TLMC3718

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj]

/-- **Heilmann–Lieb for trees.** The matching polynomial of a tree splits over `ℝ`: all of its
roots are real. -/
theorem matchingPolynomial_splits (hT : T.IsTree) : (T.matchingPolynomial ℝ).Splits := by
  rw [T.matchingPolynomial_eq_charpoly ℝ hT.isAcyclic]
  exact T.adjMatrix_isHermitian_real.splits_charpoly

/-- The matching polynomial of a tree on `n` vertices has exactly `n` real roots, counted with
multiplicity. -/
theorem card_roots_matchingPolynomial (hT : T.IsTree) :
    (T.matchingPolynomial ℝ).roots.card = Fintype.card V := by
  rw [← (matchingPolynomial_splits T hT).natDegree_eq_card_roots,
    T.matchingPolynomial_eq_charpoly ℝ hT.isAcyclic, charpoly_natDegree_eq_dim]

/-- Every complex root of the matching polynomial of a tree is a real number. -/
theorem exists_real_of_isRoot (hT : T.IsTree) {z : ℂ} (hz : (T.matchingPolynomial ℂ).IsRoot z) :
    ∃ r : ℝ, (r : ℂ) = z := by
  rw [T.matchingPolynomial_eq_charpoly ℂ hT.isAcyclic] at hz
  have hH := T.adjMatrix_isHermitian_complex
  have hmem : z ∈ (T.adjMatrix ℂ).charpoly.roots :=
    (mem_roots (charpoly_monic _).ne_zero).mpr hz
  rw [hH.roots_charpoly_eq_eigenvalues, Multiset.mem_map] at hmem
  obtain ⟨i, -, hi⟩ := hmem
  exact ⟨hH.eigenvalues i, hi⟩

theorem im_eq_zero_of_isRoot (hT : T.IsTree) {z : ℂ} (hz : (T.matchingPolynomial ℂ).IsRoot z) :
    z.im = 0 := by
  obtain ⟨r, rfl⟩ := exists_real_of_isRoot T hT hz
  exact Complex.ofReal_im r

/-- The `k`-th power sum of the roots of `μ(T; x)` is the number of closed walks of length `k`
in `T`: the distribution of the (real) roots is the moment transform of the closed-walk counts. -/
theorem sum_roots_pow_eq_card_closedWalks (hT : T.IsTree) (k : ℕ) :
    ((T.matchingPolynomial ℝ).roots.map (fun r => r ^ k)).sum =
      ∑ v, (Fintype.card {p : T.Walk v v | p.length = k} : ℝ) := by
  rw [T.matchingPolynomial_eq_charpoly ℝ hT.isAcyclic]
  have hH := T.adjMatrix_isHermitian_real
  have h1 : (T.adjMatrix ℝ ^ k).trace = ∑ i, (hH.eigenvalues i) ^ k := by
    conv_lhs => rw [hH.spectral_theorem, ← map_pow, Unitary.conjStarAlgAut_apply]
    rw [trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, diagonal_pow, trace_diagonal]
    simp
  have h2 : (T.adjMatrix ℝ ^ k).trace =
      ∑ v, (Fintype.card {p : T.Walk v v | p.length = k} : ℝ) := by
    simp only [Matrix.trace, Matrix.diag_apply, adjMatrix_pow_apply_eq_card_walk]
  rw [← h2, h1, hH.roots_charpoly_eq_eigenvalues, Multiset.map_map, Finset.sum_eq_multiset_sum]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun i _ => ?_)
  simp

/-- **Conjecture 00000003718** (the statement as filed, formalized).  For every finite tree `T`:
the matching polynomial `μ(T; x)` has only real roots — it splits over `ℝ`, has `|V(T)|` real
roots with multiplicity, and every complex root is real — and the distribution of these roots is
the moment transform of the closed-walk (path) counts of `T`. -/
theorem conjecture_00000003718 (hT : T.IsTree) :
    (T.matchingPolynomial ℝ).Splits ∧
    (T.matchingPolynomial ℝ).roots.card = Fintype.card V ∧
    (∀ z : ℂ, (T.matchingPolynomial ℂ).IsRoot z → z.im = 0) ∧
    (∀ k : ℕ, ((T.matchingPolynomial ℝ).roots.map (fun r => r ^ k)).sum =
      ∑ v, (Fintype.card {p : T.Walk v v | p.length = k} : ℝ)) :=
  ⟨matchingPolynomial_splits T hT, card_roots_matchingPolynomial T hT,
    fun _ hz => im_eq_zero_of_isRoot T hT hz, sum_roots_pow_eq_card_closedWalks T hT⟩

end TLMC3718
