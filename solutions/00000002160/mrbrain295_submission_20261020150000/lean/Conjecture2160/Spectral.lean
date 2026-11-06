/-
Spectral facts about strongly regular graphs with parameters (100, 22, 0, 6):
every adjacency eigenvalue lies in {22, 2, -8}, and the least one is exactly -8.
Consequently Hoffman's ratio bound for such a graph equals 80/3.
-/
import Mathlib

namespace Conjecture2160

open SimpleGraph Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem adjMatrix_isHermitian (G : SimpleGraph V) [DecidableRel G.Adj] :
    (adjMatrix ℝ G).IsHermitian := by
  simp [Matrix.IsHermitian]

/-- The least eigenvalue of the (real, symmetric) adjacency matrix of `G`. -/
noncomputable def minAdjEigenvalue (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (adjMatrix_isHermitian G).eigenvalues

/-- Hoffman's ratio bound for a `k`-regular graph `G` on `n` vertices with least adjacency
eigenvalue `λ_min`: `n · (-λ_min) / (k - λ_min)`.  Hoffman's theorem says that the
independence number is at most this quantity; "the bound is attained" means equality. -/
noncomputable def hoffmanBound (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (k : ℕ) : ℝ :=
  (Fintype.card V : ℝ) * (-minAdjEigenvalue G) / ((k : ℝ) - minAdjEigenvalue G)

omit [Fintype V] in
theorem adjMatrix_compl_eq [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    adjMatrix ℝ Gᶜ = Matrix.of (fun _ _ => (1:ℝ)) - 1 - adjMatrix ℝ G := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · by_cases ha : G.Adj i j <;> simp [adjMatrix_apply, compl_adj, h, ha, Matrix.one_apply_ne h]

/-- Every eigenvalue of an srg(100, 22, 0, 6) is `22`, `2` or `-8`. -/
theorem srg_eigenvalue_cases (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsSRGWith 100 22 0 6) (μ : ℝ) (v : V → ℝ) (hv : v ≠ 0)
    (h : (adjMatrix ℝ G) *ᵥ v = μ • v) : μ = 22 ∨ μ = 2 ∨ μ = -8 := by
  have hm := hG.matrix_eq (α := ℝ)
  rw [adjMatrix_compl_eq] at hm
  have h2 : (adjMatrix ℝ G ^ 2) *ᵥ v = (μ^2) • v := by
    rw [pow_two, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, h, smul_smul, pow_two]
  rw [hm] at h2
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h] at h2
  have key : ∀ x, (μ^2 + 6*μ - 16) * v x = 6 * ∑ y, v y := by
    intro x
    have := congrFun h2 x
    simp [Matrix.mulVec, dotProduct] at this
    linarith
  by_cases hq : μ^2 + 6*μ - 16 = 0
  · right
    have : (μ - 2) * (μ + 8) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · left; linarith
    · right; linarith
  · left
    set c := (6 * ∑ y, v y) / (μ^2 + 6*μ - 16)
    have hvc : v = Function.const V c := by
      funext x
      simp only [Function.const_apply, c]
      rw [eq_div_iff hq, ← key x]; ring
    obtain ⟨x, hx⟩ : ∃ x, v x ≠ 0 := by
      by_contra hcon; push_neg at hcon; exact hv (funext hcon)
    have hreg := congrFun h x
    rw [hvc, adjMatrix_mulVec_const_apply_of_regular hG.regular] at hreg
    have hc : c ≠ 0 := by rw [hvc] at hx; simpa using hx
    simp at hreg
    rcases hreg with h | h
    · linarith
    · exact absurd h hc

theorem srg_eigenvalues_cases (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsSRGWith 100 22 0 6) (i : V) :
    (adjMatrix_isHermitian G).eigenvalues i = 22 ∨ (adjMatrix_isHermitian G).eigenvalues i = 2 ∨
      (adjMatrix_isHermitian G).eigenvalues i = -8 := by
  set hA := adjMatrix_isHermitian G
  apply srg_eigenvalue_cases G hG _ (hA.eigenvectorBasis i).ofLp
  · intro h0
    have := (hA.eigenvectorBasis).orthonormal.1 i
    have h1 : (hA.eigenvectorBasis i) = 0 := by
      ext x; simpa using congrFun h0 x
    rw [h1] at this; simp at this
  · exact hA.mulVec_eigenvectorBasis i

/-- The least adjacency eigenvalue of any srg(100, 22, 0, 6) is `-8`. -/
theorem srg_minAdjEigenvalue (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hG : G.IsSRGWith 100 22 0 6) : minAdjEigenvalue G = -8 := by
  set hA := adjMatrix_isHermitian G
  have hcases := srg_eigenvalues_cases G hG
  have hge : ∀ i, -8 ≤ hA.eigenvalues i := by
    intro i; rcases hcases i with h | h | h <;> rw [h] <;> norm_num
  have hex : ∃ i, hA.eigenvalues i = -8 := by
    by_contra hne
    push_neg at hne
    have h2 : ∀ i, 2 ≤ hA.eigenvalues i := by
      intro i; rcases hcases i with h | h | h
      · rw [h]; norm_num
      · rw [h]
      · exact absurd h (hne i)
    have htr := hA.trace_eq_sum_eigenvalues
    rw [trace_adjMatrix] at htr
    have : (∑ _i : V, (2:ℝ)) ≤ ∑ i, hA.eigenvalues i := Finset.sum_le_sum (fun i _ => h2 i)
    have hc : (Fintype.card V : ℝ) = 100 := by exact_mod_cast hG.card
    simp [hc] at this
    have htr' : (∑ i, hA.eigenvalues i) = 0 := by exact_mod_cast htr.symm
    linarith
  obtain ⟨i, hi⟩ := hex
  apply le_antisymm
  · rw [← hi]; exact Finset.inf'_le _ (Finset.mem_univ i)
  · exact Finset.le_inf' _ _ (fun j _ => hge j)

/-- Hoffman's ratio bound of any srg(100, 22, 0, 6) equals `80/3`. -/
theorem srg_hoffmanBound (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hG : G.IsSRGWith 100 22 0 6) : hoffmanBound G 22 = 80 / 3 := by
  have hc : (Fintype.card V : ℝ) = 100 := by exact_mod_cast hG.card
  rw [hoffmanBound, srg_minAdjEigenvalue G hG, hc]
  norm_num

/-- No srg(100, 22, 0, 6) attains Hoffman's ratio bound: the bound `80/3` is not an
integer, while the independence number is. -/
theorem srg_indepNum_ne_hoffmanBound (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hG : G.IsSRGWith 100 22 0 6) : (G.indepNum : ℝ) ≠ hoffmanBound G 22 := by
  rw [srg_hoffmanBound G hG]
  intro h
  have h3 : ((3 * G.indepNum : ℕ) : ℝ) = (80 : ℕ) := by push_cast; linarith
  have := Nat.cast_injective h3
  omega

end Conjecture2160
