import Mathlib
import Submission.DetLeaf
import Submission.MatchingPoly
import Submission.Leaf

set_option linter.unusedSectionVars false

/-!
# The matching polynomial of a forest is the characteristic polynomial of its adjacency matrix

For a finite acyclic graph `G` (a forest) and every finite set `s` of vertices,

  `μ(G[s]; x) = det (x·I - A(G[s]))`,

where `A(G[s])` is the adjacency matrix of the induced subgraph.  Both sides satisfy the same
leaf recurrence `f(s) = x·f(s ∖ v) - f(s ∖ {v, u})` whenever `v ∈ s` has the single neighbour
`u` in `s`, and both equal `x^{|s|}` when `s` spans no edge.  (This is the classical theorem of
Godsil–Gutman / Heilmann–Lieb: for forests, matching and characteristic polynomials coincide.)
-/

open Polynomial Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (R : Type*) [CommRing R]

/-- The adjacency matrix of the induced subgraph `G[s]`. -/
def adjMatrixIn (s : Finset V) : Matrix s s R :=
  (G.adjMatrix R).submatrix Subtype.val Subtype.val

theorem adjMatrixIn_apply (s : Finset V) (i j : s) :
    G.adjMatrixIn R s i j = if G.Adj i j then 1 else 0 := by
  simp [adjMatrixIn, adjMatrix_apply]

/-- `charmatrix` commutes with principal submatrices. -/
theorem charmatrix_submatrix_val {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → Prop}
    [DecidablePred p] (M : Matrix ι ι R) :
    (charmatrix M).submatrix (Subtype.val : {x // p x} → ι) Subtype.val =
      charmatrix (M.submatrix Subtype.val Subtype.val) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [charmatrix_apply_eq]
  · have h' : (i : ι) ≠ j := fun hh => h (Subtype.ext hh)
    simp [charmatrix_apply_ne, h, h']

section Leaf

variable {s : Finset V} {v u : V}

/-- Deleting `v` from `s`, as a bijection between index types. -/
def eraseEquiv (hv : v ∈ s) : {x : s // x ≠ ⟨v, hv⟩} ≃ ↥(s.erase v) where
  toFun x := ⟨x.1.1, Finset.mem_erase.mpr ⟨fun h => x.2 (Subtype.ext h), x.1.2⟩⟩
  invFun y := ⟨⟨y.1, Finset.mem_of_mem_erase y.2⟩,
    fun h => (Finset.mem_erase.mp y.2).1 (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Deleting `v` and `u` from `s`, as a bijection between index types. -/
def eraseEquiv₂ (hv : v ∈ s) (hu : u ∈ s) :
    {x : s // x ≠ ⟨v, hv⟩ ∧ x ≠ ⟨u, hu⟩} ≃ ↥((s.erase v).erase u) where
  toFun x := ⟨x.1.1, Finset.mem_erase.mpr ⟨fun h => x.2.2 (Subtype.ext h),
    Finset.mem_erase.mpr ⟨fun h => x.2.1 (Subtype.ext h), x.1.2⟩⟩⟩
  invFun y := ⟨⟨y.1, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase y.2)⟩,
    ⟨fun h => (Finset.mem_erase.mp (Finset.mem_of_mem_erase y.2)).1 (congrArg Subtype.val h),
     fun h => (Finset.mem_erase.mp y.2).1 (congrArg Subtype.val h)⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem adjMatrixIn_erase (hv : v ∈ s) :
    G.adjMatrixIn R (s.erase v) =
      reindex (eraseEquiv hv) (eraseEquiv hv) (TLMC3718.minor (G.adjMatrixIn R s) ⟨v, hv⟩) := by
  ext i j
  simp [adjMatrixIn, TLMC3718.minor, reindex_apply, eraseEquiv]

theorem adjMatrixIn_erase₂ (hv : v ∈ s) (hu : u ∈ s) :
    G.adjMatrixIn R ((s.erase v).erase u) =
      reindex (eraseEquiv₂ hv hu) (eraseEquiv₂ hv hu)
        (TLMC3718.minor₂ (G.adjMatrixIn R s) ⟨v, hv⟩ ⟨u, hu⟩) := by
  ext i j
  simp [adjMatrixIn, TLMC3718.minor₂, reindex_apply, eraseEquiv₂]

/-- **Leaf recurrence** for the characteristic polynomial of the adjacency matrix. -/
theorem charpoly_adjMatrixIn_leaf (hv : v ∈ s) (hu : u ∈ s) (hvu : v ≠ u) (hadj : G.Adj v u)
    (hleaf : ∀ w ∈ s, G.Adj v w → w = u) :
    (G.adjMatrixIn R s).charpoly =
      X * (G.adjMatrixIn R (s.erase v)).charpoly -
        (G.adjMatrixIn R ((s.erase v).erase u)).charpoly := by
  set A := G.adjMatrixIn R s with hA
  have hvu' : (⟨v, hv⟩ : s) ≠ ⟨u, hu⟩ := fun h => hvu (congrArg Subtype.val h)
  have hrow : ∀ w : s, w ≠ ⟨v, hv⟩ → w ≠ ⟨u, hu⟩ → charmatrix A ⟨v, hv⟩ w = 0 := by
    intro w hwv hwu
    have hnadj : ¬ G.Adj v w := fun h => hwu (Subtype.ext (hleaf w w.2 h))
    rw [charmatrix_apply_ne A _ _ (Ne.symm hwv), hA, adjMatrixIn_apply, if_neg hnadj]
    simp
  have hcol : ∀ w : s, w ≠ ⟨v, hv⟩ → w ≠ ⟨u, hu⟩ → charmatrix A w ⟨v, hv⟩ = 0 := by
    intro w hwv hwu
    have hnadj : ¬ G.Adj w v := fun h => hwu (Subtype.ext (hleaf w w.2 h.symm))
    rw [charmatrix_apply_ne A _ _ hwv, hA, adjMatrixIn_apply, if_neg hnadj]
    simp
  have hvv : charmatrix A ⟨v, hv⟩ ⟨v, hv⟩ = X := by
    rw [charmatrix_apply_eq A, hA, adjMatrixIn_apply, if_neg G.irrefl]
    simp
  have hvu'' : charmatrix A ⟨v, hv⟩ ⟨u, hu⟩ = -1 := by
    rw [charmatrix_apply_ne A _ _ hvu', hA, adjMatrixIn_apply, if_pos hadj]
    simp
  have huv : charmatrix A ⟨u, hu⟩ ⟨v, hv⟩ = -1 := by
    rw [charmatrix_apply_ne A _ _ hvu'.symm, hA, adjMatrixIn_apply, if_pos hadj.symm]
    simp
  have h1 : (TLMC3718.minor (charmatrix A) ⟨v, hv⟩).det =
      (G.adjMatrixIn R (s.erase v)).charpoly := by
    rw [adjMatrixIn_erase, charpoly_reindex, charpoly, TLMC3718.minor, TLMC3718.minor,
      charmatrix_submatrix_val]
  have h2 : (TLMC3718.minor₂ (charmatrix A) ⟨v, hv⟩ ⟨u, hu⟩).det =
      (G.adjMatrixIn R ((s.erase v).erase u)).charpoly := by
    rw [adjMatrixIn_erase₂, charpoly_reindex, charpoly, TLMC3718.minor₂, TLMC3718.minor₂,
      charmatrix_submatrix_val]
  rw [charpoly, TLMC3718.det_leaf (charmatrix A) ⟨v, hv⟩ ⟨u, hu⟩ hvu' hrow hcol, hvv, hvu'', huv,
    h1, h2]
  ring

end Leaf

/-- If `s` spans no edge, the adjacency matrix of `G[s]` vanishes. -/
theorem adjMatrixIn_eq_zero (s : Finset V) (h : ∀ a ∈ s, ∀ b ∈ s, ¬ G.Adj a b) :
    G.adjMatrixIn R s = 0 := by
  ext i j
  simp [adjMatrixIn_apply, h i.1 i.2 j.1 j.2]

/-- **Main identity.**  For a forest `G` and any vertex set `s`, the matching polynomial of
`G[s]` equals the characteristic polynomial of the adjacency matrix of `G[s]`. -/
theorem matchingPolyIn_eq_charpoly (hG : G.IsAcyclic) (s : Finset V) :
    G.matchingPolyIn R s = (G.adjMatrixIn R s).charpoly := by
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hedge : ∃ a ∈ s, ∃ b ∈ s, G.Adj a b
    · obtain ⟨a, ha, b, hb, hab⟩ := hedge
      obtain ⟨v, hv, u, hu, hadj, hleaf⟩ := hG.exists_leaf_in s ha hb hab
      have hvu : v ≠ u := hadj.ne
      have hu' : u ∈ s.erase v := Finset.mem_erase.mpr ⟨hvu.symm, hu⟩
      rw [G.matchingPolyIn_leaf R hv hu hvu hadj hleaf,
        G.charpoly_adjMatrixIn_leaf R hv hu hvu hadj hleaf,
        ih _ (Finset.erase_ssubset hv),
        ih _ ((Finset.erase_ssubset hu').trans (Finset.erase_ssubset hv))]
    · push Not at hedge
      rw [G.matchingPolyIn_of_no_edge R s hedge, G.adjMatrixIn_eq_zero R s hedge,
        Matrix.charpoly_zero, Fintype.card_coe]

/-- The adjacency matrix of `G` is the adjacency matrix of `G[univ]`, up to reindexing. -/
theorem adjMatrix_eq_reindex :
    G.adjMatrix R =
      reindex (Equiv.subtypeUnivEquiv Finset.mem_univ) (Equiv.subtypeUnivEquiv Finset.mem_univ)
        (G.adjMatrixIn R Finset.univ) := by
  ext i j
  simp [adjMatrixIn, reindex_apply, Equiv.subtypeUnivEquiv]

/-- **Theorem (Godsil–Gutman).** For a forest, the matching polynomial equals the characteristic
polynomial of the adjacency matrix. -/
theorem matchingPolynomial_eq_charpoly (hG : G.IsAcyclic) :
    G.matchingPolynomial R = (G.adjMatrix R).charpoly := by
  rw [matchingPolynomial, G.matchingPolyIn_eq_charpoly R hG, G.adjMatrix_eq_reindex R,
    charpoly_reindex]

end SimpleGraph
