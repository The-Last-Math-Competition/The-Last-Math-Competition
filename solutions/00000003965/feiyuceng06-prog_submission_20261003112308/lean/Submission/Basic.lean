import Mathlib

/-!
# Conjecture 00000003965: boxicity of a graph and of its complement can differ by `3`

A `d`-dimensional *box representation* of a graph `G` assigns to every vertex an axis-parallel
box in `ℝ^d` (a product of closed intervals) so that distinct vertices are adjacent iff their
boxes intersect. The *boxicity* `box G` is the least such `d`.

Conjecture 00000003965 claims `|box G − box Gᶜ| ≤ 2` for every graph `G`. Let `G` be the
complete multipartite graph `K_{2,2,2,2}` (Mathlib's `completeEquipartiteGraph 4 2`). Its
complement is the perfect matching `4K₂`. Then:

* `box Gᶜ ≤ 1`: the matching is an interval graph (vertex `(i, s)` gets `[3i, 3i + 1]`);
* `box G ≥ 4`: each of the four non-adjacent pairs `{(i,0), (i,1)}` needs a coordinate in
  which its two intervals are disjoint, and no coordinate can serve two pairs. Indeed, if the
  intervals of `(i,0)` and `(i,1)` are disjoint, every interval meeting both contains the gap
  between them, so the intervals of `(k,0)` and `(k,1)`, which meet both, intersect each other.

So `box G − box Gᶜ ≥ 3` (in fact `box G = 4`; the representation used is also given).
-/

namespace Submission00000003965

open SimpleGraph

/-- A `d`-dimensional box representation of `G`: vertex `v` gets the box
`∏ i, [l v i, r v i]`, and distinct vertices are adjacent iff their boxes intersect, i.e. iff
their intervals overlap in every coordinate. -/
structure BoxRep {V : Type*} (G : SimpleGraph V) (d : ℕ) where
  l : V → Fin d → ℝ
  r : V → Fin d → ℝ
  le : ∀ v i, l v i ≤ r v i
  adj_iff : ∀ u v, u ≠ v → (G.Adj u v ↔ ∀ i, l u i ≤ r v i ∧ l v i ≤ r u i)

/-- The boxicity of `G`: the least `d` admitting a `d`-dimensional box representation. -/
noncomputable def boxicity {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {d | Nonempty (BoxRep G d)}

/-- The claim of Conjecture 00000003965: every (finite) graph satisfies
`|box G − box Gᶜ| ≤ 2`. -/
def BoxicityGapAtMostTwo : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    |(boxicity G : ℤ) - (boxicity Gᶜ : ℤ)| ≤ 2

/-- The complete multipartite graph `K_{2,2,2,2}` on `Fin 4 × Fin 2`: `(i, s)` and `(k, t)` are
adjacent iff `i ≠ k`. -/
abbrev K : SimpleGraph (Fin 4 × Fin 2) := completeEquipartiteGraph 4 2

instance : DecidableRel K.Adj := fun u v =>
  decidable_of_iff (u.1 ≠ v.1) completeEquipartiteGraph_adj.symm

/-! ### Upper bound `box Kᶜ ≤ 1` -/

/-- Integer endpoints of the one-dimensional representation of the matching `Kᶜ`. -/
def lC (v : Fin 4 × Fin 2) : ℕ := 3 * v.1.val
def rC (v : Fin 4 × Fin 2) : ℕ := 3 * v.1.val + 1

theorem complement_iff : ∀ u v : Fin 4 × Fin 2, u ≠ v →
    (Kᶜ.Adj u v ↔ lC u ≤ rC v ∧ lC v ≤ rC u) := by decide

/-- The matching `Kᶜ = 4K₂` is an interval graph. -/
def repCompl : BoxRep Kᶜ 1 where
  l v _ := (lC v : ℝ)
  r v _ := (rC v : ℝ)
  le v _ := by simp only [lC, rC, Nat.cast_le]; omega
  adj_iff u v huv := by
    simp only [Nat.cast_le, forall_const]
    exact complement_iff u v huv

theorem boxicity_compl_le : boxicity Kᶜ ≤ 1 := Nat.sInf_le ⟨repCompl⟩

/-! ### A representation of `K` in dimension `4` -/

/-- Integer endpoints: in coordinate `j`, the pair `{(j,0), (j,1)}` gets the disjoint
intervals `[0,1]` and `[2,3]`; every other vertex gets `[0,3]`. -/
def lK (v : Fin 4 × Fin 2) (j : Fin 4) : ℕ := if v.1 = j then (if v.2 = 0 then 0 else 2) else 0
def rK (v : Fin 4 × Fin 2) (j : Fin 4) : ℕ := if v.1 = j then (if v.2 = 0 then 1 else 3) else 3

theorem K_iff : ∀ u v : Fin 4 × Fin 2, u ≠ v →
    (K.Adj u v ↔ ∀ j, lK u j ≤ rK v j ∧ lK v j ≤ rK u j) := by decide

theorem lK_le_rK : ∀ v j, lK v j ≤ rK v j := by decide

def repK : BoxRep K 4 where
  l v j := (lK v j : ℝ)
  r v j := (rK v j : ℝ)
  le v j := by exact_mod_cast lK_le_rK v j
  adj_iff u v huv := by
    simp only [Nat.cast_le]
    exact K_iff u v huv

/-! ### Lower bound `box K ≥ 4` -/

/-- If two closed intervals `[a₁,a₂]`, `[b₁,b₂]` are disjoint and two further intervals
`[c₁,c₂]`, `[e₁,e₂]` each meet both of them, then these two further intervals meet. -/
theorem interval_lemma {a₁ a₂ b₁ b₂ c₁ c₂ e₁ e₂ : ℝ}
    (hab : ¬ (a₁ ≤ b₂ ∧ b₁ ≤ a₂))
    (hca : a₁ ≤ c₂ ∧ c₁ ≤ a₂) (hcb : b₁ ≤ c₂ ∧ c₁ ≤ b₂)
    (hea : a₁ ≤ e₂ ∧ e₁ ≤ a₂) (heb : b₁ ≤ e₂ ∧ e₁ ≤ b₂) :
    c₁ ≤ e₂ ∧ e₁ ≤ c₂ := by
  rcases not_and_or.1 hab with h | h <;> push Not at h <;> constructor <;> linarith

/-- `K` has no box representation of dimension `d < 4`. -/
theorem no_rep_of_lt_four {d : ℕ} (hd : d < 4) : BoxRep K d → False := by
  intro R
  -- vertices `(i,0)` and `(i,1)` are distinct and not adjacent, so some coordinate separates them
  have hsep : ∀ i : Fin 4, ∃ j : Fin d,
      ¬ (R.l (i, 0) j ≤ R.r (i, 1) j ∧ R.l (i, 1) j ≤ R.r (i, 0) j) := by
    intro i
    by_contra h
    push Not at h
    have hadj := (R.adj_iff (i, 0) (i, 1) (by simp)).2 (fun j => h j)
    exact (completeEquipartiteGraph_adj.1 hadj) rfl
  choose sep hsep using hsep
  obtain ⟨i, k, hik, hj⟩ := Fintype.exists_ne_map_eq_of_card_lt sep (by simpa using hd)
  -- cross pairs are adjacent, hence overlap in every coordinate
  have cross : ∀ s t : Fin 2, ∀ j, R.l (i, s) j ≤ R.r (k, t) j ∧ R.l (k, t) j ≤ R.r (i, s) j :=
    fun s t => (R.adj_iff (i, s) (k, t) (by simp [hik])).1 (completeEquipartiteGraph_adj.2 hik)
  apply hsep k
  rw [← hj]
  have h00 := cross 0 0 (sep i)
  have h01 := cross 0 1 (sep i)
  have h10 := cross 1 0 (sep i)
  have h11 := cross 1 1 (sep i)
  exact interval_lemma (hsep i) h00 h10 h01 h11

theorem four_le_boxicity : 4 ≤ boxicity K := by
  refine le_csInf ⟨4, ⟨repK⟩⟩ fun d ⟨R⟩ => ?_
  by_contra h
  exact no_rep_of_lt_four (not_le.1 h) R

/-- `box K = 4`. -/
theorem boxicity_K : boxicity K = 4 :=
  le_antisymm (Nat.sInf_le ⟨repK⟩) four_le_boxicity

/-- **Conjecture 00000003965 is false**: `box K − box Kᶜ ≥ 4 − 1 = 3`. -/
theorem conjecture_00000003965_false : ¬ BoxicityGapAtMostTwo := by
  intro h
  have h1 := h (Fin 4 × Fin 2) K
  have h2 := four_le_boxicity
  have h3 := boxicity_compl_le
  have : (3 : ℤ) ≤ (boxicity K : ℤ) - (boxicity Kᶜ : ℤ) := by omega
  have := le_abs_self ((boxicity K : ℤ) - (boxicity Kᶜ : ℤ))
  omega

end Submission00000003965

#print axioms Submission00000003965.conjecture_00000003965_false
#print axioms Submission00000003965.boxicity_K
