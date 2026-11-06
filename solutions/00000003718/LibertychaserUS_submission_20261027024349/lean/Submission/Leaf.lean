import Mathlib

set_option linter.unusedSectionVars false

/-!
# Leaves of forests

If an acyclic graph has an edge inside a finite vertex set `s`, then some vertex of `s` has exactly
one neighbour inside `s`.  (Take an end point of a longest path of the induced subgraph `G[s]`.)
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In an acyclic graph, if some edge lies inside `s`, then some vertex `v ∈ s` has exactly one
neighbour `u` inside `s`. -/
theorem IsAcyclic.exists_leaf_in (hG : G.IsAcyclic) (s : Finset V) {a b : V} (ha : a ∈ s)
    (hb : b ∈ s) (hab : G.Adj a b) :
    ∃ v ∈ s, ∃ u ∈ s, G.Adj v u ∧ ∀ w ∈ s, G.Adj v w → w = u := by
  classical
  let H : SimpleGraph (↥(s : Set V)) := G.induce (s : Set V)
  have hH : H.IsAcyclic := hG.induce _
  have : Nonempty (↥(s : Set V)) := ⟨⟨a, by simpa using ha⟩⟩
  obtain ⟨x, y, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length H
  have hab' : H.Adj ⟨a, by simpa using ha⟩ ⟨b, by simpa using hb⟩ := by
    simpa [H, comap_adj] using hab
  have hlen : 1 ≤ p.length := by
    have := hmax _ _ (Path.singleton hab').1 (Path.singleton hab').2
    simpa [Path.singleton] using this
  have hnil : ¬ p.Nil := by
    rw [← Walk.length_eq_zero_iff]
    omega
  refine ⟨x.1, by simp, p.snd, by simp, p.adj_snd hnil, ?_⟩
  intro w hw hadj
  have hadjH : H.Adj x ⟨w, by simpa using hw⟩ := by
    simpa [H, comap_adj] using hadj
  have hsupp : (⟨w, by simpa using hw⟩ : ↥(s : Set V)) ∈ p.support := by
    by_contra hns
    have hpath : (p.cons hadjH.symm).IsPath := hp.cons hns
    have := hmax _ _ _ hpath
    simp [Walk.length_cons] at this
  have := hH.eq_snd_of_adj_start hp hadjH hsupp
  exact congrArg Subtype.val this

end SimpleGraph
