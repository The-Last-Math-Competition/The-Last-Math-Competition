import Conjecture1663.Definitions

namespace Conjecture1663

theorem edgeEditCost_iso {n : ℕ} {G H : Graph n} (e : G ≃g H) :
    edgeEditCost G H e.toEquiv = 0 := by
  classical
  simp only [edgeEditCost, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _ hp
  exact hp.2 e.map_adj_iff.symm

theorem editDistance_iso {n : ℕ} {G H : Graph n} (e : G ≃g H) :
    editDistance G H = 0 := by
  have h := editDistance_le_cost G H e.toEquiv
  rw [edgeEditCost_iso e] at h
  exact Nat.eq_zero_of_le_zero h

/-- The counterexample works for every finite simple graph, regardless of its edges. -/
theorem editDistance_self {n : ℕ} (G : Graph n) : editDistance G G = 0 :=
  editDistance_iso SimpleGraph.Iso.refl

theorem every_graph_violates_rigidity {n : ℕ} (G : Graph (n + 1)) :
    deck G = deck G ∧ ¬(2 ≤ editDistance G G) := by
  exact ⟨rfl, by simp [editDistance_self]⟩

/-- Explicit order-three witness: the empty simple graph paired with itself. -/
theorem order_three_counterexample :
    ∃ G H : Graph 3, deck G = deck H ∧ editDistance G H < 2 := by
  refine ⟨⊥, ⊥, rfl, ?_⟩
  simp [editDistance_self]

theorem not_reconstructionRigidity : ¬ReconstructionRigidity := by
  intro h
  have bad := h 2 (by decide) (⊥ : Graph 3) ⊥ rfl
  rw [editDistance_self] at bad
  omega

/-- Disproof of the full conjunction; this does not disprove classical reconstruction. -/
theorem originalClaim_false : ¬OriginalClaim :=
  fun h => not_reconstructionRigidity h.2

end Conjecture1663
