import ConnectedPartial

namespace P4110Geometry
noncomputable section
variable {V E W F : Type*}
variable [TopologicalSpace V] [DiscreteTopology V]
variable [TopologicalSpace W] [DiscreteTopology W]

def rawRelabeling (v : V ≃ W) (e : E ≃ F) : CellPoint V E → CellPoint W F :=
  Sum.elim (fun a => .inl (v a)) (fun p => .inr ⟨e p.1, p.2⟩)

theorem rawRelabeling_respects (G : CellGraph V E) (H : CellGraph W F)
    (v : V ≃ W) (e : E ≃ F)
    (hs : ∀ a, v (G.source a) = H.source (e a))
    (ht : ∀ a, v (G.target a) = H.target (e a))
    (a b : CellPoint V E) (h : EndpointRelation G a b) :
    Quot.mk (EndpointRelation H) (rawRelabeling v e a) =
      Quot.mk (EndpointRelation H) (rawRelabeling v e b) := by
  cases h with
  | source a =>
    change Quot.mk (EndpointRelation H) (.inr ⟨e a, intervalZero⟩) = Quot.mk (EndpointRelation H) (.inl (v (G.source a)))
    rw [hs]
    exact Quot.sound (EndpointRelation.source (e a))
  | target a =>
    change Quot.mk (EndpointRelation H) (.inr ⟨e a, intervalOne⟩) = Quot.mk (EndpointRelation H) (.inl (v (G.target a)))
    rw [ht]
    exact Quot.sound (EndpointRelation.target (e a))

def cellRelabeling (G : CellGraph V E) (H : CellGraph W F)
    (v : V ≃ W) (e : E ≃ F)
    (hs : ∀ a, v (G.source a) = H.source (e a))
    (ht : ∀ a, v (G.target a) = H.target (e a)) :
    CellRealization G → CellRealization H :=
  Quot.lift (fun a => Quot.mk _ (rawRelabeling v e a))
    (rawRelabeling_respects G H v e hs ht)

theorem continuous_rawRelabeling (v : V ≃ W) (e : E ≃ F) :
    Continuous (rawRelabeling v e) := by
  apply continuous_sumElim.mpr
  constructor
  · exact continuous_inl.comp continuous_of_discreteTopology
  · apply continuous_sigma
    intro a
    change Continuous (fun t : EdgeInterval => Sum.inr (Sigma.mk (e a) t) : EdgeInterval → CellPoint W F)
    exact continuous_inr.comp continuous_sigmaMk

theorem continuous_cellRelabeling (G : CellGraph V E) (H : CellGraph W F)
    (v : V ≃ W) (e : E ≃ F)
    (hs : ∀ a, v (G.source a) = H.source (e a))
    (ht : ∀ a, v (G.target a) = H.target (e a)) :
    Continuous (cellRelabeling G H v e hs ht) :=
  continuous_quot_lift (rawRelabeling_respects G H v e hs ht)
    (continuous_quot_mk.comp (continuous_rawRelabeling v e))

def cellRelabelingHomeomorph (G : CellGraph V E) (H : CellGraph W F)
    (v : V ≃ W) (e : E ≃ F)
    (hs : ∀ a, v (G.source a) = H.source (e a))
    (ht : ∀ a, v (G.target a) = H.target (e a)) :
    CellRealization G ≃ₜ CellRealization H := by
  have hsi : ∀ b, v.symm (H.source b) = G.source (e.symm b) := by
    intro b
    apply v.injective
    simpa using (hs (e.symm b)).symm
  have hti : ∀ b, v.symm (H.target b) = G.target (e.symm b) := by
    intro b
    apply v.injective
    simpa using (ht (e.symm b)).symm
  exact {
    toFun := cellRelabeling G H v e hs ht
    invFun := cellRelabeling H G v.symm e.symm hsi hti
    left_inv := by
      intro q
      induction q using Quot.inductionOn with
      | h a =>
        cases a with
        | inl a => simp [cellRelabeling, rawRelabeling]
        | inr p => cases p; simp [cellRelabeling, rawRelabeling]
    right_inv := by
      intro q
      induction q using Quot.inductionOn with
      | h a =>
        cases a with
        | inl a => simp [cellRelabeling, rawRelabeling]
        | inr p => cases p; simp [cellRelabeling, rawRelabeling]
    continuous_toFun := continuous_cellRelabeling G H v e hs ht
    continuous_invFun := continuous_cellRelabeling H G v.symm e.symm hsi hti
  }

#print axioms cellRelabelingHomeomorph
end
end P4110Geometry
