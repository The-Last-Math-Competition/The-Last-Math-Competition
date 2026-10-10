import Relabeling

namespace P4110Geometry
noncomputable section
variable {V E : Type*} [TopologicalSpace V] [DiscreteTopology V]

def intervalReverse (t : EdgeInterval) : EdgeInterval :=
  ⟨1-t.1, by constructor <;> linarith [t.2.1,t.2.2]⟩

@[simp] theorem intervalReverse_zero : intervalReverse intervalZero = intervalOne := by
  apply Subtype.ext
  norm_num [intervalReverse,intervalZero,intervalOne]
@[simp] theorem intervalReverse_one : intervalReverse intervalOne = intervalZero := by
  apply Subtype.ext
  norm_num [intervalReverse,intervalZero,intervalOne]
@[simp] theorem intervalReverse_reverse (t : EdgeInterval) :
    intervalReverse (intervalReverse t) = t := by
  apply Subtype.ext
  simp [intervalReverse]

def CellGraph.reorient (G : CellGraph V E) (r : E → Bool) : CellGraph V E where
  source a := if r a then G.target a else G.source a
  target a := if r a then G.source a else G.target a

def rawReorient (r : E → Bool) : CellPoint V E → CellPoint V E :=
  Sum.elim Sum.inl (fun p => Sum.inr ⟨p.1, if r p.1 then intervalReverse p.2 else p.2⟩)

theorem rawReorient_respects (G H : CellGraph V E) (r : E → Bool)
    (hs : ∀ a, H.source a = if r a then G.target a else G.source a)
    (ht : ∀ a, H.target a = if r a then G.source a else G.target a)
    (a b : CellPoint V E) (h : EndpointRelation G a b) :
    Quot.mk (EndpointRelation H) (rawReorient r a) =
      Quot.mk (EndpointRelation H) (rawReorient r b) := by
  cases h with
  | source a =>
    cases hr : r a
    · simpa [rawReorient,hr,hs] using (Quot.sound (EndpointRelation.source (G:=H) a))
    · simpa [rawReorient,hr,ht] using (Quot.sound (EndpointRelation.target (G:=H) a))
  | target a =>
    cases hr : r a
    · simpa [rawReorient,hr,ht] using (Quot.sound (EndpointRelation.target (G:=H) a))
    · simpa [rawReorient,hr,hs] using (Quot.sound (EndpointRelation.source (G:=H) a))

def reorientMap (G H : CellGraph V E) (r : E → Bool)
    (hs : ∀ a, H.source a = if r a then G.target a else G.source a)
    (ht : ∀ a, H.target a = if r a then G.source a else G.target a) :
    CellRealization G → CellRealization H :=
  Quot.lift (fun a => Quot.mk _ (rawReorient r a)) (rawReorient_respects G H r hs ht)

theorem continuous_rawReorient (r : E → Bool) : Continuous (rawReorient (V:=V) r) := by
  apply continuous_sumElim.mpr
  constructor
  · exact continuous_inl
  · apply continuous_sigma
    intro a
    change Continuous (fun t : EdgeInterval =>
      (Sum.inr (Sigma.mk a (if r a then intervalReverse t else t)) : CellPoint V E))
    cases hr : r a
    · change Continuous (fun t : EdgeInterval => (Sum.inr (Sigma.mk a t) : CellPoint V E))
      exact continuous_inr.comp continuous_sigmaMk
    · change Continuous (fun t : EdgeInterval => (Sum.inr (Sigma.mk a (intervalReverse t)) : CellPoint V E))
      apply continuous_inr.comp
      apply continuous_sigmaMk.comp
      exact (continuous_const.sub continuous_subtype_val).subtype_mk _

theorem continuous_reorientMap (G H : CellGraph V E) (r : E → Bool)
    (hs : ∀ a, H.source a = if r a then G.target a else G.source a)
    (ht : ∀ a, H.target a = if r a then G.source a else G.target a) :
    Continuous (reorientMap G H r hs ht) :=
  continuous_quot_lift (rawReorient_respects G H r hs ht)
    (continuous_quot_mk.comp (continuous_rawReorient r))

def cellReorientationHomeomorph (G : CellGraph V E) (r : E → Bool) :
    CellRealization G ≃ₜ CellRealization (G.reorient r) := by
  have hs : ∀ a, (G.reorient r).source a = if r a then G.target a else G.source a := fun _ => rfl
  have ht : ∀ a, (G.reorient r).target a = if r a then G.source a else G.target a := fun _ => rfl
  have hsi : ∀ a, G.source a = if r a then (G.reorient r).target a else (G.reorient r).source a := by
    intro a; cases hr : r a <;> simp [CellGraph.reorient,hr]
  have hti : ∀ a, G.target a = if r a then (G.reorient r).source a else (G.reorient r).target a := by
    intro a; cases hr : r a <;> simp [CellGraph.reorient,hr]
  exact {
    toFun := reorientMap G (G.reorient r) r hs ht
    invFun := reorientMap (G.reorient r) G r hsi hti
    left_inv := by
      intro q
      induction q using Quot.inductionOn with
      | h p =>
        rcases p with v | ⟨a,t⟩
        · rfl
        · cases hr : r a <;> simp [reorientMap,rawReorient,hr]
    right_inv := by
      intro q
      induction q using Quot.inductionOn with
      | h p =>
        rcases p with v | ⟨a,t⟩
        · rfl
        · cases hr : r a <;> simp [reorientMap,rawReorient,hr]
    continuous_toFun := continuous_reorientMap G (G.reorient r) r hs ht
    continuous_invFun := continuous_reorientMap (G.reorient r) G r hsi hti
  }

#print axioms cellReorientationHomeomorph
end
end P4110Geometry
