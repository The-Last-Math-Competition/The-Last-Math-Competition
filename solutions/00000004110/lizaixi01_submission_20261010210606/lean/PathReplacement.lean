import Disproof

namespace P4110Paths
open P4110Geometry P4110Subdivision P4110Disproof P4110
noncomputable section
set_option backward.isDefEq.respectTransparency false

def extendLabels (A : Type) (k : ℕ) : (A ⊕ Fin k) ⊕ Unit ≃ A ⊕ Fin (k+1) where
  toFun := Sum.elim (Sum.elim Sum.inl (fun j => .inr j.succ)) (fun _ => .inr 0)
  invFun := Sum.elim (fun a => .inl (.inl a))
    (Fin.cases (.inr ()) (fun j => .inl (.inr j)))
  left_inv := by
    rintro ((a | j) | u)
    · rfl
    · simp
    · cases u; rfl
  right_inv := by
    rintro (a | j)
    · rfl
    · induction j using Fin.cases with
      | zero => rfl
      | succ j => simp

def emptyLabels (A : Type) : A ≃ A ⊕ Fin 0 where
  toFun := Sum.inl
  invFun := Sum.elim id Fin.elim0
  left_inv := fun _ => rfl
  right_inv := by rintro (a | j); rfl; exact Fin.elim0 j

@[simp] theorem emptyLabels_apply (A : Type) (a : A) : emptyLabels A a = Sum.inl a := rfl
@[simp] theorem extendLabels_old (A : Type) (k : ℕ) (a : A) :
    extendLabels A k (.inl (.inl a)) = .inl a := rfl
@[simp] theorem extendLabels_fresh (A : Type) (k : ℕ) (j : Fin k) :
    extendLabels A k (.inl (.inr j)) = .inr j.succ := rfl
@[simp] theorem extendLabels_new (A : Type) (k : ℕ) :
    extendLabels A k (.inr ()) = .inr 0 := rfl

/-- Replace the selected edge by a path with k fresh interior vertices and k+1 edges.
Its old edge label is the first path edge; fresh labels are the following edges. -/
def _root_.P4110Geometry.CellGraph.replaceEdge {V E : Type} [DecidableEq E]
    (G : CellGraph V E) (e : E) (k : ℕ) : CellGraph (V ⊕ Fin k) (E ⊕ Fin k) where
  source := Sum.elim (fun f => .inl (G.source f)) (fun j => .inr j)
  target := Sum.elim
    (fun f => if f=e then
      if h : 0<k then .inr ⟨0,h⟩ else .inl (G.target e)
      else .inl (G.target f))
    (fun j => if h : j.1+1<k then .inr ⟨j.1+1,h⟩ else .inl (G.target e))

abbrev _root_.P4110Subdivision.GraphPresentation.replaceEdge (G : GraphPresentation) (e : G.Edge) (k : ℕ) :
    GraphPresentation where
  Vertex := G.Vertex ⊕ Fin k
  Edge := G.Edge ⊕ Fin k
  vertexTopology := inferInstance
  vertexDiscrete := inferInstance
  vertexFinite := inferInstance
  edgeFinite := inferInstance
  cell := @CellGraph.replaceEdge G.Vertex G.Edge (Classical.decEq _) G.cell e k

def replaceEdge_zero_iso (G : GraphPresentation) (e : G.Edge) :
    PresentationIso G (G.replaceEdge e 0) where
  vertex := emptyLabels _
  edge := emptyLabels _
  source_eq := fun _ => rfl
  target_eq := by
    intro f
    classical
    dsimp [GraphPresentation.replaceEdge,CellGraph.replaceEdge,emptyLabels]
    by_cases hf : f=e
    · subst f; simp [GraphPresentation.replaceEdge,CellGraph.replaceEdge]
    · simp [GraphPresentation.replaceEdge,CellGraph.replaceEdge,hf]

def replaceEdge_step_iso (G : GraphPresentation) (e : G.Edge) (k : ℕ) :
    PresentationIso ((G.replaceEdge e k).insert (.inl e)) (G.replaceEdge e (k+1)) where
  vertex := extendLabels _ k
  edge := extendLabels _ k
  source_eq := by
    rintro ((f | j) | u)
    · rfl
    · rfl
    · cases u; rfl
  target_eq := by
    classical
    rintro ((f | j) | u)
    · by_cases hf : f=e
      · subst f
        dsimp [GraphPresentation.insert,GraphPresentation.replaceEdge,CellGraph.subdivideOne,
          CellGraph.replaceEdge,extendLabels]
        simp [GraphPresentation.insert,GraphPresentation.replaceEdge,CellGraph.subdivideOne,
          CellGraph.replaceEdge]
      · simp [GraphPresentation.insert,GraphPresentation.replaceEdge,CellGraph.subdivideOne,
          CellGraph.replaceEdge,hf]
    · have hne : Sum.inr j ≠ (Sum.inl e : G.Edge ⊕ Fin k) := by simp
      by_cases hj : j.1+1<k
      · have hj' : (j.succ).1+1<k+1 := by dsimp [Fin.succ]; omega
        dsimp [GraphPresentation.insert,GraphPresentation.replaceEdge,CellGraph.subdivideOne,
          CellGraph.replaceEdge,extendLabels]
        simp [GraphPresentation.insert,GraphPresentation.replaceEdge,CellGraph.subdivideOne,
          CellGraph.replaceEdge,hne,hj,hj',Fin.succ]
      · have hj' : ¬ (j.succ).1+1<k+1 := by dsimp [Fin.succ]; omega
        dsimp [GraphPresentation.insert,GraphPresentation.replaceEdge,CellGraph.subdivideOne,
          CellGraph.replaceEdge,extendLabels]
        simp [GraphPresentation.insert,GraphPresentation.replaceEdge,CellGraph.subdivideOne,
          CellGraph.replaceEdge,hne,hj,hj']
    · cases u
      by_cases hk : 0<k
      · have hk' : (0 : Fin (k+1)).1+1<k+1 := by change 1<k+1; omega
        dsimp [GraphPresentation.insert,GraphPresentation.replaceEdge,CellGraph.subdivideOne,
          CellGraph.replaceEdge,extendLabels]
        simp [GraphPresentation.insert,GraphPresentation.replaceEdge,CellGraph.subdivideOne,
          CellGraph.replaceEdge,hk,hk',Fin.succ]
      · have hk' : ¬ (0 : Fin (k+1)).1+1<k+1 := by change ¬ 1<k+1; omega
        dsimp [GraphPresentation.insert,GraphPresentation.replaceEdge,CellGraph.subdivideOne,
          CellGraph.replaceEdge,extendLabels]
        simp [GraphPresentation.insert,GraphPresentation.replaceEdge,CellGraph.subdivideOne,
          CellGraph.replaceEdge,hk,hk']

theorem path_replacement_is_subdivision (G : GraphPresentation) (e : G.Edge) (k : ℕ) :
    Subdivision G (G.replaceEdge e k) k := by
  induction k with
  | zero => exact Subdivision.relabel (replaceEdge_zero_iso G e)
  | succ k ih =>
    simpa using Subdivision.trans (Subdivision.trans ih
      (Subdivision.insert (G.replaceEdge e k) (.inl e)))
      (Subdivision.relabel (replaceEdge_step_iso G e k))

#print axioms path_replacement_is_subdivision
end
end P4110Paths
