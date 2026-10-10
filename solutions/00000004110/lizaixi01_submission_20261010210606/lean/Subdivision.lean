import Reorientation
import Mathlib.Data.Finite.Sum

namespace P4110Subdivision
open P4110Geometry P4110
noncomputable section

/-- Finite graph presentations: discrete vertices, edge labels and actual endpoint maps. -/
structure GraphPresentation where
  Vertex : Type
  Edge : Type
  vertexTopology : TopologicalSpace Vertex
  vertexDiscrete : @DiscreteTopology Vertex vertexTopology
  vertexFinite : Finite Vertex
  edgeFinite : Finite Edge
  cell : CellGraph Vertex Edge

instance (G : GraphPresentation) : TopologicalSpace G.Vertex := G.vertexTopology
instance (G : GraphPresentation) : DiscreteTopology G.Vertex := G.vertexDiscrete
instance (G : GraphPresentation) : Finite G.Vertex := G.vertexFinite
instance (G : GraphPresentation) : Finite G.Edge := G.edgeFinite

abbrev GraphPresentation.realization (G : GraphPresentation) := CellRealization G.cell

/-- Add a vertex inside an actual selected edge, splitting its closed interval into two. -/
def GraphPresentation.insert (G : GraphPresentation) (a : G.Edge) : GraphPresentation where
  Vertex := G.Vertex ⊕ Unit
  Edge := G.Edge ⊕ Unit
  vertexTopology := inferInstance
  vertexDiscrete := inferInstance
  vertexFinite := inferInstance
  edgeFinite := inferInstance
  cell := @CellGraph.subdivideOne G.Vertex G.Edge (Classical.decEq _) G.cell a

/-- Presentation identity preserves both endpoints under bijective vertex/edge relabeling. -/
structure PresentationIso (G H : GraphPresentation) where
  vertex : G.Vertex ≃ H.Vertex
  edge : G.Edge ≃ H.Edge
  source_eq : ∀ a, vertex (G.cell.source a) = H.cell.source (edge a)
  target_eq : ∀ a, vertex (G.cell.target a) = H.cell.target (edge a)

def PresentationIso.realizationHomeomorph {G H : GraphPresentation} (h : PresentationIso G H) :
    G.realization ≃ₜ H.realization :=
  cellRelabelingHomeomorph G.cell H.cell h.vertex h.edge h.source_eq h.target_eq

def GraphPresentation.insertHomeomorph (G : GraphPresentation) (a : G.Edge) :
    G.realization ≃ₜ (G.insert a).realization := by
  letI : DecidableEq G.Edge := Classical.decEq _
  exact cellSubdivisionHomeomorph G.cell a

/-- Edge orientations are only choices of graph-cell presentation. -/
def GraphPresentation.reorient (G : GraphPresentation) (r : G.Edge → Bool) :
    GraphPresentation where
  Vertex := G.Vertex
  Edge := G.Edge
  vertexTopology := G.vertexTopology
  vertexDiscrete := G.vertexDiscrete
  vertexFinite := G.vertexFinite
  edgeFinite := G.edgeFinite
  cell := G.cell.reorient r

def GraphPresentation.reorientHomeomorph (G : GraphPresentation) (r : G.Edge → Bool) :
    G.realization ≃ₜ (G.reorient r).realization :=
  cellReorientationHomeomorph G.cell r

/-- The finite closure of edge insertions and actual graph-presentation relabelings.
The natural-number index counts insertions, so positive index means proper subdivision. -/
inductive Subdivision : GraphPresentation → GraphPresentation → ℕ → Prop
  | refl (G) : Subdivision G G 0
  | insert (G) (a : G.Edge) : Subdivision G (G.insert a) 1
  | relabel {G H} (h : PresentationIso G H) : Subdivision G H 0
  | reorient (G) (r : G.Edge → Bool) : Subdivision G (G.reorient r) 0
  | trans {G H K m n} : Subdivision G H m → Subdivision H K n → Subdivision G K (m+n)

/-- Identity of underlying undirected graph presentations: every edge's unordered
endpoint pair is preserved by the actual bijections. -/
structure UndirectedPresentationIso (G H : GraphPresentation) where
  vertex : G.Vertex ≃ H.Vertex
  edge : G.Edge ≃ H.Edge
  endpoints : ∀ a,
    (vertex (G.cell.source a) = H.cell.source (edge a) ∧
      vertex (G.cell.target a) = H.cell.target (edge a)) ∨
    (vertex (G.cell.source a) = H.cell.target (edge a) ∧
      vertex (G.cell.target a) = H.cell.source (edge a))

theorem presentation_identity_subdivision {G H : GraphPresentation}
    (h : UndirectedPresentationIso G H) : Subdivision G H 0 := by
  classical
  let r : G.Edge → Bool := fun a =>
    if h.vertex (G.cell.source a) = H.cell.source (h.edge a) ∧
      h.vertex (G.cell.target a) = H.cell.target (h.edge a) then false else true
  have hi : PresentationIso (G.reorient r) H := {
    vertex := h.vertex
    edge := h.edge
    source_eq := by
      intro a
      change h.vertex (if r a then G.cell.target a else G.cell.source a) = H.cell.source (h.edge a)
      by_cases hd : h.vertex (G.cell.source a) = H.cell.source (h.edge a) ∧
          h.vertex (G.cell.target a) = H.cell.target (h.edge a)
      · have hr : r a = false := by simp only [r,if_pos hd]
        rw [hr]
        exact hd.1
      · have hx := (h.endpoints a).resolve_left hd
        have hr : r a = true := by simp only [r,if_neg hd]
        rw [hr]
        exact hx.2
    target_eq := by
      intro a
      change h.vertex (if r a then G.cell.source a else G.cell.target a) = H.cell.target (h.edge a)
      by_cases hd : h.vertex (G.cell.source a) = H.cell.source (h.edge a) ∧
          h.vertex (G.cell.target a) = H.cell.target (h.edge a)
      · have hr : r a = false := by simp only [r,if_pos hd]
        rw [hr]
        exact hd.2
      · have hx := (h.endpoints a).resolve_left hd
        have hr : r a = true := by simp only [r,if_neg hd]
        rw [hr]
        exact hx.1
  }
  simpa using Subdivision.trans (Subdivision.reorient G r) (Subdivision.relabel hi)

theorem subdivision_homeomorphic {G H : GraphPresentation} {k : ℕ}
    (h : Subdivision G H k) : Nonempty (G.realization ≃ₜ H.realization) := by
  induction h with
  | refl G => exact ⟨Homeomorph.refl _⟩
  | insert G a => exact ⟨G.insertHomeomorph a⟩
  | relabel h => exact ⟨h.realizationHomeomorph⟩
  | reorient G r => exact ⟨G.reorientHomeomorph r⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.some.trans ih₂.some⟩

def subdivisionHomeomorph {G H : GraphPresentation} {k : ℕ}
    (h : Subdivision G H k) : G.realization ≃ₜ H.realization :=
  (subdivision_homeomorphic h).some

def orderedSubdivisionHomeomorph {G H : GraphPresentation} {k : ℕ}
    (h : Subdivision G H k) (n : ℕ) :
    OrderedConfig n G.realization ≃ₜ OrderedConfig n H.realization :=
  orderedConfigHomeomorph n (subdivisionHomeomorph h)

def unorderedSubdivisionHomeomorph {G H : GraphPresentation} {k : ℕ}
    (h : Subdivision G H k) (n : ℕ) :
    UnorderedConfig n G.realization ≃ₜ UnorderedConfig n H.realization :=
  unorderedConfigHomeomorph n (subdivisionHomeomorph h)

#print axioms subdivisionHomeomorph
#print axioms orderedSubdivisionHomeomorph
#print axioms unorderedSubdivisionHomeomorph
end
end P4110Subdivision
