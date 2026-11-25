import Std

namespace C4113

private instance decidableFinForall {n : Nat} {P : Fin n → Prop}
    [dec : (i : Fin n) → Decidable (P i)] : Decidable (∀ i, P i) := by
  induction n with
  | zero => exact isTrue (fun i => Fin.elim0 i)
  | succ n ih =>
    letI : Decidable (∀ i : Fin n, P i.succ) := ih
    exact decidable_of_iff _ Fin.forall_fin_succ.symm

abbrev Vertex := Fin 3
abbrev Edge := Fin 3

/-- Each edge is indexed by the vertex absent from its endpoints. -/
def ends (i : Edge) : Vertex × Vertex :=
  if i = 0 then (1, 2) else if i = 1 then (0, 2) else (0, 1)

def orderPair (u v : Vertex) : Vertex × Vertex := if u ≤ v then (u, v) else (v, u)

def adjacent (u v : Vertex) : Prop := ∃ i, orderPair u v = ends i

def HasThreeCycle : Prop :=
  ∃ a b c : Vertex, a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ adjacent a b ∧ adjacent b c ∧ adjacent c a

theorem original_has_cycle : HasThreeCycle := by
  exact ⟨0, 1, 2, by decide, by decide, by decide,
    ⟨2, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩⟩

inductive Cell where
  | vertex (v : Vertex)
  | edge (e : Edge)

def closureVertices : Cell → List Vertex
  | .vertex v => [v]
  | .edge e => [(ends e).1, (ends e).2]

def disjointClosures (a b : Cell) : Bool :=
  (closureVertices a).all fun v => !(closureVertices b).contains v

theorem vertex_pairs_disjoint : ∀ u v : Vertex,
    disjointClosures (.vertex u) (.vertex v) = true ↔ u ≠ v := by decide

theorem edge_vertex_disjoint : ∀ (e : Edge) (v : Vertex),
    disjointClosures (.edge e) (.vertex v) = true ↔ v = e := by decide

theorem no_square_cells : ∀ e f : Edge,
    disjointClosures (.edge e) (.edge f) = false := by decide

/-- Sorted representatives of unordered pairs of distinct vertices. -/
abbrev UDVertex := {pair : Vertex × Vertex // pair.1 < pair.2}

/-- The edge factor comes first in each unordered edge--vertex cell. -/
abbrev UDEdge := {pair : Edge × Vertex //
  disjointClosures (.edge pair.1) (.vertex pair.2) = true}

def missingVertex (p : Vertex × Vertex) : Vertex :=
  if p = (1, 2) then 0 else if p = (0, 2) then 1 else 2

def vertexToCycle (v : UDVertex) : Vertex := missingVertex v.val

private theorem ends_ordered : ∀ i : Edge, (ends i).1 < (ends i).2 := by decide

def vertexFromCycle (v : Vertex) : UDVertex := ⟨ends v, ends_ordered v⟩

theorem vertex_to_from : ∀ v : Vertex, vertexToCycle (vertexFromCycle v) = v := by decide

theorem vertex_from_to (v : UDVertex) : vertexFromCycle (vertexToCycle v) = v := by
  have checked : ∀ a b : Vertex, a < b → ends (missingVertex (a, b)) = (a, b) := by decide
  exact Subtype.ext (checked v.val.1 v.val.2 v.property)

def edgeToCycle (e : UDEdge) : Edge := e.val.1

def edgeFromCycle (e : Edge) : UDEdge :=
  ⟨(e, e), (edge_vertex_disjoint e e).mpr rfl⟩

theorem edge_to_from (e : Edge) : edgeToCycle (edgeFromCycle e) = e := rfl

theorem edge_from_to (e : UDEdge) : edgeFromCycle (edgeToCycle e) = e := by
  have remaining := (edge_vertex_disjoint e.val.1 e.val.2).mp e.property
  apply Subtype.ext
  exact Prod.ext rfl remaining.symm

def endVertex (e : Edge) (last : Bool) : Vertex :=
  if last then (ends e).2 else (ends e).1

private theorem orderPair_strict : ∀ u v : Vertex,
    u ≠ v → (orderPair u v).1 < (orderPair u v).2 := by decide

private theorem missing_not_endpoint : ∀ e : Edge,
    e ≠ endVertex e false ∧ e ≠ endVertex e true := by decide

def endpoint (e : UDEdge) (last : Bool) : UDVertex := by
  have remaining := (edge_vertex_disjoint e.val.1 e.val.2).mp e.property
  refine ⟨orderPair e.val.2 (endVertex e.val.1 last), orderPair_strict _ _ ?_⟩
  rw [remaining]
  cases last
  · exact (missing_not_endpoint e.val.1).1
  · exact (missing_not_endpoint e.val.1).2

/-- The incidence of the unordered configuration graph agrees with the original cycle.
The chosen labels reverse the two endpoints of each edge. -/
theorem incidence (e : UDEdge) :
    (vertexToCycle (endpoint e false), vertexToCycle (endpoint e true)) =
      ((ends (edgeToCycle e)).2, (ends (edgeToCycle e)).1) := by
  have verified : ∀ i : Edge,
      (missingVertex (orderPair i (endVertex i false)),
        missingVertex (orderPair i (endVertex i true))) = ((ends i).2, (ends i).1) := by decide
  have remaining := (edge_vertex_disjoint e.val.1 e.val.2).mp e.property
  change (missingVertex (orderPair e.val.2 (endVertex e.val.1 false)),
    missingVertex (orderPair e.val.2 (endVertex e.val.1 true))) = ((ends e.val.1).2, (ends e.val.1).1)
  rw [remaining]
  exact verified e.val.1

theorem cycle_configuration_certificate :
    HasThreeCycle ∧
    (∀ e f : Edge, disjointClosures (.edge e) (.edge f) = false) ∧
    (∀ v : Vertex, vertexToCycle (vertexFromCycle v) = v) ∧
    (∀ v : UDVertex, vertexFromCycle (vertexToCycle v) = v) ∧
    (∀ e : Edge, edgeToCycle (edgeFromCycle e) = e) ∧
    (∀ e : UDEdge, edgeFromCycle (edgeToCycle e) = e) ∧
    (∀ e : UDEdge,
      (vertexToCycle (endpoint e false), vertexToCycle (endpoint e true)) =
        ((ends (edgeToCycle e)).2, (ends (edgeToCycle e)).1)) := by
  exact ⟨original_has_cycle, no_square_cells, vertex_to_from, vertex_from_to,
    edge_to_from, edge_from_to, incidence⟩

#print axioms cycle_configuration_certificate

end C4113
