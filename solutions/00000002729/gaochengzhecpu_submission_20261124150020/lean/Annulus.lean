import Std

namespace C2729

private instance decidableFinForall {n : Nat} {P : Fin n → Prop}
    [dec : (i : Fin n) → Decidable (P i)] : Decidable (∀ i, P i) := by
  induction n with
  | zero => exact isTrue (fun i => Fin.elim0 i)
  | succ n ih =>
      letI : Decidable (∀ i : Fin n, P i.succ) := ih
      exact decidable_of_iff _ Fin.forall_fin_succ.symm

private instance decidableFinExists {n : Nat} {P : Fin n → Prop}
    [dec : (i : Fin n) → Decidable (P i)] : Decidable (∃ i, P i) := by
  induction n with
  | zero => exact isFalse (fun ⟨i, _⟩ => Fin.elim0 i)
  | succ n ih =>
      letI : Decidable (∃ i : Fin n, P i.succ) := ih
      exact decidable_of_iff _ Fin.exists_fin_succ.symm

abbrev Vertex := Fin 6
abbrev Edge := Vertex × Vertex
abbrev Triangle := Vertex × Vertex × Vertex
abbrev FacetIndex := Fin 6
abbrev Facets := FacetIndex → Triangle

def triangleVertices (t : Triangle) : List Vertex := [t.1, t.2.1, t.2.2]

def triangleEdges (t : Triangle) : List Edge :=
  [(t.1, t.2.1), (t.1, t.2.2), (t.2.1, t.2.2)]

def edge (x y : Vertex) : Edge := if x ≤ y then (x, y) else (y, x)

def sortedFacets (facets : Facets) : Prop :=
  ∀ i, (facets i).1 < (facets i).2.1 ∧ (facets i).2.1 < (facets i).2.2

def fullVertexSet (facets : Facets) : Prop :=
  ∀ v, ∃ i, v ∈ triangleVertices (facets i)

def adjacency (facets : Facets) (x y : Vertex) : Prop :=
  ∃ i, edge x y ∈ triangleEdges (facets i)

def linkAdjacency (facets : Facets) (v x y : Vertex) : Prop :=
  v ≠ x ∧ v ≠ y ∧ ∃ i, v ∈ triangleVertices (facets i) ∧
    edge x y ∈ triangleEdges (facets i)

inductive Walk (adj : Vertex → Vertex → Prop) : Vertex → Vertex → Prop
  | stay (v : Vertex) : Walk adj v v
  | step {x y z : Vertex} : adj x y → Walk adj y z → Walk adj x z

def connected (facets : Facets) : Prop := ∀ x y, Walk (adjacency facets) x y

/-- For the link of a vertex of a pure two-dimensional complex, the graph
criterion for Cohen–Macaulayness is that it is nonempty and connected. -/
def vertexLinksCM (facets : Facets) : Prop :=
  ∀ v, (∃ x y, linkAdjacency facets v x y) ∧
    ∀ x y, adjacency facets v x → adjacency facets v y →
      Walk (linkAdjacency facets v) x y

def edgeLinksNonempty (facets : Facets) : Prop :=
  ∀ x y, adjacency facets x y → ∃ v, linkAdjacency facets v x y

private def ThreeSteps (adj : Vertex → Vertex → Prop) (x y : Vertex) : Prop :=
  ∃ a b, (x = a ∨ adj x a) ∧ (a = b ∨ adj a b) ∧ (b = y ∨ adj b y)

private theorem threeSteps_walk {adj : Vertex → Vertex → Prop} {x y : Vertex}
    (h : ThreeSteps adj x y) : Walk adj x y := by
  obtain ⟨a, b, hxa, hab, hby⟩ := h
  have prepend {s t u : Vertex} (hst : s = t ∨ adj s t) (htu : Walk adj t u) :
      Walk adj s u := by
    rcases hst with rfl | hst
    · exact htu
    · exact Walk.step hst htu
  exact prepend hxa (prepend hab (prepend hby (Walk.stay y)))

def annulus (i : FacetIndex) : Triangle :=
  let table : Array Triangle :=
    #[(0, 1, 4), (0, 3, 4), (1, 2, 5), (1, 4, 5), (0, 2, 3), (2, 3, 5)]
  table[i.val]'(i.isLt)

theorem annulus_sorted : sortedFacets annulus := by
  unfold sortedFacets
  decide

theorem annulus_full : fullVertexSet annulus := by
  unfold fullVertexSet
  decide

private instance (f : Facets) (x y : Vertex) : Decidable (adjacency f x y) := by
  unfold adjacency
  infer_instance

private instance (f : Facets) (v x y : Vertex) : Decidable (linkAdjacency f v x y) := by
  unfold linkAdjacency
  infer_instance

private instance (adj : Vertex → Vertex → Prop) [∀ x y, Decidable (adj x y)]
    (x y : Vertex) : Decidable (ThreeSteps adj x y) := by
  unfold ThreeSteps
  infer_instance

theorem annulus_connected : connected annulus := by
  have h : ∀ x y, ThreeSteps (adjacency annulus) x y := by decide
  exact fun x y => threeSteps_walk (h x y)

theorem annulus_vertexLinksCM : vertexLinksCM annulus := by
  have nonempty : ∀ v, ∃ x y, linkAdjacency annulus v x y := by decide
  have paths : ∀ v x y, adjacency annulus v x → adjacency annulus v y →
      ThreeSteps (linkAdjacency annulus v) x y := by decide
  exact fun v => ⟨nonempty v, fun x y hx hy => threeSteps_walk (paths v x y hx hy)⟩

theorem annulus_edgeLinksNonempty : edgeLinksNonempty annulus := by
  unfold edgeLinksNonempty
  decide

/-- A list represents the chain whose coefficients are the multiplicities mod 2. -/
def coefficient {α : Type} [BEq α] (a : α) (chain : List α) : Nat :=
  chain.count a % 2

def boundaryOne (chain : List Edge) : List Vertex :=
  chain.flatMap fun (x, y) => [x, y]

def boundaryTwo (facets : Facets) (chain : List FacetIndex) : List Edge :=
  chain.flatMap fun i => triangleEdges (facets i)

def isCycle (chain : List Edge) : Prop := ∀ v, coefficient v (boundaryOne chain) = 0

def isSupported (facets : Facets) (chain : List Edge) : Prop :=
  ∀ e ∈ chain, ∃ i, e ∈ triangleEdges (facets i)

def sameEdgeChain (left right : List Edge) : Prop :=
  ∀ e : Edge, coefficient e left = coefficient e right

def firstHomologyVanishes (facets : Facets) : Prop :=
  ∀ chain, isSupported facets chain → isCycle chain →
    ∃ filling, sameEdgeChain chain (boundaryTwo facets filling)

/-- Reisner's criterion over F₂ for pure two-dimensional complexes with the
given vertex set. The facet links impose no condition. -/
def cohenMacaulayF2 (facets : Facets) : Prop :=
  connected facets ∧ vertexLinksCM facets ∧ edgeLinksNonempty facets ∧
    firstHomologyVanishes facets

def outerBoundary : List Edge := [(0, 1), (1, 2), (0, 2)]

theorem outerBoundary_supported : isSupported annulus outerBoundary := by
  unfold isSupported outerBoundary
  intro e h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · exact ⟨0, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨4, by decide⟩

theorem outerBoundary_cycle : isCycle outerBoundary := by
  unfold isCycle
  decide

def seamEvaluation (chain : List Edge) : Nat :=
  (coefficient (0, 2) chain + coefficient (2, 3) chain + coefficient (3, 5) chain) % 2

private theorem seamEvaluation_append (left right : List Edge) :
    seamEvaluation (left ++ right) = (seamEvaluation left + seamEvaluation right) % 2 := by
  unfold seamEvaluation coefficient
  simp only [List.count_append]
  omega

private theorem seamEvaluation_facet :
    ∀ i, seamEvaluation (triangleEdges (annulus i)) = 0 := by decide

theorem seamEvaluation_boundary (chain : List FacetIndex) :
    seamEvaluation (boundaryTwo annulus chain) = 0 := by
  induction chain with
  | nil => decide
  | cons i rest ih =>
      unfold boundaryTwo at *
      rw [List.flatMap_cons, seamEvaluation_append, seamEvaluation_facet i, ih]

theorem annulus_firstHomology_nonzero : ¬ firstHomologyVanishes annulus := by
  intro h
  obtain ⟨filling, hfilling⟩ := h outerBoundary outerBoundary_supported outerBoundary_cycle
  have hEval : seamEvaluation outerBoundary = seamEvaluation (boundaryTwo annulus filling) := by
    unfold seamEvaluation
    rw [hfilling (0, 2), hfilling (2, 3), hfilling (3, 5)]
  have hOuter : seamEvaluation outerBoundary = 1 := by decide
  rw [seamEvaluation_boundary filling, hOuter] at hEval
  contradiction

/-- Refutes the proposed local-to-global implication even on six vertices and six facets. -/
theorem counterexample :
    ∃ facets : Facets, sortedFacets facets ∧ fullVertexSet facets ∧
      connected facets ∧ vertexLinksCM facets ∧ edgeLinksNonempty facets ∧
      ¬ cohenMacaulayF2 facets := by
  exact ⟨annulus, annulus_sorted, annulus_full, annulus_connected, annulus_vertexLinksCM,
    annulus_edgeLinksNonempty, fun h => annulus_firstHomology_nonzero h.2.2.2⟩

theorem not_localCriterion :
    ¬ (∀ facets : Facets, sortedFacets facets → fullVertexSet facets →
      (cohenMacaulayF2 facets ↔ connected facets ∧ vertexLinksCM facets)) := by
  intro criterion
  obtain ⟨facets, sorted, full, connect, links, _, notCM⟩ := counterexample
  exact notCM ((criterion facets sorted full).mpr ⟨connect, links⟩)

#print axioms not_localCriterion

end C2729
