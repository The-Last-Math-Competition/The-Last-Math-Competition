import Std

namespace Conjecture2731

abbrev Edge (vertices : Nat) := Fin vertices × Fin vertices

/-- All vertices belong to the complex. Edges are distinct and have canonically
    ordered distinct endpoints. These data specify all faces of size at most two. -/
structure Complex1 (vertices : Nat) where
  edges : List (Edge vertices)
  ordered : ∀ e ∈ edges, e.1 < e.2
  distinct : edges.Nodup

inductive Face {n : Nat} (complex : Complex1 n) : List (Fin n) → Prop where
  | empty : Face complex []
  | vertex (v : Fin n) : Face complex [v]
  | edge {e : Edge n} (member : e ∈ complex.edges) : Face complex [e.1, e.2]

def DimensionPreserving {n k : Nat} (complex : Complex1 n)
    (vertexMap : Fin n → Fin k) : Prop :=
  ∀ e ∈ complex.edges, vertexMap e.1 ≠ vertexMap e.2

/-- The image contains the whole simplex if a single source face maps onto its
    full vertex set. Permutation ignores the order used to list that face. -/
def OntoSimplex {n k : Nat} (complex : Complex1 n) (vertexMap : Fin n → Fin k) : Prop :=
  DimensionPreserving complex vertexMap ∧
    ∃ face, Face complex face ∧ (face.map vertexMap).Perm (List.finRange k)

def HasOntoSimplex {n : Nat} (complex : Complex1 n) (k : Nat) : Prop :=
  ∃ vertexMap : Fin n → Fin k, OntoSimplex complex vertexMap

def HasChromaticNumber {n : Nat} (complex : Complex1 n) (k : Nat) : Prop :=
  (∃ coloring : Fin n → Fin k, DimensionPreserving complex coloring) ∧
    ∀ j < k, ¬ ∃ coloring : Fin n → Fin j, DimensionPreserving complex coloring

theorem chromatic_number_unique {n a b : Nat} {complex : Complex1 n}
    (first : HasChromaticNumber complex a) (second : HasChromaticNumber complex b) : a = b := by
  by_cases before : a < b
  · exact False.elim (second.2 a before first.1)
  by_cases after : b < a
  · exact False.elim (first.2 b after second.1)
  omega

theorem target_is_one_simplex {n k : Nat} {complex : Complex1 n}
    {vertexMap : Fin n → Fin k} (edgeExists : ∃ e, e ∈ complex.edges)
    (onto : OntoSimplex complex vertexMap) : k = 2 := by
  obtain ⟨e, member⟩ := edgeExists
  have different := onto.1 e member
  have leftBound := (vertexMap e.1).isLt
  have rightBound := (vertexMap e.2).isLt
  have differentValues : (vertexMap e.1).val ≠ (vertexMap e.2).val :=
    fun same => different (Fin.ext same)
  obtain ⟨face, isFace, image⟩ := onto.2
  have lengths := image.length_eq
  simp only [List.length_map, List.length_finRange] at lengths
  have small : face.length ≤ 2 := by
    cases isFace <;> simp only [List.length_nil, List.length_cons] <;> omega
  omega

private theorem fin_two_cases (color : Fin 2) : color = 0 ∨ color = 1 := by
  have isLt := color.isLt
  by_cases zero : color.val = 0
  · exact Or.inl (Fin.ext zero)
  · right
    apply Fin.ext
    change color.val = 1
    omega

theorem proper_two_coloring_is_onto {n : Nat} {complex : Complex1 n}
    (edgeExists : ∃ e, e ∈ complex.edges) {coloring : Fin n → Fin 2}
    (proper : DimensionPreserving complex coloring) : OntoSimplex complex coloring := by
  obtain ⟨e, member⟩ := edgeExists
  have distinct := proper e member
  refine ⟨proper, [e.1, e.2], Face.edge member, ?_⟩
  change [coloring e.1, coloring e.2].Perm [(0 : Fin 2), 1]
  rcases fin_two_cases (coloring e.1) with leftZero | leftOne <;>
    rcases fin_two_cases (coloring e.2) with rightZero | rightOne
  · exact False.elim (distinct (leftZero.trans rightZero.symm))
  · rw [leftZero, rightOne]
  · rw [leftOne, rightZero]
    exact List.Perm.swap _ _ _
  · exact False.elim (distinct (leftOne.trans rightOne.symm))

def fVector {n : Nat} (complex : Complex1 n) : Nat × Nat := (n, complex.edges.length)

def hVector {n : Nat} (complex : Complex1 n) : List Int :=
  let (vertices, edges) := fVector complex
  [1, (vertices : Int) - 2, (edges : Int) - (vertices : Int) + 1]

def cycleEdges : List (Edge 4) := [(0, 1), (1, 2), (2, 3), (0, 3)]

def trianglePendantEdges : List (Edge 4) := [(0, 1), (0, 2), (1, 2), (2, 3)]

private theorem cycle_edge_cases {e : Edge 4} (member : e ∈ cycleEdges) :
    e = (0, 1) ∨ e = (1, 2) ∨ e = (2, 3) ∨ e = (0, 3) := by
  simpa only [cycleEdges, List.mem_cons, List.not_mem_nil, or_false] using member

private theorem triangle_pendant_edge_cases {e : Edge 4} (member : e ∈ trianglePendantEdges) :
    e = (0, 1) ∨ e = (0, 2) ∨ e = (1, 2) ∨ e = (2, 3) := by
  simpa only [trianglePendantEdges, List.mem_cons, List.not_mem_nil, or_false] using member

def cycleFour : Complex1 4 where
  edges := cycleEdges
  ordered := by
    intro e member
    rcases cycle_edge_cases member with rfl | rfl | rfl | rfl <;> decide
  distinct := by decide

def trianglePendant : Complex1 4 where
  edges := trianglePendantEdges
  ordered := by
    intro e member
    rcases triangle_pendant_edge_cases member with rfl | rfl | rfl | rfl <;> decide
  distinct := by decide

/-- The path 0–1–2–3 witnesses connectivity and covers every vertex. -/
def HasSpanningPath (complex : Complex1 4) : Prop :=
  (0, 1) ∈ complex.edges ∧ (1, 2) ∈ complex.edges ∧ (2, 3) ∈ complex.edges

theorem cycle_spanning_path : HasSpanningPath cycleFour := by
  unfold HasSpanningPath
  decide

theorem triangle_pendant_spanning_path : HasSpanningPath trianglePendant := by
  unfold HasSpanningPath
  decide

private def colorMod {k : Nat} (positive : 0 < k) (v : Fin 4) : Fin k :=
  ⟨v.val % k, Nat.mod_lt _ positive⟩

theorem cycle_two_coloring : DimensionPreserving cycleFour (colorMod (by decide : 0 < 2)) := by
  intro e member
  rcases cycle_edge_cases member with rfl | rfl | rfl | rfl <;> decide

theorem triangle_pendant_three_coloring :
    DimensionPreserving trianglePendant (colorMod (by decide : 0 < 3)) := by
  intro e member
  rcases triangle_pendant_edge_cases member with rfl | rfl | rfl | rfl <;> decide

theorem cycle_chromatic_number : HasChromaticNumber cycleFour 2 := by
  refine ⟨⟨_, cycle_two_coloring⟩, ?_⟩
  intro k small ⟨f, proper⟩
  have different := proper (0, 1) (by decide)
  have leftBound := (f 0).isLt
  have rightBound := (f 1).isLt
  exact different (Fin.ext (by omega))

theorem triangle_pendant_chromatic_number : HasChromaticNumber trianglePendant 3 := by
  refine ⟨⟨_, triangle_pendant_three_coloring⟩, ?_⟩
  intro k small ⟨f, proper⟩
  have ne01 : (f 0).val ≠ (f 1).val := fun same => proper (0, 1) (by decide) (Fin.ext same)
  have ne02 : (f 0).val ≠ (f 2).val := fun same => proper (0, 2) (by decide) (Fin.ext same)
  have ne12 : (f 1).val ≠ (f 2).val := fun same => proper (1, 2) (by decide) (Fin.ext same)
  have b0 := (f 0).isLt
  have b1 := (f 1).isLt
  have b2 := (f 2).isLt
  omega

theorem both_h_vectors : hVector cycleFour = [1, 2, 1] ∧
    hVector trianglePendant = [1, 2, 1] := by decide

theorem cycle_onto_one_simplex : HasOntoSimplex cycleFour 2 :=
  ⟨_, proper_two_coloring_is_onto ⟨(0, 1), by decide⟩ cycle_two_coloring⟩

theorem triangle_pendant_no_onto_simplex (k : Nat) : ¬ HasOntoSimplex trianglePendant k := by
  intro ⟨vertexMap, onto⟩
  have hk := target_is_one_simplex ⟨(0, 1), by decide⟩ onto
  subst k
  exact triangle_pendant_chromatic_number.2 2 (by decide) ⟨vertexMap, onto.1⟩

theorem no_h_vector_criterion :
    ¬ ∃ criterion : List Int → Prop, ∀ complex : Complex1 4,
      HasSpanningPath complex → (criterion (hVector complex) ↔ (∃ k, HasOntoSimplex complex k)) := by
  intro ⟨criterion, correct⟩
  have trueForCycle := (correct cycleFour cycle_spanning_path).2 ⟨2, cycle_onto_one_simplex⟩
  rw [both_h_vectors.1] at trueForCycle
  have trueForTriangle : criterion (hVector trianglePendant) := by
    rw [both_h_vectors.2]
    exact trueForCycle
  obtain ⟨k, onto⟩ := (correct trianglePendant triangle_pendant_spanning_path).1 trueForTriangle
  exact triangle_pendant_no_onto_simplex k onto

theorem no_h_vector_chromatic_formula :
    ¬ ∃ formula : List Int → Nat, ∀ complex : Complex1 4,
      HasSpanningPath complex → HasChromaticNumber complex (formula (hVector complex)) := by
  intro ⟨formula, correct⟩
  have cycleValue := chromatic_number_unique
    (correct cycleFour cycle_spanning_path) cycle_chromatic_number
  have triangleValue := chromatic_number_unique
    (correct trianglePendant triangle_pendant_spanning_path) triangle_pendant_chromatic_number
  rw [both_h_vectors.1] at cycleValue
  rw [both_h_vectors.2] at triangleValue
  omega

end Conjecture2731

#print axioms Conjecture2731.cycle_chromatic_number
#print axioms Conjecture2731.triangle_pendant_chromatic_number
#print axioms Conjecture2731.cycle_onto_one_simplex
#print axioms Conjecture2731.triangle_pendant_no_onto_simplex
#print axioms Conjecture2731.no_h_vector_criterion
#print axioms Conjecture2731.no_h_vector_chromatic_formula
