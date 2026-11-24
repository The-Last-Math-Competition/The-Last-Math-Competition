import Std

namespace C4093

abbrev Vertex := Fin 4
abbrev Edge := Vertex × Vertex

def graphEdges (lastNeighbor : Vertex) : List Edge := [(0, 1), (1, 2), (lastNeighbor, 3)]
def pathEdges := graphEdges 2
def starEdges := graphEdges 1

def Proper {Color : Type} (edges : List Edge) (color : Vertex → Color) : Prop :=
  ∀ edge ∈ edges, color edge.1 ≠ color edge.2

abbrev Coloring (edges : List Edge) (Color : Type) :=
  {color : Vertex → Color // Proper edges color}

private theorem proper_iff {Color : Type} (lastNeighbor : Vertex) (color : Vertex → Color) :
    Proper (graphEdges lastNeighbor) color ↔
      color 0 ≠ color 1 ∧ color 1 ≠ color 2 ∧ color lastNeighbor ≠ color 3 := by
  constructor
  · intro proper
    exact ⟨proper (0, 1) (by simp [graphEdges]), proper (1, 2) (by simp [graphEdges]),
      proper (lastNeighbor, 3) (by simp [graphEdges])⟩
  · rintro ⟨h01, h12, hlast⟩ edge membership
    simp only [graphEdges, List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl
    · exact h01
    · exact h12
    · exact hlast

private def swapColor {Color : Type} [DecidableEq Color] (a b x : Color) : Color :=
  if x = a then b else if x = b then a else x

private theorem swapColor_twice {Color : Type} [DecidableEq Color] (a b x : Color) :
    swapColor a b (swapColor a b x) = x := by
  by_cases hab : a = b
  · subst b
    by_cases h : x = a <;> simp [swapColor, h]
  · by_cases ha : x = a
    · subst x
      simp [swapColor, Ne.symm hab]
    · by_cases hb : x = b
      · subst x
        simp [swapColor, ha]
      · simp [swapColor, ha, hb]

private theorem from_not_first {Color : Type} [DecidableEq Color] {a b x : Color}
    (h : a ≠ x) : b ≠ swapColor a b x := by
  intro same
  have mapped := congrArg (swapColor a b) same
  have swap_b : swapColor a b b = a := by
    by_cases hab : a = b
    · subst b
      simp [swapColor]
    · simp [swapColor, Ne.symm hab]
  rw [swap_b, swapColor_twice] at mapped
  exact h mapped

private theorem from_not_second {Color : Type} [DecidableEq Color] {a b x : Color}
    (h : b ≠ x) : a ≠ swapColor a b x := by
  intro same
  have mapped := congrArg (swapColor a b) same
  rw [swapColor_twice] at mapped
  exact h (by simpa [swapColor] using mapped)

private def changeLast {Color : Type} [DecidableEq Color] (color : Vertex → Color)
    (v : Vertex) : Color :=
  if v = 3 then swapColor (color 1) (color 2) (color 3) else color v

private theorem changeLast_twice {Color : Type} [DecidableEq Color] (color : Vertex → Color) :
    changeLast (changeLast color) = color := by
  funext v
  by_cases h : v = 3
  · subst v
    simp [changeLast, swapColor_twice]
  · simp [changeLast, h]

private def pathToStar {Color : Type} [DecidableEq Color] (c : Coloring pathEdges Color) :
    Coloring starEdges Color := by
  refine ⟨changeLast c.val, (proper_iff 1 _).mpr ?_⟩
  have h := (proper_iff 2 c.val).mp c.property
  simpa [changeLast] using And.intro h.1 (And.intro h.2.1 (from_not_second h.2.2))

private def starToPath {Color : Type} [DecidableEq Color] (c : Coloring starEdges Color) :
    Coloring pathEdges Color := by
  refine ⟨changeLast c.val, (proper_iff 2 _).mpr ?_⟩
  have h := (proper_iff 1 c.val).mp c.property
  simpa [changeLast] using And.intro h.1 (And.intro h.2.1 (from_not_first h.2.2))

def SameChromaticData (first second : List Edge) : Prop :=
  ∀ k : Nat, ∃ toSecond : Coloring first (Fin k) → Coloring second (Fin k),
    ∃ toFirst : Coloring second (Fin k) → Coloring first (Fin k),
      (∀ c, toFirst (toSecond c) = c) ∧ (∀ c, toSecond (toFirst c) = c)

theorem same_chromatic_data : SameChromaticData pathEdges starEdges := by
  intro k
  refine ⟨pathToStar, starToPath, ?_, ?_⟩
  · intro color
    exact Subtype.ext (changeLast_twice color.val)
  · intro color
    exact Subtype.ext (changeLast_twice color.val)

inductive Cell where
  | vertex (v : Vertex)
  | edge (e : Edge)

def dimension : Cell → Nat
  | .vertex _ => 0
  | .edge _ => 1

def closureVertices : Cell → List Vertex
  | .vertex v => [v]
  | .edge e => [e.1, e.2]

def disjointClosures (c d : Cell) : Bool :=
  (closureVertices c).all fun v => !(closureVertices d).contains v

def graphCells (edges : List Edge) : List Cell :=
  (List.finRange 4).map Cell.vertex ++ edges.map Cell.edge

private def admissiblePairs (c : Cell) (cells : List Cell) : List (Cell × Cell) :=
  cells.filterMap fun d => if disjointClosures c d then some (c, d) else none

def orderedCells (edges : List Edge) : List (Cell × Cell) :=
  let cells := graphCells edges
  cells.flatMap fun c => admissiblePairs c cells

/-- Each coordinate-swap orbit has one representative with the first cell earlier in the list. -/
private def orbitRepresentatives : List Cell → List (Cell × Cell)
  | [] => []
  | c :: rest => admissiblePairs c rest ++ orbitRepresentatives rest

def unorderedCells (edges : List Edge) : List (Cell × Cell) :=
  orbitRepresentatives (graphCells edges)

def cellCount (cells : List (Cell × Cell)) (k : Nat) : Nat :=
  (cells.filter fun (c, d) => dimension c + dimension d == k).length

def eulerCharacteristic (cells : List (Cell × Cell)) : Int :=
  (cellCount cells 0 : Int) - (cellCount cells 1 : Int) + (cellCount cells 2 : Int)

theorem ordered_path_counts :
    (cellCount (orderedCells pathEdges) 0, cellCount (orderedCells pathEdges) 1,
      cellCount (orderedCells pathEdges) 2) = (12, 12, 2) := by decide

theorem ordered_star_counts :
    (cellCount (orderedCells starEdges) 0, cellCount (orderedCells starEdges) 1,
      cellCount (orderedCells starEdges) 2) = (12, 12, 0) := by decide

theorem unordered_path_counts :
    (cellCount (unorderedCells pathEdges) 0, cellCount (unorderedCells pathEdges) 1,
      cellCount (unorderedCells pathEdges) 2) = (6, 6, 1) := by decide

theorem unordered_star_counts :
    (cellCount (unorderedCells starEdges) 0, cellCount (unorderedCells starEdges) 1,
      cellCount (unorderedCells starEdges) 2) = (6, 6, 0) := by decide

theorem counterexample :
    SameChromaticData pathEdges starEdges ∧
      eulerCharacteristic (orderedCells pathEdges) = 2 ∧
      eulerCharacteristic (orderedCells starEdges) = 0 ∧
      eulerCharacteristic (unorderedCells pathEdges) = 1 ∧
      eulerCharacteristic (unorderedCells starEdges) = 0 := by
  exact ⟨same_chromatic_data, by decide, by decide, by decide, by decide⟩

theorem no_chromatic_rule (rule : List Edge → Int)
    (respects : ∀ a b, SameChromaticData a b → rule a = rule b) :
    (¬ ∀ g, rule g = eulerCharacteristic (orderedCells g)) ∧
    (¬ ∀ g, rule g = eulerCharacteristic (unorderedCells g)) := by
  obtain ⟨matchColors, orderedPath, orderedStar, unorderedPath, unorderedStar⟩ := counterexample
  have same := respects pathEdges starEdges matchColors
  constructor
  · intro correct
    have impossible : (2 : Int) = 0 :=
      orderedPath.symm.trans ((correct pathEdges).symm.trans
        (same.trans ((correct starEdges).trans orderedStar)))
    contradiction
  · intro correct
    have impossible : (1 : Int) = 0 :=
      unorderedPath.symm.trans ((correct pathEdges).symm.trans
        (same.trans ((correct starEdges).trans unorderedStar)))
    contradiction

#print axioms no_chromatic_rule

end C4093
