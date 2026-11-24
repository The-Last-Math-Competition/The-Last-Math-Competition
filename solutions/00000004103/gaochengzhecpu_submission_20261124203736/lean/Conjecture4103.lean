import Std

namespace Conjecture4103

abbrev Leaf := Fin 4
abbrev StarVertex := Option Leaf

def starAdjacent (a b : StarVertex) : Prop :=
  (a = none ∧ b ≠ none) ∨ (b = none ∧ a ≠ none)

def oppositeLeaf (leaf : Leaf) : Leaf := ⟨3 - leaf.val, by omega⟩

def starInvolution (vertex : StarVertex) : StarVertex := vertex.map oppositeLeaf

theorem star_involution (vertex : StarVertex) :
    starInvolution (starInvolution vertex) = vertex := by
  cases vertex with
  | none => rfl
  | some leaf =>
    change some (oppositeLeaf (oppositeLeaf leaf)) = some leaf
    congr 1
    apply Fin.ext
    change 3 - (3 - leaf.val) = leaf.val
    have bound := leaf.isLt
    omega

theorem star_involution_preserves_edges (a b : StarVertex) :
    starAdjacent (starInvolution a) (starInvolution b) ↔ starAdjacent a b := by
  cases a <;> cases b <;> simp [starAdjacent, starInvolution]

theorem star_involution_fixes_only_center (vertex : StarVertex) :
    starInvolution vertex = vertex ↔ vertex = none := by
  cases vertex with
  | none => simp [starInvolution]
  | some leaf =>
    change some (oppositeLeaf leaf) = some leaf ↔ some leaf = none
    simp only [Option.some.injEq, reduceCtorEq, iff_false]
    intro fixed
    have values := congrArg Fin.val fixed
    change 3 - leaf.val = leaf.val at values
    have bound := leaf.isLt
    omega

/-- An unordered configuration of two distinct vertices takes one of these
    forms, using increasing leaf labels for the leaf-pair state. -/
inductive State where
  | centerWith (leaf : Leaf)
  | twoLeaves (first second : Leaf) (ordered : first.val < second.val)

/-- A one-cell moves along one arm while a different leaf stays fixed.
    At a leaf-pair state, either leaf may be the one that stays fixed. -/
inductive Incidence : State → State → Prop where
  | first {i j : Leaf} {ordered : i.val < j.val} :
      Incidence (.centerWith i) (.twoLeaves i j ordered)
  | second {i j : Leaf} {ordered : i.val < j.val} :
      Incidence (.centerWith j) (.twoLeaves i j ordered)

theorem midpoint_incidence {i j k : Leaf} (ordered : i.val < j.val) :
    Incidence (.centerWith k) (.twoLeaves i j ordered) ↔ k = i ∨ k = j := by
  constructor
  · intro h
    cases h
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro h
    rcases h with rfl | rfl
    · exact Incidence.first
    · exact Incidence.second

inductive Reaches : State → State → Prop where
  | stay (state : State) : Reaches state state
  | step {a b c : State} (path : Reaches a b) (edge : Incidence b c ∨ Incidence c b) :
      Reaches a c

private theorem reaches_leaf (leaf : Leaf) : Reaches (.centerWith 0) (.centerWith leaf) := by
  by_cases isZero : leaf = 0
  · cases isZero
    exact Reaches.stay _
  · have positive : (0 : Leaf).val < leaf.val := by
      by_cases valueZero : leaf.val = 0
      · exact False.elim (isZero (Fin.ext valueZero))
      · change 0 < leaf.val
        omega
    have toMidpoint : Reaches (.centerWith 0) (.twoLeaves 0 leaf positive) :=
      Reaches.step (Reaches.stay _) (Or.inl Incidence.first)
    exact Reaches.step toMidpoint (Or.inr Incidence.second)

theorem configuration_connected (state : State) : Reaches (.centerWith 0) state := by
  cases state with
  | centerWith leaf => exact reaches_leaf leaf
  | twoLeaves first _ _ => exact Reaches.step (reaches_leaf first) (Or.inl Incidence.first)

def leafPairs : List (Leaf × Leaf) :=
  (List.finRange 4).flatMap fun i =>
    ((List.finRange 4).filter fun j => i.val < j.val).map fun j => (i, j)

def oneCells : List (Leaf × Leaf) :=
  (List.finRange 4).flatMap fun moving =>
    ((List.finRange 4).filter fun fixed => moving != fixed).map fun fixed => (moving, fixed)

def armClosure (leaf : Leaf) : List StarVertex := [none, some leaf]

def twoCells : List (Leaf × Leaf) :=
  (List.finRange 4).flatMap fun i =>
    ((List.finRange 4).filter fun j =>
      !(armClosure i).any fun v => (armClosure j).contains v).map fun j => (i, j)

theorem configuration_cell_counts :
    (List.finRange 4).length + leafPairs.length = 10 ∧
      oneCells.length = 12 ∧ twoCells.length = 0 := by decide

theorem cycle_rank :
    oneCells.length + 1 - ((List.finRange 4).length + leafPairs.length) = 3 := by decide

structure Letter where
  generator : Fin 3
  positive : Bool

def Letter.inverse (letter : Letter) : Letter := ⟨letter.generator, !letter.positive⟩

@[simp] theorem letter_inverse_involutive (letter : Letter) :
    letter.inverse.inverse = letter := by
  cases letter with
  | mk _ positive => cases positive <;> rfl

theorem letter_ne_inverse (letter : Letter) : letter ≠ letter.inverse := by
  cases letter with
  | mk _ positive =>
    intro same
    have signs := congrArg Letter.positive same
    cases positive <;> contradiction

def wordInverse (word : List Letter) : List Letter := word.reverse.map Letter.inverse

def Reduced (word : List Letter) : Prop :=
  ∀ letter : Letter, [letter, letter.inverse] <:+: word → False

/-- In the reduced-word model of the free group on three generators, inversion
    reverses and inverts the letters. A self-inverse reduced word is empty. -/
theorem reduced_self_inverse_is_empty (word : List Letter) (reduced : Reduced word)
    (fixed : word = wordInverse word) : word = [] := by
  cases wordShape : word with
  | nil => rfl
  | cons first tail =>
    have localFixed : first :: tail = wordInverse (first :: tail) := by
      simpa only [wordShape] using fixed
    have localReduced : Reduced (first :: tail) := by
      simpa only [wordShape] using reduced
    by_cases tailEmpty : tail = []
    · subst tail
      have letters : first = first.inverse := by simpa [wordInverse] using localFixed
      exact False.elim (letter_ne_inverse first letters)
    · let middle := tail.dropLast
      let last := tail.getLast tailEmpty
      have tailShape : tail = middle ++ [last] := (List.dropLast_concat_getLast tailEmpty).symm
      have shape : first :: (middle ++ [last]) =
          last.inverse :: (wordInverse middle ++ [first.inverse]) := by
        simpa [tailShape, wordInverse, List.reverse_cons, List.reverse_append, List.append_assoc]
          using localFixed
      obtain ⟨headMatch, tailMatch⟩ := List.cons.inj shape
      have lastMatch : last = first.inverse := by
        simpa using congrArg Letter.inverse headMatch.symm
      have middleFixed : middle = wordInverse middle := by
        rw [lastMatch] at tailMatch
        exact List.append_cancel_right tailMatch
      have middleReduced : Reduced middle := by
        intro letter pair
        have contained : middle <:+: first :: tail := by
          rw [tailShape]
          exact List.infix_append' [first] middle [last]
        exact localReduced letter (pair.trans contained)
      have middleEmpty := reduced_self_inverse_is_empty middle middleReduced middleFixed
      have adjacent : [first, first.inverse] <:+: first :: tail := by
        rw [tailShape, middleEmpty, lastMatch]
        exact List.infix_rfl
      exact False.elim (localReduced first adjacent)
termination_by word.length
decreasing_by
  simp [middle, List.length_dropLast, wordShape]
  omega

end Conjecture4103

#print axioms Conjecture4103.star_involution_fixes_only_center
#print axioms Conjecture4103.midpoint_incidence
#print axioms Conjecture4103.configuration_connected
#print axioms Conjecture4103.configuration_cell_counts
#print axioms Conjecture4103.cycle_rank
#print axioms Conjecture4103.reduced_self_inverse_is_empty
