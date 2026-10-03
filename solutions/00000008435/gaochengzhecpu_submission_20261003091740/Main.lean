import Std

/-! Four successive derived symmetric BIBDs refute the chain-length bound.
The initial blocks are all six-element subsets of a seven-element set.
Every derivation is defined on the actual incidence structure. -/
namespace Conjecture8435
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

abbrev Point := Fin 7
abbrev Subset := Fin 128

def member (s : Subset) (i : Point) : Bool := (s.val / 2^i.val) % 2 == 1

def contained (a b : Subset) : Bool := a.val &&& b.val == a.val

def intersection (a b : Subset) : Subset :=
  ⟨(a.val &&& b.val) % 128, Nat.mod_lt _ (by decide)⟩

def erase (s : Subset) (i : Point) : Subset :=
  ⟨(s.val &&& (127 - 2^i.val)) % 128, Nat.mod_lt _ (by decide)⟩

def size (s : Subset) : Nat := ((List.finRange 7).filter (member s)).length

structure Design where
  points : Subset
  blocks : List Subset
  deriving DecidableEq

/-- A simple t-(v,k,lambda) design on a subset of the seven labels.
The explicit inequalities ensure positive parameters and proper blocks. -/
def IsDesign (D : Design) (t v k lambda : Nat) : Prop :=
  1 ≤ t ∧ t ≤ k ∧ k < v ∧ 0 < lambda ∧
  size D.points = v ∧ D.blocks.Nodup ∧
  (∀ b : Subset, b ∈ D.blocks → contained b D.points = true ∧ size b = k) ∧
  (∀ s : Subset, contained s D.points = true → size s = t →
    (D.blocks.filter fun b => contained s b).length = lambda)

def IsSymmetricBIBD (D : Design) (v k lambda : Nat) : Prop :=
  IsDesign D 2 v k lambda ∧ D.blocks.length = v

/-- Standard block derivation: use B as the new point set and intersect
all other blocks with B. -/
def deriveBlock (D : Design) (B : Subset) : Design where
  points := B
  blocks := ((D.blocks.filter fun C => C != B).map fun C => intersection C B)

/-- Standard point derivation, for an additional independent convention check. -/
def derivePoint (D : Design) (i : Point) : Design where
  points := erase D.points i
  blocks := ((D.blocks.filter fun C => member C i).map fun C => erase C i)

def d0 : Design where
  points := 127
  blocks := (List.finRange 7).map fun i => erase 127 i

def b0 : Subset := erase d0.points 0
def d1 : Design := deriveBlock d0 b0
def b1 : Subset := erase d1.points 1
def d2 : Design := deriveBlock d1 b1
def b2 : Subset := erase d2.points 2
def d3 : Design := deriveBlock d2 b2
def b3 : Subset := erase d3.points 3
def d4 : Design := deriveBlock d3 b3

theorem d0_correct : IsSymmetricBIBD d0 7 6 5 := by
  constructor
  · unfold IsDesign; decide
  · decide

theorem d1_correct : IsSymmetricBIBD d1 6 5 4 := by
  constructor
  · unfold IsDesign; decide
  · decide

theorem d2_correct : IsSymmetricBIBD d2 5 4 3 := by
  constructor
  · unfold IsDesign; decide
  · decide

theorem d3_correct : IsSymmetricBIBD d3 4 3 2 := by
  constructor
  · unfold IsDesign; decide
  · decide

theorem d4_correct : IsSymmetricBIBD d4 3 2 1 := by
  constructor
  · unfold IsDesign; decide
  · decide

/-- The selected object is really a proper block at each of the four steps. -/
theorem chosen_blocks_valid :
    (b0 ∈ d0.blocks ∧ b0 ≠ d0.points) ∧
    (b1 ∈ d1.blocks ∧ b1 ≠ d1.points) ∧
    (b2 ∈ d2.blocks ∧ b2 ≠ d2.points) ∧
    (b3 ∈ d3.blocks ∧ b3 ≠ d3.points) := by decide

/-- In this example point derivation yields exactly the same incidence data. -/
theorem also_point_derivations :
    derivePoint d0 0 = d1 ∧ derivePoint d1 1 = d2 ∧
    derivePoint d2 2 = d3 ∧ derivePoint d3 3 = d4 := by decide

def Good (D : Design) : Prop :=
  ∃ v k lambda : Nat, IsSymmetricBIBD D v k lambda

def DerivedStep (D E : Design) : Prop :=
  Good D ∧ Good E ∧ ∃ B : Subset, B ∈ D.blocks ∧ B ≠ D.points ∧ E = deriveBlock D B

/-- A bound of three on derivation-chain length forbids four successive
valid derivation steps, even within the subclass of symmetric BIBDs. -/
def ChainLengthAtMostThree : Prop :=
  ∀ D0 D1 D2 D3 D4 : Design,
    DerivedStep D0 D1 → DerivedStep D1 D2 →
    DerivedStep D2 D3 → DerivedStep D3 D4 → False

theorem step0 : DerivedStep d0 d1 := by
  refine ⟨⟨7,6,5,d0_correct⟩, ⟨6,5,4,d1_correct⟩, b0, ?_, ?_, rfl⟩
  · exact chosen_blocks_valid.1.1
  · exact chosen_blocks_valid.1.2

theorem step1 : DerivedStep d1 d2 := by
  refine ⟨⟨6,5,4,d1_correct⟩, ⟨5,4,3,d2_correct⟩, b1, ?_, ?_, rfl⟩
  · exact chosen_blocks_valid.2.1.1
  · exact chosen_blocks_valid.2.1.2

theorem step2 : DerivedStep d2 d3 := by
  refine ⟨⟨5,4,3,d2_correct⟩, ⟨4,3,2,d3_correct⟩, b2, ?_, ?_, rfl⟩
  · exact chosen_blocks_valid.2.2.1.1
  · exact chosen_blocks_valid.2.2.1.2

theorem step3 : DerivedStep d3 d4 := by
  refine ⟨⟨4,3,2,d3_correct⟩, ⟨3,2,1,d4_correct⟩, b3, ?_, ?_, rfl⟩
  · exact chosen_blocks_valid.2.2.2.1
  · exact chosen_blocks_valid.2.2.2.2

/-- Direct negation of the chain bound, with all four actual operations. -/
theorem conjecture8435_false : ¬ ChainLengthAtMostThree := by
  intro h
  exact h d0 d1 d2 d3 d4 step0 step1 step2 step3

#print axioms d0_correct
#print axioms d1_correct
#print axioms d2_correct
#print axioms d3_correct
#print axioms d4_correct
#print axioms also_point_derivations
#print axioms conjecture8435_false
end Conjecture8435
