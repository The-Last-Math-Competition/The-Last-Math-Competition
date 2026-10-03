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

/-- Every subset of the seven point labels, independent of the mask encoding. -/
abbrev BooleanSubset := Point → Bool

def encodeBits (b0 b1 b2 b3 b4 b5 b6 : Bool) : Subset :=
  ⟨((if b0 then 1 else 0) + (if b1 then 2 else 0) +
    (if b2 then 4 else 0) + (if b3 then 8 else 0) +
    (if b4 then 16 else 0) + (if b5 then 32 else 0) +
    (if b6 then 64 else 0)) % 128, Nat.mod_lt _ (by decide)⟩

def bitTable (b0 b1 b2 b3 b4 b5 b6 : Bool) (i : Point) : Bool :=
  match i.val with
  | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
  | 4 => b4 | 5 => b5 | _ => b6

theorem encodeBits_correct :
    ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, ∀ i : Point,
    member (encodeBits b0 b1 b2 b3 b4 b5 b6) i =
      bitTable b0 b1 b2 b3 b4 b5 b6 i := by decide

def encode (p : BooleanSubset) : Subset :=
  encodeBits (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6)

/-- Surjectivity onto all membership functions, not just the five examples. -/
theorem every_subset_encoded (p : BooleanSubset) : member (encode p) = p := by
  funext i
  unfold encode
  rw [encodeBits_correct]
  have h : ∀ i : Point, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by decide
  rcases h i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Distinct masks really represent distinct ordinary subsets. -/
theorem membership_injective :
    ∀ a b : Subset, (∀ i : Point, member a i = member b i) → a = b := by decide

theorem encode_member (s : Subset) : encode (member s) = s := by
  apply membership_injective
  intro i
  exact congrArg (fun p => p i) (every_subset_encoded (member s))

theorem every_decidable_subset_encoded (S : Point → Prop) [DecidablePred S] :
    ∀ i, member (encode (fun j => decide (S j))) i = true ↔ S i := by
  intro i
  rw [every_subset_encoded]
  simp

/-- The bitwise inclusion test is exactly ordinary subset inclusion. -/
theorem contained_iff : ∀ a b : Subset,
    contained a b = true ↔ ∀ i : Point, member a i = true → member b i = true := by decide

def BooleanContained (p q : BooleanSubset) : Prop :=
  ∀ i : Point, p i = true → q i = true

instance (p q : BooleanSubset) : Decidable (BooleanContained p q) := by
  unfold BooleanContained
  infer_instance

theorem contained_as_boolean : ∀ a b : Subset,
    contained a b = decide (BooleanContained (member a) (member b)) := by decide

/-- Membership in the computed intersection is conjunction of memberships. -/
theorem intersection_membership : ∀ a b : Subset, ∀ i : Point,
    member (intersection a b) i = (member a i && member b i) := by decide

/-- Erasure keeps exactly the original members other than the deleted point. -/
theorem erase_membership : ∀ s : Subset, ∀ i j : Point,
    member (erase s i) j = (member s j && decide (j ≠ i)) := by decide

def booleanSize (p : BooleanSubset) : Nat := ((List.finRange 7).filter p).length

theorem size_encode (p : BooleanSubset) : size (encode p) = booleanSize p := by
  simp only [size, booleanSize, every_subset_encoded]

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

/-- The design balance statement applies to every ordinary Boolean subset.
This theorem explicitly transports the finite-mask check to the unencoded
set-theoretic condition, using both exhaustiveness and inclusion correctness. -/
theorem design_balance_for_all_subsets {D : Design} {t v k lambda : Nat}
    (hD : IsDesign D t v k lambda) (p : BooleanSubset)
    (hp : BooleanContained p (member D.points)) (hsize : booleanSize p = t) :
    (D.blocks.filter fun b => decide (BooleanContained p (member b))).length = lambda := by
  rcases hD with ⟨_, _, _, _, _, _, _, hbalanced⟩
  have hcontained : contained (encode p) D.points = true := by
    apply (contained_iff (encode p) D.points).mpr
    simpa only [every_subset_encoded] using hp
  have hs : size (encode p) = t := (size_encode p).trans hsize
  have h := hbalanced (encode p) hcontained hs
  have heq : (fun b => contained (encode p) b) =
      (fun b => decide (BooleanContained p (member b))) := by
    funext b
    rw [contained_as_boolean, every_subset_encoded]
  rw [heq] at h
  exact h

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

#print axioms every_subset_encoded
#print axioms encode_member
#print axioms every_decidable_subset_encoded
#print axioms contained_iff
#print axioms intersection_membership
#print axioms erase_membership
#print axioms design_balance_for_all_subsets
#print axioms d0_correct
#print axioms d1_correct
#print axioms d2_correct
#print axioms d3_correct
#print axioms d4_correct
#print axioms also_point_derivations
#print axioms conjecture8435_false
end Conjecture8435
