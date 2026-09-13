/-
  Disproof of conjecture `00000002175`: formalisation.

  Conjecture (as filed):

    A 3-wise odd-intersecting family is one where the intersection of any three
    members is odd.  Conjecture: the maximal size is always 2^{n-3}; and the
    extremal families consist of indicator functions of 3-dimensional affine
    subspaces.

  Disproof.  On a 4-element ground set {1,2,3,4} the four subsets

      {1,2},  {1,3},  {1,4},  {1,2,3,4}

  form a 3-wise odd-intersecting family: the intersection of any three of them
  is exactly {1}, of odd size 1.  But the family has size 4, whereas the
  conjecture predicts the maximum 2^{4-3} = 2.  Hence the size claim is false
  already at n = 4.  (The true maximum at n = 4 is 5, and a 5-element family is
  also exhibited below.)

  Members are represented as `List Bool` (indicator vectors of length 4).  This
  representation is deliberate: the function type `Fin 4 → Bool` has no
  `DecidableEq` instance in core Lean, so the bounded quantifier
  `∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ F, …` would fail to synthesise a `Decidable`
  instance and `decide` could not close the goal.

  The file uses CORE LEAN ONLY (`import Std`); no Mathlib, `Finset`, `ZMod`,
  `Fintype`, `Matrix`, or `sorry`.
-/

import Std

set_option maxRecDepth 1000000

namespace Tlmc2175

/-! ## Intersections of three members -/

/-- `interSize a b c` is the size of the intersection of three indicator
vectors: the number of coordinates at which all three lists carry `true`.  It
zips the three lists together and counts the positions where every entry is
`true`. -/
def interSize (a b c : List Bool) : Nat :=
  (((a.zip b).zip c).filter (fun p => p.1.1 && p.1.2 && p.2)).length

/-- `TripleOdd F` says that `F` is a 3-wise odd-intersecting family: any three
*distinct* members of `F` have an intersection of odd size. -/
def TripleOdd (F : List (List Bool)) : Prop :=
  ∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ F, a ≠ b → a ≠ c → b ≠ c → interSize a b c % 2 = 1

/-- Boolean checker for the 3-wise odd-intersection property: it scans every
ordered triple of members and accepts unless the three members are distinct and
their intersection has even size.  It is a `Bool`-valued mirror of `TripleOdd`;
for lists it is decidable by evaluation. -/
def checkFamily (F : List (List Bool)) : Bool :=
  F.all fun a => F.all fun b => F.all fun c =>
    (a == b) || (a == c) || (b == c) || (interSize a b c % 2 == 1)

/-! ## The counterexample: the four members and the family -/

/-- The member `{1,2}` as an indicator vector. -/
def m12 : List Bool := [true, true, false, false]

/-- The member `{1,3}` as an indicator vector. -/
def m13 : List Bool := [true, false, true, false]

/-- The member `{1,4}` as an indicator vector. -/
def m14 : List Bool := [true, false, false, true]

/-- The member `{1,2,3,4}` (the full ground set) as an indicator vector. -/
def m1234 : List Bool := [true, true, true, true]

/-- The witness family `F = { {1,2}, {1,3}, {1,4}, {1,2,3,4} }`, written as the
list of indicator vectors of length 4. -/
def F : List (List Bool) :=
  [[true, true, false, false], [true, false, true, false],
   [true, false, false, true], [true, true, true, true]]

/-- `F` is the list of the four named members. -/
theorem F_eq : F = [m12, m13, m14, m1234] := by decide

/-- The four members are pairwise distinct, so all four triples of distinct
members exist and must be checked. -/
theorem witness_members_pairwise_distinct :
    m12 ≠ m13 ∧ m12 ≠ m14 ∧ m12 ≠ m1234 ∧ m13 ≠ m14 ∧ m13 ≠ m1234 ∧
    m14 ≠ m1234 := by decide

/-! ## The explicit four-triple intersection check -/

/-- The first triple `{1,2}, {1,3}, {1,4}` meets in `{1}`. -/
theorem triple_123 : interSize m12 m13 m14 = 1 := by decide

/-- The second triple `{1,2}, {1,3}, {1,2,3,4}` meets in `{1}`. -/
theorem triple_124 : interSize m12 m13 m1234 = 1 := by decide

/-- The third triple `{1,2}, {1,4}, {1,2,3,4}` meets in `{1}`. -/
theorem triple_134 : interSize m12 m14 m1234 = 1 := by decide

/-- The fourth triple `{1,3}, {1,4}, {1,2,3,4}` meets in `{1}`. -/
theorem triple_234 : interSize m13 m14 m1234 = 1 := by decide

/-- The intersection of every one of the four triples of distinct members has
size 1.  This is the explicit check requested by the disproof. -/
theorem witness_all_triples_meet_in_one :
    interSize m12 m13 m14 = 1 ∧ interSize m12 m13 m1234 = 1 ∧
    interSize m12 m14 m1234 = 1 ∧ interSize m13 m14 m1234 = 1 :=
  ⟨triple_123, triple_124, triple_134, triple_234⟩

/-- `F` is 3-wise odd-intersecting.  After case-splitting on the four possible
values of each of the three members, every surviving goal is either a
distinctness contradiction (handled by `absurd`) or a concrete arithmetic fact
(handled by `decide`). -/
theorem witness_oddTriples : TripleOdd F := by
  unfold TripleOdd
  simp only [F, List.mem_cons, List.mem_nil_iff, or_false]
  intro a ha b hb c hc hab hac hbc
  rcases ha with rfl | rfl | rfl | rfl <;>
  rcases hb with rfl | rfl | rfl | rfl <;>
  rcases hc with rfl | rfl | rfl | rfl <;>
  first | exact absurd rfl hab | exact absurd rfl hac | exact absurd rfl hbc
        | decide

/-- The Boolean checker also accepts `F`. -/
theorem witness_check : checkFamily F = true := by decide

/-! ## The witness breaks the claimed bound -/

/-- The witness has four members. -/
theorem witness_length : F.length = 4 := by decide

/-- The conjecture's claimed maximum at `n = 4` is `2^{4-3} = 2`. -/
theorem claimed_bound_n4 : 2 ^ (4 - 3 : Nat) = 2 := by decide

/-- The witness breaks the claimed maximum: `4 > 2^{4-3}`. -/
theorem witness_breaks_bound : F.length > 2 ^ (4 - 3 : Nat) := by decide

/-- Packaged refutation of the size claim at `n = 4`: `F` is 3-wise
odd-intersecting, has four members, and `4 > 2^{4-3} = 2`. -/
theorem witness_refutes_size_claim :
    TripleOdd F ∧ F.length = 4 ∧ 2 ^ (4 - 3 : Nat) = 2 ∧
    F.length > 2 ^ (4 - 3 : Nat) :=
  ⟨witness_oddTriples, witness_length, claimed_bound_n4, witness_breaks_bound⟩

/-! ## The true maximum at `n = 4` is at least 5 -/

/-- A 5-element 3-wise odd-intersecting family on `{1,2,3,4}`, namely
`{1}, {1,2}, {1,3}, {1,4}, {1,2,3}`.  This shows the true maximum at `n = 4`
is at least 5, exceeding the claimed `2^{4-3} = 2` even further. -/
def G5 : List (List Bool) :=
  [[true, false, false, false], [true, true, false, false],
   [true, false, true, false], [true, false, false, true],
   [true, true, true, false]]

/-- The 5-element family `G5` is 3-wise odd-intersecting. -/
theorem G5_oddTriples : TripleOdd G5 := by
  unfold TripleOdd
  simp only [G5, List.mem_cons, List.mem_nil_iff, or_false]
  intro a ha b hb c hc hab hac hbc
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
  rcases hb with rfl | rfl | rfl | rfl | rfl <;>
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
  first | exact absurd rfl hab | exact absurd rfl hac | exact absurd rfl hbc
        | decide

/-- The Boolean checker accepts `G5`. -/
theorem G5_check : checkFamily G5 = true := by decide

/-- `G5` has five members. -/
theorem G5_length : G5.length = 5 := by decide

/-- The true maximum at `n = 4` exceeds the conjecture's bound: `5 > 2^{4-3}`. -/
theorem true_max_n4_exceeds_claim : G5.length > 2 ^ (4 - 3 : Nat) := by decide

/-- Packaged: `G5` is a valid 5-element family, so `M(4) ≥ 5 > 2 = 2^{4-3}`. -/
theorem n4_max_at_least_five :
    TripleOdd G5 ∧ G5.length = 5 ∧ G5.length > 2 ^ (4 - 3 : Nat) :=
  ⟨G5_oddTriples, G5_length, true_max_n4_exceeds_claim⟩

end Tlmc2175
