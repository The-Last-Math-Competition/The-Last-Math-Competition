/-
  Refutation of conjecture 00000002604 ("distributive lattice layer-thickness rigidity").

  Reading. A finite distributive lattice is isomorphic to the ideal lattice J(P) of its
  join-irreducible poset P (Birkhoff). The "layer-count vector" of the lattice is the
  rank-size vector of J(P): the number of order ideals of P of each cardinality, i.e. the
  number of elements of each rank in J(P). The conjecture asserts that this vector
  determines J(P) up to isomorphism.

  Refutation. We exhibit two non-isomorphic posets on 4 elements whose ideal lattices have
  the same rank-size vector (1,2,2,2,1). Hence the two distributive lattices J(P), J(Q)
  are non-isomorphic but have the same layer-count vector.

    P : 0 < 1 < 2, with 3 isolated.
    Q : 0 < 2, 0 < 3, 1 < 2 (reflexive-transitive closure).

  Everything is core Lean only (`import Std`), no Mathlib, no `sorry`, no axioms,
  no `native_decide`. `Finset` is Mathlib, so subsets of Fin 4 are encoded as Nat bitmasks
  and all enumeration is done with `List`/`Fin`/`Nat`/`Bool`.
-/

import Std

namespace Tlmc2604

/-! ## Two posets on `Fin 4` -/

/-- Poset P: the chain `0 < 1 < 2`, element `3` isolated. -/
def leP : Fin 4 → Fin 4 → Bool := fun a b =>
  (a.val == b.val) ||
  (a.val == 0 && (b.val == 1 || b.val == 2)) ||
  (a.val == 1 && b.val == 2)

/-- Poset Q: the relations `0 < 2`, `0 < 3`, `1 < 2`, reflexively-transitively closed. -/
def leQ : Fin 4 → Fin 4 → Bool := fun a b =>
  (a.val == b.val) ||
  (a.val == 0 && (b.val == 2 || b.val == 3)) ||
  (a.val == 1 && b.val == 2)

/-! ## Ideals and the ideal-count vector -/

/-- Membership of `x : Fin 4` in the subset encoded by the bitmask `S : Nat`. -/
def memMask (S : Nat) (x : Fin 4) : Bool := S.testBit x.val

/-- Cardinality of the subset encoded by `S`, computed by filtering `Fin 4`. -/
def cardMask (S : Nat) : Nat :=
  ((List.finRange 4).filter (fun x => memMask S x)).length

/-- The subset encoded by `S` is down-closed for the relation `le`. -/
def downClosed (le : Fin 4 → Fin 4 → Bool) (S : Nat) : Bool :=
  (List.finRange 4).all (fun x =>
    (List.finRange 4).all (fun y =>
      !(memMask S x && le y x) || memMask S y))

/-- The ideal-count (rank-size) vector of `le`: for each size `s = 0..4`, the number of
down-closed subsets of `Fin 4` of cardinality `s`. -/
def idealCountVector (le : Fin 4 → Fin 4 → Bool) : List Nat :=
  (List.range 5).map (fun s =>
    ((List.range 16).filter (fun S => downClosed le S && cardMask S == s)).length)

/-! ## The two vectors coincide, both equal `[1,2,2,2,1]` -/

theorem vectorP : idealCountVector leP = [1, 2, 2, 2, 1] := by decide

theorem vectorQ : idealCountVector leQ = [1, 2, 2, 2, 1] := by decide

theorem vectors_equal : idealCountVector leP = idealCountVector leQ := by decide

/-! ## Non-isomorphism

We enumerate all bijections `Fin 4 → Fin 4` as the `24` permutations of `[0,1,2,3]` and
check that none is an order isomorphism. -/

/-- The function `Fin 4 → Fin 4` induced by a list of four values. -/
def permFun (p : List Nat) : Fin 4 → Fin 4 := fun a =>
  ⟨p.getD a.val 0 % 4, Nat.mod_lt _ (by decide)⟩

/-- `f` is bijective, checked by counting preimages. -/
def IsBijective (f : Fin 4 → Fin 4) : Bool :=
  (List.finRange 4).all (fun b =>
    ((List.finRange 4).filter (fun a => f a == b)).length == 1)

/-- `f` preserves and reflects the relation, i.e. `le1 a b ↔ le2 (f a) (f b)`. -/
def IsOrderEmbedding (le1 le2 : Fin 4 → Fin 4 → Bool) (f : Fin 4 → Fin 4) : Bool :=
  (List.finRange 4).all (fun a =>
    (List.finRange 4).all (fun b =>
      le1 a b == le2 (f a) (f b)))

/-- The permutation `p` (a bijection `Fin 4 → Fin 4`) is an isomorphism of `le1` onto `le2`. -/
def IsIsoPerm (le1 le2 : Fin 4 → Fin 4 → Bool) (p : List Nat) : Bool :=
  IsBijective (permFun p) && IsOrderEmbedding le1 le2 (permFun p)

/-- Insert `x` at every position of the list `l`, producing a list of lists. -/
def insertEverywhere (x : Nat) : List Nat → List (List Nat)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertEverywhere x ys).map (fun l => y :: l)

/-- All permutations of a list of pairwise distinct naturals. -/
def permutations : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => (permutations xs).flatMap (insertEverywhere x)

/-- All `4! = 24` bijections `Fin 4 → Fin 4`, as value lists. -/
def perms : List (List Nat) := permutations [0, 1, 2, 3]

/-- No bijection `Fin 4 → Fin 4` is an isomorphism from P to Q. -/
theorem not_isomorphic :
    perms.all (fun p => IsIsoPerm leP leQ p) = false := by decide

/-! ## The refutation -/

/-- The layer-count vector is the same for the two non-isomorphic posets P and Q, and no
order-isomorphism between them exists. Therefore the two distributive lattices `J(P)` and
`J(Q)` are non-isomorphic while having the same layer-count vector, so the conjecture is
false. -/
theorem conjecture_00000002604_false :
    idealCountVector leP = idealCountVector leQ ∧
    idealCountVector leP = [1, 2, 2, 2, 1] ∧
    perms.all (fun p => IsIsoPerm leP leQ p) = false := by
  decide

end Tlmc2604
