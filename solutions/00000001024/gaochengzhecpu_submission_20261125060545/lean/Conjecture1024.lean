import Std

namespace Conjecture1024

/-- The additive identities used for binary syndromes. -/
structure BinaryAddition (F : Type) where
  zero : F
  add : F → F → F
  zeroAdd : ∀ a, add zero a = a
  addZero : ∀ a, add a zero = a
  addAssoc : ∀ a b c, add (add a b) c = add a (add b c)
  selfAdd : ∀ a, add a a = zero

namespace BinaryAddition

variable {F : Type} (arithmetic : BinaryAddition F)

theorem eq_of_add_eq_zero {a b : F} (zeroSum : arithmetic.add a b = arithmetic.zero) :
    a = b := by
  calc
    a = arithmetic.add a arithmetic.zero := (arithmetic.addZero a).symm
    _ = arithmetic.add a (arithmetic.add a b) := by rw [zeroSum]
    _ = arithmetic.add (arithmetic.add a a) b := (arithmetic.addAssoc a a b).symm
    _ = b := by rw [arithmetic.selfAdd, arithmetic.zeroAdd]

theorem add_ne_left {a b : F} (nonzero : b ≠ arithmetic.zero) :
    arithmetic.add a b ≠ a := by
  intro equal
  apply nonzero
  calc
    b = arithmetic.add arithmetic.zero b := (arithmetic.zeroAdd b).symm
    _ = arithmetic.add (arithmetic.add a a) b := by rw [arithmetic.selfAdd]
    _ = arithmetic.add a (arithmetic.add a b) := arithmetic.addAssoc a a b
    _ = arithmetic.zero := by rw [equal, arithmetic.selfAdd]

theorem add_ne_right {a b : F} (nonzero : a ≠ arithmetic.zero) :
    arithmetic.add a b ≠ b := by
  intro equal
  apply nonzero
  calc
    a = arithmetic.add a arithmetic.zero := (arithmetic.addZero a).symm
    _ = arithmetic.add a (arithmetic.add b b) := by rw [arithmetic.selfAdd]
    _ = arithmetic.add (arithmetic.add a b) b := (arithmetic.addAssoc a b b).symm
    _ = arithmetic.zero := by rw [equal, arithmetic.selfAdd]

end BinaryAddition

def syndrome {F : Type} (arithmetic : BinaryAddition F) (values : List F) : F :=
  values.foldr arithmetic.add arithmetic.zero

/-- The primitive powers form one enumeration of the nonzero elements. -/
structure LocatorSystem {F : Type} (arithmetic : BinaryAddition F) (m : Nat) where
  locators : List F
  distinct : locators.Nodup
  membership : ∀ value, value ∈ locators ↔ value ≠ arithmetic.zero
  size : locators.length + 1 = 2 ^ m

/-- A binary word is represented by its support. It passes the single-root
    check exactly when its distinct locators sum to zero. -/
def SingleCheckWord {F : Type} {arithmetic : BinaryAddition F} {m : Nat}
    (system : LocatorSystem arithmetic m) (support : List F) : Prop :=
  support.Nodup ∧ (∀ value ∈ support, value ∈ system.locators) ∧
    syndrome arithmetic support = arithmetic.zero

def HasMinimumWeight {F : Type} {arithmetic : BinaryAddition F} {m : Nat}
    (system : LocatorSystem arithmetic m) (minimum : Nat) : Prop :=
  (∃ support, support ≠ [] ∧ SingleCheckWord system support ∧ support.length = minimum) ∧
    ∀ support, support ≠ [] → SingleCheckWord system support → minimum ≤ support.length

private theorem weight_at_least_three {F : Type} {arithmetic : BinaryAddition F} {m : Nat}
    (system : LocatorSystem arithmetic m) (support : List F)
    (nonempty : support ≠ []) (valid : SingleCheckWord system support) : 3 ≤ support.length := by
  cases support with
  | nil => exact False.elim (nonempty rfl)
  | cons a rest =>
    cases rest with
    | nil =>
      have nonzero := (system.membership a).mp (valid.2.1 a List.mem_cons_self)
      have zeroSum := valid.2.2
      change arithmetic.add a arithmetic.zero = arithmetic.zero at zeroSum
      rw [arithmetic.addZero] at zeroSum
      exact False.elim (nonzero zeroSum)
    | cons b rest =>
      cases rest with
      | nil =>
        have zeroSum := valid.2.2
        change arithmetic.add a (arithmetic.add b arithmetic.zero) = arithmetic.zero at zeroSum
        rw [arithmetic.addZero] at zeroSum
        have same := arithmetic.eq_of_add_eq_zero zeroSum
        exact False.elim ((List.nodup_cons.mp valid.1).1 (List.mem_singleton.mpr same))
      | cons c rest =>
        simp only [List.length_cons]
        omega

private theorem two_distinct_in_list {F : Type} (values : List F)
    (distinct : values.Nodup) (enough : 2 ≤ values.length) :
    ∃ a b : F, a ∈ values ∧ b ∈ values ∧ a ≠ b := by
  cases values with
  | nil => simp at enough
  | cons a rest =>
    cases rest with
    | nil => simp at enough
    | cons b tail =>
      refine ⟨a, b, List.mem_cons_self, List.mem_cons_of_mem a List.mem_cons_self, ?_⟩
      intro same
      exact (List.nodup_cons.mp distinct).1 (List.mem_cons.mpr (Or.inl same))

private theorem weight_three_word {F : Type} {arithmetic : BinaryAddition F} {m : Nat}
    (system : LocatorSystem arithmetic m) (a b : F) (aPresent : a ∈ system.locators)
    (bPresent : b ∈ system.locators) (distinct : a ≠ b) :
    SingleCheckWord system [a, b, arithmetic.add a b] := by
  let c := arithmetic.add a b
  have aNonzero := (system.membership a).mp aPresent
  have bNonzero := (system.membership b).mp bPresent
  have cPresent : c ∈ system.locators :=
    (system.membership c).mpr (fun zeroSum => distinct (arithmetic.eq_of_add_eq_zero zeroSum))
  have aNeC : a ≠ c := (arithmetic.add_ne_left bNonzero).symm
  have bNeC : b ≠ c := (arithmetic.add_ne_right aNonzero).symm
  change SingleCheckWord system [a, b, c]
  refine ⟨?_, ?_, ?_⟩
  · simp [List.nodup_cons, distinct, aNeC, bNeC]
  · intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact aPresent
    · exact bPresent
    · exact cPresent
  · change arithmetic.add a (arithmetic.add b (arithmetic.add c arithmetic.zero)) = arithmetic.zero
    rw [arithmetic.addZero, ← arithmetic.addAssoc, arithmetic.selfAdd]

/-- Exact minimum distance 3 for the family with the single prescribed root,
    uniformly over all extension degrees m ≥ 2. -/
theorem single_root_minimum_is_three {F : Type} {arithmetic : BinaryAddition F} {m : Nat}
    (system : LocatorSystem arithmetic m) (extensionDegree : 2 ≤ m) :
    HasMinimumWeight system 3 := by
  have powerBound : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) extensionDegree
  have size := system.size
  have enough : 2 ≤ system.locators.length := by omega
  obtain ⟨a, b, aPresent, bPresent, distinct⟩ :=
    two_distinct_in_list system.locators system.distinct enough
  exact ⟨⟨[a, b, arithmetic.add a b], by simp, weight_three_word system a b aPresent bPresent distinct,
    rfl⟩, weight_at_least_three system⟩

theorem single_root_has_no_weight_two {F : Type} {arithmetic : BinaryAddition F} {m : Nat}
    (system : LocatorSystem arithmetic m) :
    ¬ ∃ support, SingleCheckWord system support ∧ support.length = 2 := by
  intro ⟨support, valid, weight⟩
  have nonempty : support ≠ [] := by
    intro empty
    simp [empty] at weight
  have bound := weight_at_least_three system support nonempty valid
  omega

/-- In a field of characteristic two, squaring is additive and sending each
    locator to its r-th power followed by squaring doubles the exponent. -/
structure Frobenius {F : Type} (arithmetic : BinaryAddition F) where
  square : F → F
  power : F → Nat → F
  squareZero : square arithmetic.zero = arithmetic.zero
  squareAdd : ∀ a b, square (arithmetic.add a b) = arithmetic.add (square a) (square b)
  squarePower : ∀ a r, power a (2 * r) = square (power a r)

def powerSyndrome {F : Type} {arithmetic : BinaryAddition F} (frob : Frobenius arithmetic)
    (support : List F) (r : Nat) : F :=
  syndrome arithmetic (support.map fun a => frob.power a r)

private theorem square_syndrome {F : Type} {arithmetic : BinaryAddition F}
    (frob : Frobenius arithmetic) (values : List F) :
    syndrome arithmetic (values.map frob.square) = frob.square (syndrome arithmetic values) := by
  induction values with
  | nil => exact frob.squareZero.symm
  | cons a rest ih =>
    change arithmetic.add (frob.square a) (syndrome arithmetic (rest.map frob.square)) =
      frob.square (arithmetic.add a (syndrome arithmetic rest))
    rw [ih, frob.squareAdd]

theorem doubling_syndrome {F : Type} {arithmetic : BinaryAddition F}
    (frob : Frobenius arithmetic) (support : List F) (r : Nat) :
    powerSyndrome frob support (2 * r) = frob.square (powerSyndrome frob support r) := by
  unfold powerSyndrome
  have doublePowers : (support.map fun a => frob.power a (2 * r)) =
      (support.map fun a => frob.power a r).map frob.square := by
    rw [List.map_map]
    apply List.map_congr_left
    intro a _
    exact frob.squarePower a r
  rw [doublePowers, square_syndrome]

/-- If δ=2r+1 is odd, the prescribed set 1,...,δ forces the next root. -/
theorem odd_cutoff_forces_next_root {F : Type} {arithmetic : BinaryAddition F}
    (frob : Frobenius arithmetic) (support : List F) (r : Nat)
    (prescribed : ∀ k, 1 ≤ k → k ≤ 2 * r + 1 →
      powerSyndrome frob support k = arithmetic.zero) :
    powerSyndrome frob support (2 * r + 2) = arithmetic.zero := by
  have halfRoot := prescribed (r + 1) (by omega) (by omega)
  rw [show 2 * r + 2 = 2 * (r + 1) by omega, doubling_syndrome, halfRoot, frob.squareZero]

end Conjecture1024

#print axioms Conjecture1024.single_root_minimum_is_three
#print axioms Conjecture1024.single_root_has_no_weight_two
#print axioms Conjecture1024.doubling_syndrome
#print axioms Conjecture1024.odd_cutoff_forces_next_root
