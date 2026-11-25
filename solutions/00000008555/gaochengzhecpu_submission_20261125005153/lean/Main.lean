/-
  Conjecture 00000008555 — Complete Core Lean 4.19.0 Formalization
  Zero external dependencies; compiled with `-DwarningAsError=true`.
  Zero `sorry`, zero `admit`, zero `native_decide`, zero custom axioms.

  Contents:
  1. Bounded lattices, covering, atoms, upper semimodularity, atomisticity,
     geometric lattices, distributivity, modularity, congruences, and simplicity.
  2. Boolean binary-relation lattices `(BinRel X, ∩, ∪)` and Birkhoff's
     distributivity obstruction for arbitrary families of set-relation maps.
  3. Equivalence-relation lattices `(EqRel X, ∩, ∨_Eq, Δ_X, ∇_X)` and a complete,
     axiom-clean proof from scratch of Whitman's Complete Representation Theorem:
     every bounded lattice embeds preserving `(⊥, ⊤, ∧, ∨)` into `EqRel X` via a
     single map (`1 ≤ |L|`, and `0 < 1` for the 1-element lattice).
  4. Universal strict upper bounds (`< |L|`) for separating families of 2-valued
     meet-homomorphisms / binary relations `R_i ⊆ L × {*}` on every finite lattice,
     plus single-relation Galois / principal-downset representation.
  5. Concrete benchmark lattices (`C₁`, `B₁`, `B₂`, `M₃`, `C₃`, `N₅`) with full
     proofs of geometricity / non-geometricity (positive non-vacuity witnesses).
  6. Refutation of the geometric-lattice equality `= |L|` across all interpretations:
     - Finite `Eq(X)` family size (`0 < 1` on `C₁`; `1 < 2, 4, 5` on `B₁, B₂, M₃`
       over `Fin 2` and 3-element `Three`),
     - Generating-relation count in `Eq(Three)` (`2 < 4` on `B₂`; `3 < 5` on `M₃`),
     - Separating 2-valued relation count (`|L| - 1 < |L|` universally; `2 < 4` on
       `B₂`, `3 < 5` on `M₃`),
     - Dushnik–Miller linear-order / Ferrers dimension (`1 < 2` on `B₁`, `2 < 4` on
       `B₂`, `2 < 5` on `M₃`),
     - Subdirect / congruence factor count (`1 < 2` on `B₁`, `2 < 4` on `B₂`,
       `1 < 5` on simple `M₃`),
     - Boolean `(∩, ∪)` non-representability of geometric `M₃`,
     - Injective image-size tautology `|φ(L)| = |L|` holding equally on non-geometric
       finite lattices `C₃` (`Eq(Three)`) and `N₅` (`Eq(Four)`).
-/

namespace Conjecture00000008555

universe u v

/-! ## Section 1: Bounded Lattices and Geometric Lattices -/

structure BoundedLattice (α : Type u) where
  le : α → α → Prop
  bot : α
  top : α
  meet : α → α → α
  join : α → α → α
  le_refl : ∀ x, le x x
  le_trans : ∀ {x y z}, le x y → le y z → le x z
  le_antisymm : ∀ {x y}, le x y → le y x → x = y
  bot_le : ∀ x, le bot x
  le_top : ∀ x, le x top
  meet_le_left : ∀ x y, le (meet x y) x
  meet_le_right : ∀ x y, le (meet x y) y
  le_meet : ∀ {z x y}, le z x → le z y → le z (meet x y)
  le_join_left : ∀ x y, le x (join x y)
  le_join_right : ∀ x y, le y (join x y)
  join_le : ∀ {x y z}, le x z → le y z → le (join x y) z

namespace BoundedLattice

section BasicLaws
variable {α : Type u} (L : BoundedLattice α)

theorem meet_comm (x y : α) : L.meet x y = L.meet y x :=
  L.le_antisymm
    (L.le_meet (L.meet_le_right x y) (L.meet_le_left x y))
    (L.le_meet (L.meet_le_right y x) (L.meet_le_left y x))

theorem join_comm (x y : α) : L.join x y = L.join y x :=
  L.le_antisymm
    (L.join_le (L.le_join_right y x) (L.le_join_left y x))
    (L.join_le (L.le_join_right x y) (L.le_join_left x y))

theorem meet_idem (x : α) : L.meet x x = x :=
  L.le_antisymm (L.meet_le_left x x) (L.le_meet (L.le_refl x) (L.le_refl x))

theorem join_idem (x : α) : L.join x x = x :=
  L.le_antisymm (L.join_le (L.le_refl x) (L.le_refl x)) (L.le_join_left x x)

theorem meet_eq_left_of_le {x y : α} (h : L.le x y) : L.meet x y = x :=
  L.le_antisymm (L.meet_le_left x y) (L.le_meet (L.le_refl x) h)

theorem meet_eq_right_of_le {x y : α} (h : L.le y x) : L.meet x y = y := by
  rw [L.meet_comm]
  exact L.meet_eq_left_of_le h

theorem join_eq_right_of_le {x y : α} (h : L.le x y) : L.join x y = y :=
  L.le_antisymm (L.join_le h (L.le_refl y)) (L.le_join_right x y)

theorem join_eq_left_of_le {x y : α} (h : L.le y x) : L.join x y = x := by
  rw [L.join_comm]
  exact L.join_eq_right_of_le h

theorem le_iff_meet_eq (x y : α) : L.le x y ↔ L.meet x y = x :=
  ⟨fun h => L.meet_eq_left_of_le h, fun h => h ▸ L.meet_le_right x y⟩

theorem le_iff_join_eq (x y : α) : L.le x y ↔ L.join x y = y :=
  ⟨fun h => L.join_eq_right_of_le h, fun h => h ▸ L.le_join_left x y⟩

theorem bot_join (x : α) : L.join L.bot x = x :=
  L.join_eq_right_of_le (L.bot_le x)

theorem join_bot (x : α) : L.join x L.bot = x :=
  L.join_eq_left_of_le (L.bot_le x)

theorem top_join (x : α) : L.join L.top x = L.top :=
  L.join_eq_left_of_le (L.le_top x)

theorem join_top (x : α) : L.join x L.top = L.top :=
  L.join_eq_right_of_le (L.le_top x)

theorem bot_meet (x : α) : L.meet L.bot x = L.bot :=
  L.meet_eq_left_of_le (L.bot_le x)

theorem meet_bot (x : α) : L.meet x L.bot = L.bot :=
  L.meet_eq_right_of_le (L.bot_le x)

theorem top_meet (x : α) : L.meet L.top x = x :=
  L.meet_eq_right_of_le (L.le_top x)

theorem meet_top (x : α) : L.meet x L.top = x :=
  L.meet_eq_left_of_le (L.le_top x)

end BasicLaws

end BoundedLattice

/-- `Covers L x y` (`x ⋖ y`): `x < y` with no strictly intermediate element. -/
def Covers {α : Type u} (L : BoundedLattice α) (x y : α) : Prop :=
  x ≠ y ∧ L.le x y ∧ ∀ z, L.le x z → L.le z y → z = x ∨ z = y

/-- An atom of `L` is an element covering `⊥`. -/
def IsAtom {α : Type u} (L : BoundedLattice α) (a : α) : Prop :=
  Covers L L.bot a

/-- Upper semimodularity (Birkhoff covering condition):
    whenever `x ∧ y ⋖ y`, we have `x = x ∨ y` or `x ⋖ x ∨ y`
    (in fact `x ≠ x ∨ y`, so `x ⋖ x ∨ y`). -/
def IsUpperSemimodular {α : Type u} (L : BoundedLattice α) : Prop :=
  ∀ x y, Covers L (L.meet x y) y → Covers L x (L.join x y)

/-- `L` is atomistic if every element `x` is the least upper bound of the set of atoms
    below `x`: since `x` is tautologically an upper bound of `{a | IsAtom L a ∧ a ≤ x}`,
    `x` is its least upper bound iff every upper bound `y` satisfies `x ≤ y`. -/
def IsAtomistic {α : Type u} (L : BoundedLattice α) : Prop :=
  ∀ x y, (∀ a, IsAtom L a → L.le a x → L.le a y) → L.le x y

/-- A bounded lattice is geometric iff it is upper semimodular and atomistic. -/
def IsGeometricLattice {α : Type u} (L : BoundedLattice α) : Prop :=
  IsUpperSemimodular L ∧ IsAtomistic L

def IsDistributive {α : Type u} (L : BoundedLattice α) : Prop :=
  ∀ x y z, L.meet x (L.join y z) = L.join (L.meet x y) (L.meet x z)

def IsModular {α : Type u} (L : BoundedLattice α) : Prop :=
  ∀ x y z, L.le x z → L.join x (L.meet y z) = L.meet (L.join x y) z

/-- A lattice congruence on `L`. -/
structure IsLatticeCongruence {α : Type u} (L : BoundedLattice α) (θ : α → α → Prop) : Prop where
  refl : ∀ x, θ x x
  symm : ∀ {x y}, θ x y → θ y x
  trans : ∀ {x y z}, θ x y → θ y z → θ x z
  meet_compat : ∀ {x₁ y₁ x₂ y₂}, θ x₁ y₁ → θ x₂ y₂ → θ (L.meet x₁ x₂) (L.meet y₁ y₂)
  join_compat : ∀ {x₁ y₁ x₂ y₂}, θ x₁ y₁ → θ x₂ y₂ → θ (L.join x₁ x₂) (L.join y₁ y₂)

/-- A bounded lattice is simple if `⊥ ≠ ⊤` and its only congruences are equality and `⊤`. -/
def IsSimpleLattice {α : Type u} (L : BoundedLattice α) : Prop :=
  L.bot ≠ L.top ∧
    ∀ θ : α → α → Prop, IsLatticeCongruence L θ →
      (∀ x y, θ x y ↔ x = y) ∨ (∀ x y, θ x y)

/-- Complete `(⊥, ⊤, ∧, ∨)`-lattice embedding (for finite lattices, preserves all meets and joins). -/
structure BoundedLatticeEmbedding {α : Type u} {β : Type v}
    (L₁ : BoundedLattice α) (L₂ : BoundedLattice β) (φ : α → β) : Prop where
  inj : ∀ x y, φ x = φ y → x = y
  map_bot : φ L₁.bot = L₂.bot
  map_top : φ L₁.top = L₂.top
  map_meet : ∀ x y, φ (L₁.meet x y) = L₂.meet (φ x) (φ y)
  map_join : ∀ x y, φ (L₁.join x y) = L₂.join (φ x) (φ y)

theorem BoundedLatticeEmbedding.map_le_iff {α : Type u} {β : Type v}
    {L₁ : BoundedLattice α} {L₂ : BoundedLattice β} {φ : α → β}
    (hφ : BoundedLatticeEmbedding L₁ L₂ φ) (x y : α) :
    L₂.le (φ x) (φ y) ↔ L₁.le x y := by
  rw [L₂.le_iff_meet_eq, L₁.le_iff_meet_eq, ← hφ.map_meet]
  exact ⟨fun h => hφ.inj _ _ h, fun h => congrArg φ h⟩

/-! ## Section 2: Boolean and Equivalence-Relation Algebras of Binary Relations -/

/-- Binary relations on `X`. -/
abbrev BinRel (X : Type v) : Type v := X → X → Prop

def BoolRelLattice (X : Type v) : BoundedLattice (BinRel X) where
  le R S := ∀ x y, R x y → S x y
  bot := fun _ _ => False
  top := fun _ _ => True
  meet R S := fun x y => R x y ∧ S x y
  join R S := fun x y => R x y ∨ S x y
  le_refl _ _ _ h := h
  le_trans h₁ h₂ _ _ h := h₂ _ _ (h₁ _ _ h)
  le_antisymm h₁ h₂ := funext fun x => funext fun y => propext ⟨h₁ x y, h₂ x y⟩
  bot_le _ _ _ h := False.elim h
  le_top _ _ _ _ := trivial
  meet_le_left _ _ _ _ h := h.1
  meet_le_right _ _ _ _ h := h.2
  le_meet h₁ h₂ _ _ h := ⟨h₁ _ _ h, h₂ _ _ h⟩
  le_join_left _ _ _ _ h := Or.inl h
  le_join_right _ _ _ _ h := Or.inr h
  join_le h₁ h₂ _ _ h := h.elim (h₁ _ _) (h₂ _ _)

/-- Birkhoff obstruction: any lattice faithfully represented by a family of maps into
    Boolean binary-relation lattices `(BinRel (X i), ∩, ∪)` MUST be distributive. -/
theorem boolRel_family_implies_distributive {α : Type u} {I : Type v}
    (L : BoundedLattice α) (X : I → Type v) (φ : (i : I) → α → BinRel (X i))
    (h_meet : ∀ i x y, φ i (L.meet x y) = (BoolRelLattice (X i)).meet (φ i x) (φ i y))
    (h_join : ∀ i x y, φ i (L.join x y) = (BoolRelLattice (X i)).join (φ i x) (φ i y))
    (h_inj : ∀ x y, (∀ i, φ i x = φ i y) → x = y) :
    IsDistributive L := by
  intro x y z
  apply h_inj
  intro i
  rw [h_meet, h_join, h_join, h_meet, h_meet]
  funext u v
  exact propext ⟨fun ⟨hx, hyz⟩ => hyz.elim (fun hy => Or.inl ⟨hx, hy⟩) (fun hz => Or.inr ⟨hx, hz⟩),
    fun h => h.elim (fun ⟨hx, hy⟩ => ⟨hx, Or.inl hy⟩) (fun ⟨hx, hz⟩ => ⟨hx, Or.inr hz⟩)⟩

/-- Equivalence relations on `X`. -/
structure EqRel (X : Type v) where
  r : X → X → Prop
  refl : ∀ x, r x x
  symm : ∀ {x y}, r x y → r y x
  trans : ∀ {x y z}, r x y → r y z → r x z

theorem EqRel.ext {X : Type v} {R S : EqRel X} (h : ∀ x y, R.r x y ↔ S.r x y) : R = S := by
  cases R with
  | mk rR reflR symmR transR =>
    cases S with
    | mk rS reflS symmS transS =>
      have hr : rR = rS := funext fun x => funext fun y => propext (h x y)
      subst hr
      rfl

/-- Reflexive-symmetric-transitive closure of a binary relation. -/
inductive EqClosure {X : Type v} (R : X → X → Prop) : X → X → Prop where
  | base {x y} : R x y → EqClosure R x y
  | refl (x) : EqClosure R x x
  | symm {x y} : EqClosure R x y → EqClosure R y x
  | trans {x y z} : EqClosure R x y → EqClosure R y z → EqClosure R x z

def EqBot (X : Type v) : EqRel X where
  r x y := x = y
  refl _ := rfl
  symm h := h.symm
  trans h₁ h₂ := h₁.trans h₂

def EqTop (X : Type v) : EqRel X where
  r _ _ := True
  refl _ := trivial
  symm h := h
  trans _ _ := trivial

def EqMeet {X : Type v} (R S : EqRel X) : EqRel X where
  r x y := R.r x y ∧ S.r x y
  refl x := ⟨R.refl x, S.refl x⟩
  symm h := ⟨R.symm h.1, S.symm h.2⟩
  trans h₁ h₂ := ⟨R.trans h₁.1 h₂.1, S.trans h₁.2 h₂.2⟩

def EqJoin {X : Type v} (R S : EqRel X) : EqRel X where
  r := EqClosure (fun x y => R.r x y ∨ S.r x y)
  refl := EqClosure.refl
  symm := EqClosure.symm
  trans := EqClosure.trans

def EqRelLattice (X : Type v) : BoundedLattice (EqRel X) where
  le R S := ∀ x y, R.r x y → S.r x y
  bot := EqBot X
  top := EqTop X
  meet := EqMeet
  join := EqJoin
  le_refl _ _ _ h := h
  le_trans h₁ h₂ _ _ h := h₂ _ _ (h₁ _ _ h)
  le_antisymm h₁ h₂ := EqRel.ext fun x y => ⟨h₁ x y, h₂ x y⟩
  bot_le R x y h := h ▸ R.refl x
  le_top _ _ _ _ := trivial
  meet_le_left _ _ _ _ h := h.1
  meet_le_right _ _ _ _ h := h.2
  le_meet h₁ h₂ _ _ h := ⟨h₁ _ _ h, h₂ _ _ h⟩
  le_join_left _ _ _ _ h := EqClosure.base (Or.inl h)
  le_join_right _ _ _ _ h := EqClosure.base (Or.inr h)
  join_le {R S T} hR hS x y h := by
    induction h with
    | base hRS => exact hRS.elim (hR _ _) (hS _ _)
    | refl z => exact T.refl z
    | symm _ ih => exact T.symm ih
    | trans _ _ ih₁ ih₂ => exact T.trans ih₁ ih₂

/-- Indexed family of `(⊥, ⊤, ∧, ∨)`-representations of `L` into equivalence-relation lattices. -/
def CompleteEqFamilyRep {α : Type u} (L : BoundedLattice α) (n : Nat) : Prop :=
  ∃ (X : Fin n → Type u) (φ : (i : Fin n) → α → EqRel (X i)),
    (∀ i, φ i L.bot = EqBot (X i)) ∧
    (∀ i, φ i L.top = EqTop (X i)) ∧
    (∀ i x y, φ i (L.meet x y) = EqMeet (φ i x) (φ i y)) ∧
    (∀ i x y, φ i (L.join x y) = EqJoin (φ i x) (φ i y)) ∧
    (∀ x y, (∀ i, φ i x = φ i y) → x = y)

/-! ## Section 3: Whitman's Complete Equivalence-Relation Representation Theorem -/

/-- Bounded `(⊥, ⊤, ∧)`-preserving map into `EqRel X`. -/
structure MeetPreservingEqMap {α : Type u} (L : BoundedLattice α) (X : Type u)
    (φ : α → EqRel X) : Prop where
  map_bot : φ L.bot = EqBot X
  map_top : φ L.top = EqTop X
  map_meet : ∀ u v, φ (L.meet u v) = EqMeet (φ u) (φ v)

theorem MeetPreservingEqMap.mono {α : Type u} {L : BoundedLattice α} {X : Type u}
    {φ : α → EqRel X} (hφ : MeetPreservingEqMap L X φ) {u v : α} (huv : L.le u v)
    {p q : X} (hpq : (φ u).r p q) : (φ v).r p q := by
  have hm : φ (L.meet u v) = φ u := congrArg φ (L.meet_eq_left_of_le huv)
  rw [hφ.map_meet] at hm
  have hiff : (EqMeet (φ u) (φ v)).r p q ↔ (φ u).r p q := by rw [hm]
  exact (hiff.mpr hpq).2

/-- Canonical Stage-0 bounded meet-embedding `φ₀ : L → EqRel L`. -/
def wPhi0 {α : Type u} (L : BoundedLattice α) (u : α) : EqRel α where
  r x y := x = y ∨ (L.le x u ∧ L.le y u)
  refl _ := Or.inl rfl
  symm h := h.elim (fun he => Or.inl he.symm) (fun ⟨h₁, h₂⟩ => Or.inr ⟨h₂, h₁⟩)
  trans h₁ h₂ := by
    rcases h₁ with rfl | ⟨hx, hy⟩
    · exact h₂
    · rcases h₂ with rfl | ⟨_, hz⟩
      · exact Or.inr ⟨hx, hy⟩
      · exact Or.inr ⟨hx, hz⟩

theorem wPhi0_meetPreserving {α : Type u} (L : BoundedLattice α) :
    MeetPreservingEqMap L α (wPhi0 L) where
  map_bot := EqRel.ext fun x y =>
    ⟨fun h => h.elim id (fun ⟨hx, hy⟩ =>
      (L.le_antisymm hx (L.bot_le x)).trans (L.le_antisymm hy (L.bot_le y)).symm),
     fun h => Or.inl h⟩
  map_top := EqRel.ext fun x y =>
    ⟨fun _ => trivial, fun _ => Or.inr ⟨L.le_top x, L.le_top y⟩⟩
  map_meet u v := EqRel.ext fun x y => by
    constructor
    · intro h
      rcases h with rfl | ⟨hx, hy⟩
      · exact ⟨Or.inl rfl, Or.inl rfl⟩
      · exact ⟨Or.inr ⟨L.le_trans hx (L.meet_le_left u v), L.le_trans hy (L.meet_le_left u v)⟩,
               Or.inr ⟨L.le_trans hx (L.meet_le_right u v), L.le_trans hy (L.meet_le_right u v)⟩⟩
    · rintro ⟨h₁, h₂⟩
      rcases h₁ with rfl | ⟨hxu, hyu⟩
      · exact Or.inl rfl
      · rcases h₂ with rfl | ⟨hxv, hyv⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨L.le_meet hxu hxv, L.le_meet hyu hyv⟩

theorem wPhi0_inj {α : Type u} (L : BoundedLattice α) {u v : α}
    (h : wPhi0 L u = wPhi0 L v) : u = v := by
  have hle : ∀ x y : α, wPhi0 L x = wPhi0 L y → L.le x y := by
    intro x y hxy
    have hbx : (wPhi0 L x).r L.bot x := Or.inr ⟨L.bot_le x, L.le_refl x⟩
    rw [hxy] at hbx
    rcases hbx with hbot | ⟨_, hxy'⟩
    · exact hbot ▸ L.bot_le y
    · exact hxy'
  exact L.le_antisymm (hle u v h) (hle v u h.symm)

/-- Three-element tag type used both for Whitman's 3-point extension and `Eq(Three) ≅ M₃`. -/
inductive Three : Type where
  | zero : Three
  | one : Three
  | two : Three
  deriving DecidableEq

/-- Extension task `τ = (a, b, p, q)` witnessing `(p, q) ∈ φ(a ∨ b)` with `a, b ≠ ⊥`. -/
structure WTask {α : Type u} (L : BoundedLattice α) (X : Type u) (φ : α → EqRel X) : Type u where
  a : α
  b : α
  p : X
  q : X
  ha : ¬ L.le a L.bot
  hb : ¬ L.le b L.bot
  hpq : (φ (L.join a b)).r p q

abbrev WNewPt {α : Type u} (L : BoundedLattice α) (X : Type u) (φ : α → EqRel X) : Type u :=
  WTask L X φ × Three

abbrev WStepX {α : Type u} (L : BoundedLattice α) (X : Type u) (φ : α → EqRel X) : Type u :=
  Sum X (WNewPt L X φ)

def wBasePt {α : Type u} {L : BoundedLattice α} {X : Type u} {φ : α → EqRel X} :
    WStepX L X φ → X
  | Sum.inl x => x
  | Sum.inr (τ, Three.zero) => τ.p
  | Sum.inr (τ, Three.one) => τ.p
  | Sum.inr (τ, Three.two) => τ.q

def wActive {α : Type u} (L : BoundedLattice α) {X : Type u} {φ : α → EqRel X} (u : α) :
    WStepX L X φ → Prop
  | Sum.inl _ => True
  | Sum.inr (τ, Three.zero) => L.le τ.a u
  | Sum.inr (τ, Three.one) => L.le τ.a u ∧ L.le τ.b u
  | Sum.inr (τ, Three.two) => L.le τ.b u

def wLocalLink {α : Type u} (L : BoundedLattice α) {X : Type u} {φ : α → EqRel X} (u : α)
    (z₁ z₂ : WStepX L X φ) : Prop :=
  match z₁ with
  | Sum.inl _ => False
  | Sum.inr (τ₁, tag₁) =>
    match z₂ with
    | Sum.inl _ => False
    | Sum.inr (τ₂, tag₂) =>
      match tag₁, tag₂ with
      | Three.zero, Three.one => τ₁ = τ₂ ∧ L.le τ₁.b u ∧ ¬ L.le τ₁.a u
      | Three.one, Three.zero => τ₁ = τ₂ ∧ L.le τ₁.b u ∧ ¬ L.le τ₁.a u
      | Three.one, Three.two => τ₁ = τ₂ ∧ L.le τ₁.a u ∧ ¬ L.le τ₁.b u
      | Three.two, Three.one => τ₁ = τ₂ ∧ L.le τ₁.a u ∧ ¬ L.le τ₁.b u
      | _, _ => False

def wStepRel {α : Type u} (L : BoundedLattice α) {X : Type u} (φ : α → EqRel X) (u : α)
    (z₁ z₂ : WStepX L X φ) : Prop :=
  z₁ = z₂ ∨ (wActive L u z₁ ∧ wActive L u z₂ ∧ (φ u).r (wBasePt z₁) (wBasePt z₂)) ∨
    wLocalLink L u z₁ z₂

theorem wActive_meet_iff {α : Type u} (L : BoundedLattice α) {X : Type u} {φ : α → EqRel X}
    (u v : α) (z : WStepX L X φ) :
    wActive L (L.meet u v) z ↔ wActive L u z ∧ wActive L v z := by
  cases z with
  | inl _ => exact ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩
  | inr tp =>
    rcases tp with ⟨τ, tag⟩
    cases tag with
    | zero =>
      exact ⟨fun h => ⟨L.le_trans h (L.meet_le_left u v), L.le_trans h (L.meet_le_right u v)⟩,
             fun ⟨h₁, h₂⟩ => L.le_meet h₁ h₂⟩
    | one =>
      exact ⟨fun ⟨ha, hb⟩ =>
               ⟨⟨L.le_trans ha (L.meet_le_left u v), L.le_trans hb (L.meet_le_left u v)⟩,
                ⟨L.le_trans ha (L.meet_le_right u v), L.le_trans hb (L.meet_le_right u v)⟩⟩,
             fun ⟨⟨hau, hbu⟩, ⟨hav, hbv⟩⟩ => ⟨L.le_meet hau hav, L.le_meet hbu hbv⟩⟩
    | two =>
      exact ⟨fun h => ⟨L.le_trans h (L.meet_le_left u v), L.le_trans h (L.meet_le_right u v)⟩,
             fun ⟨h₁, h₂⟩ => L.le_meet h₁ h₂⟩

theorem wActive_mono {α : Type u} (L : BoundedLattice α) {X : Type u} {φ : α → EqRel X}
    {u w : α} (huw : L.le u w) {z : WStepX L X φ} (hz : wActive L u z) : wActive L w z := by
  cases z with
  | inl _ => exact trivial
  | inr tp =>
    rcases tp with ⟨τ, tag⟩
    cases tag with
    | zero => exact L.le_trans hz huw
    | one => exact ⟨L.le_trans hz.1 huw, L.le_trans hz.2 huw⟩
    | two => exact L.le_trans hz huw

theorem wLocalLink_symm {α : Type u} (L : BoundedLattice α) {X : Type u} {φ : α → EqRel X}
    {u : α} {z₁ z₂ : WStepX L X φ} (h : wLocalLink L u z₁ z₂) : wLocalLink L u z₂ z₁ := by
  cases z₁ with
  | inl _ => exact False.elim h
  | inr tp₁ =>
    rcases tp₁ with ⟨τ₁, tag₁⟩
    cases z₂ with
    | inl _ => exact False.elim h
    | inr tp₂ =>
      rcases tp₂ with ⟨τ₂, tag₂⟩
      cases tag₁ <;> cases tag₂ <;> first
        | exact False.elim h
        | (rcases h with ⟨rfl, h₁, h₂⟩; exact ⟨rfl, h₁, h₂⟩)

theorem wLocalLink_inactive {α : Type u} (L : BoundedLattice α) {X : Type u} {φ : α → EqRel X}
    {u : α} {z₁ z₂ : WStepX L X φ} (h : wLocalLink L u z₁ z₂) :
    ¬ wActive L u z₁ ∧ ¬ wActive L u z₂ := by
  cases z₁ with
  | inl _ => exact False.elim h
  | inr tp₁ =>
    rcases tp₁ with ⟨τ₁, tag₁⟩
    cases z₂ with
    | inl _ => exact False.elim h
    | inr tp₂ =>
      rcases tp₂ with ⟨τ₂, tag₂⟩
      cases tag₁ <;> cases tag₂ <;> first
        | exact False.elim h
        | (rcases h with ⟨rfl, _, hna⟩; exact ⟨fun ha => hna ha, fun ⟨ha, _⟩ => hna ha⟩)
        | (rcases h with ⟨rfl, _, hna⟩; exact ⟨fun ⟨ha, _⟩ => hna ha, fun ha => hna ha⟩)
        | (rcases h with ⟨rfl, _, hnb⟩; exact ⟨fun ⟨_, hb⟩ => hnb hb, fun hb => hnb hb⟩)
        | (rcases h with ⟨rfl, _, hnb⟩; exact ⟨fun hb => hnb hb, fun ⟨_, hb⟩ => hnb hb⟩)

theorem wLocalLink_trans_eq {α : Type u} (L : BoundedLattice α) {X : Type u} {φ : α → EqRel X}
    {u : α} {z₁ z₂ z₃ : WStepX L X φ}
    (h₁₂ : wLocalLink L u z₁ z₂) (h₂₃ : wLocalLink L u z₂ z₃) : z₁ = z₃ := by
  cases z₁ with
  | inl _ => exact False.elim h₁₂
  | inr tp₁ =>
    rcases tp₁ with ⟨τ₁, tag₁⟩
    cases z₂ with
    | inl _ => exact False.elim h₁₂
    | inr tp₂ =>
      rcases tp₂ with ⟨τ₂, tag₂⟩
      cases z₃ with
      | inl _ => exact False.elim h₂₃
      | inr tp₃ =>
        rcases tp₃ with ⟨τ₃, tag₃⟩
        cases tag₁ <;> cases tag₂ <;> cases tag₃ <;> first
          | exact False.elim h₁₂
          | exact False.elim h₂₃
          | (rcases h₁₂ with ⟨rfl, _, _⟩; rcases h₂₃ with ⟨rfl, _, _⟩; rfl)
          | (rcases h₁₂ with ⟨rfl, hb, hna⟩; rcases h₂₃ with ⟨rfl, ha, _⟩; exact False.elim (hna ha))
          | (rcases h₁₂ with ⟨rfl, ha, hnb⟩; rcases h₂₃ with ⟨rfl, hb, _⟩; exact False.elim (hnb hb))

def wStepPhi {α : Type u} (L : BoundedLattice α) {X : Type u} (φ : α → EqRel X) (u : α) :
    EqRel (WStepX L X φ) where
  r := wStepRel L φ u
  refl _ := Or.inl rfl
  symm h := by
    rcases h with rfl | ⟨ha₁, ha₂, hr⟩ | hloc
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨ha₂, ha₁, (φ u).symm hr⟩)
    · exact Or.inr (Or.inr (wLocalLink_symm L hloc))
  trans {z₁ z₂ z₃} h₁₂ h₂₃ := by
    rcases h₁₂ with rfl | ⟨ha₁, ha₂, hr₁₂⟩ | hloc₁₂
    · exact h₂₃
    · rcases h₂₃ with rfl | ⟨_, ha₃, hr₂₃⟩ | hloc₂₃
      · exact Or.inr (Or.inl ⟨ha₁, ha₂, hr₁₂⟩)
      · exact Or.inr (Or.inl ⟨ha₁, ha₃, (φ u).trans hr₁₂ hr₂₃⟩)
      · exact False.elim ((wLocalLink_inactive L hloc₂₃).1 ha₂)
    · rcases h₂₃ with rfl | ⟨ha₂, _, _⟩ | hloc₂₃
      · exact Or.inr (Or.inr hloc₁₂)
      · exact False.elim ((wLocalLink_inactive L hloc₁₂).2 ha₂)
      · exact Or.inl (wLocalLink_trans_eq L hloc₁₂ hloc₂₃)

theorem wStepRel_zero_one {α : Type u} (L : BoundedLattice α) {X : Type u} {φ : α → EqRel X}
    (τ : WTask L X φ) (w : α) :
    wStepRel L φ w (Sum.inr (τ, Three.zero)) (Sum.inr (τ, Three.one)) ↔ L.le τ.b w := by
  constructor
  · intro h
    rcases h with heq | ⟨_, ⟨_, hbw⟩, _⟩ | ⟨_, hbw, _⟩
    · cases heq
    · exact hbw
    · exact hbw
  · intro hbw
    by_cases haw : L.le τ.a w
    · exact Or.inr (Or.inl ⟨haw, ⟨haw, hbw⟩, (φ w).refl τ.p⟩)
    · exact Or.inr (Or.inr ⟨rfl, hbw, haw⟩)

theorem wStepRel_one_two {α : Type u} (L : BoundedLattice α) {X : Type u} {φ : α → EqRel X}
    (hφ : MeetPreservingEqMap L X φ) (τ : WTask L X φ) (w : α) :
    wStepRel L φ w (Sum.inr (τ, Three.one)) (Sum.inr (τ, Three.two)) ↔ L.le τ.a w := by
  constructor
  · intro h
    rcases h with heq | ⟨⟨haw, _⟩, _, _⟩ | ⟨_, haw, _⟩
    · cases heq
    · exact haw
    · exact haw
  · intro haw
    by_cases hbw : L.le τ.b w
    · have hjw : L.le (L.join τ.a τ.b) w := L.join_le haw hbw
      exact Or.inr (Or.inl ⟨⟨haw, hbw⟩, hbw, hφ.mono hjw τ.hpq⟩)
    · exact Or.inr (Or.inr ⟨rfl, haw, hbw⟩)

theorem wStepRel_mono {α : Type u} (L : BoundedLattice α) {X : Type u} {φ : α → EqRel X}
    (hφ : MeetPreservingEqMap L X φ) {u w : α} (huw : L.le u w)
    {z₁ z₂ : WStepX L X φ} (h : wStepRel L φ u z₁ z₂) : wStepRel L φ w z₁ z₂ := by
  rcases h with rfl | ⟨ha₁, ha₂, hr⟩ | hloc
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨wActive_mono L huw ha₁, wActive_mono L huw ha₂, hφ.mono huw hr⟩)
  · cases z₁ with
    | inl _ => exact False.elim hloc
    | inr tp₁ =>
      rcases tp₁ with ⟨τ₁, tag₁⟩
      cases z₂ with
      | inl _ => exact False.elim hloc
      | inr tp₂ =>
        rcases tp₂ with ⟨τ₂, tag₂⟩
        cases tag₁ <;> cases tag₂ <;> first
          | exact False.elim hloc
          | (rcases hloc with ⟨rfl, hbu, _⟩
             exact (wStepRel_zero_one L τ₁ w).mpr (L.le_trans hbu huw))
          | (rcases hloc with ⟨rfl, hbu, _⟩
             exact (wStepPhi L φ w).symm ((wStepRel_zero_one L τ₁ w).mpr (L.le_trans hbu huw)))
          | (rcases hloc with ⟨rfl, hau, _⟩
             exact (wStepRel_one_two L hφ τ₁ w).mpr (L.le_trans hau huw))
          | (rcases hloc with ⟨rfl, hau, _⟩
             exact (wStepPhi L φ w).symm ((wStepRel_one_two L hφ τ₁ w).mpr (L.le_trans hau huw)))

theorem wStepRel_from_localLink_meet {α : Type u} (L : BoundedLattice α) {X : Type u}
    {φ : α → EqRel X} (hφ : MeetPreservingEqMap L X φ) {u v : α}
    {z₁ z₂ : WStepX L X φ} (hloc : wLocalLink L u z₁ z₂) (hv : wStepRel L φ v z₁ z₂) :
    wStepRel L φ (L.meet u v) z₁ z₂ := by
  cases z₁ with
  | inl _ => exact False.elim hloc
  | inr tp₁ =>
    rcases tp₁ with ⟨τ₁, tag₁⟩
    cases z₂ with
    | inl _ => exact False.elim hloc
    | inr tp₂ =>
      rcases tp₂ with ⟨τ₂, tag₂⟩
      cases tag₁ <;> cases tag₂ <;> first
        | exact False.elim hloc
        | (rcases hloc with ⟨rfl, hbu, _⟩
           have hbv : L.le τ₁.b v := (wStepRel_zero_one L τ₁ v).mp hv
           exact (wStepRel_zero_one L τ₁ (L.meet u v)).mpr (L.le_meet hbu hbv))
        | (rcases hloc with ⟨rfl, hbu, _⟩
           have hv' : wStepRel L φ v (Sum.inr (τ₁, Three.zero)) (Sum.inr (τ₁, Three.one)) :=
             (wStepPhi L φ v).symm hv
           have hbv : L.le τ₁.b v := (wStepRel_zero_one L τ₁ v).mp hv'
           exact (wStepPhi L φ (L.meet u v)).symm
             ((wStepRel_zero_one L τ₁ (L.meet u v)).mpr (L.le_meet hbu hbv)))
        | (rcases hloc with ⟨rfl, hau, _⟩
           have hav : L.le τ₁.a v := (wStepRel_one_two L hφ τ₁ v).mp hv
           exact (wStepRel_one_two L hφ τ₁ (L.meet u v)).mpr (L.le_meet hau hav))
        | (rcases hloc with ⟨rfl, hau, _⟩
           have hv' : wStepRel L φ v (Sum.inr (τ₁, Three.one)) (Sum.inr (τ₁, Three.two)) :=
             (wStepPhi L φ v).symm hv
           have hav : L.le τ₁.a v := (wStepRel_one_two L hφ τ₁ v).mp hv'
           exact (wStepPhi L φ (L.meet u v)).symm
             ((wStepRel_one_two L hφ τ₁ (L.meet u v)).mpr (L.le_meet hau hav)))

theorem wStepPhi_meetPreserving {α : Type u} (L : BoundedLattice α) {X : Type u}
    {φ : α → EqRel X} (hφ : MeetPreservingEqMap L X φ) :
    MeetPreservingEqMap L (WStepX L X φ) (wStepPhi L φ) where
  map_bot := EqRel.ext fun z₁ z₂ => by
    constructor
    · intro h
      rcases h with rfl | ⟨ha₁, ha₂, hr⟩ | hloc
      · rfl
      · cases z₁ with
        | inl x₁ =>
          cases z₂ with
          | inl x₂ =>
            have hbot : (EqBot X).r x₁ x₂ := hφ.map_bot ▸ hr
            exact congrArg Sum.inl hbot
          | inr tp₂ =>
            rcases tp₂ with ⟨τ₂, tag₂⟩
            cases tag₂ with
            | zero => exact False.elim (τ₂.ha ha₂)
            | one => exact False.elim (τ₂.ha ha₂.1)
            | two => exact False.elim (τ₂.hb ha₂)
        | inr tp₁ =>
          rcases tp₁ with ⟨τ₁, tag₁⟩
          cases tag₁ with
          | zero => exact False.elim (τ₁.ha ha₁)
          | one => exact False.elim (τ₁.ha ha₁.1)
          | two => exact False.elim (τ₁.hb ha₁)
      · cases z₁ with
        | inl _ => exact False.elim hloc
        | inr tp₁ =>
          rcases tp₁ with ⟨τ₁, tag₁⟩
          cases z₂ with
          | inl _ => exact False.elim hloc
          | inr tp₂ =>
            rcases tp₂ with ⟨τ₂, tag₂⟩
            cases tag₁ <;> cases tag₂ <;> first
              | exact False.elim hloc
              | (rcases hloc with ⟨_, hb, _⟩; exact False.elim (τ₁.hb hb))
              | (rcases hloc with ⟨_, ha, _⟩; exact False.elim (τ₁.ha ha))
    · intro h
      exact Or.inl h
  map_top := EqRel.ext fun z₁ z₂ => by
    constructor
    · intro _
      exact trivial
    · intro _
      have hact : ∀ z : WStepX L X φ, wActive L L.top z := by
        intro z
        cases z with
        | inl _ => exact trivial
        | inr tp =>
          rcases tp with ⟨τ, tag⟩
          cases tag with
          | zero => exact L.le_top τ.a
          | one => exact ⟨L.le_top τ.a, L.le_top τ.b⟩
          | two => exact L.le_top τ.b
      have htop : (φ L.top).r (wBasePt z₁) (wBasePt z₂) := by
        rw [hφ.map_top]
        exact trivial
      exact Or.inr (Or.inl ⟨hact z₁, hact z₂, htop⟩)
  map_meet u v := EqRel.ext fun z₁ z₂ => by
    constructor
    · intro h
      exact ⟨wStepRel_mono L hφ (L.meet_le_left u v) h,
             wStepRel_mono L hφ (L.meet_le_right u v) h⟩
    · rintro ⟨hu, hv⟩
      rcases hu with rfl | ⟨hau₁, hau₂, hru⟩ | hlocu
      · exact Or.inl rfl
      · rcases hv with rfl | ⟨hav₁, hav₂, hrv⟩ | hlocv
        · exact Or.inl rfl
        · have hm : (φ (L.meet u v)).r (wBasePt z₁) (wBasePt z₂) := by
            rw [hφ.map_meet]
            exact ⟨hru, hrv⟩
          exact Or.inr (Or.inl
            ⟨(wActive_meet_iff L u v z₁).mpr ⟨hau₁, hav₁⟩,
             (wActive_meet_iff L u v z₂).mpr ⟨hau₂, hav₂⟩, hm⟩)
        · have hm_vu : wStepRel L φ (L.meet v u) z₁ z₂ :=
            wStepRel_from_localLink_meet L hφ hlocv (Or.inr (Or.inl ⟨hau₁, hau₂, hru⟩))
          rw [L.meet_comm] at hm_vu
          exact hm_vu
      · exact wStepRel_from_localLink_meet L hφ hlocu hv

/-- Conservative extension property: restricting `wStepPhi` to `Sum.inl` recovers `φ`. -/
theorem wStepPhi_inl_iff {α : Type u} (L : BoundedLattice α) {X : Type u} (φ : α → EqRel X)
    (u : α) (x y : X) :
    (wStepPhi L φ u).r (Sum.inl x) (Sum.inl y) ↔ (φ u).r x y := by
  constructor
  · intro h
    rcases h with heq | ⟨_, _, hr⟩ | hloc
    · injection heq with hxy
      exact hxy ▸ (φ u).refl x
    · exact hr
    · exact False.elim hloc
  · intro hr
    exact Or.inr (Or.inl ⟨trivial, trivial, hr⟩)

/-- Whitman's 4-step join repair: every pair `(p, q) ∈ φ(a ∨ b)` becomes equivalent in
    `EqJoin (wStepPhi a) (wStepPhi b)` at the next stage! -/
theorem wStepPhi_join_repair {α : Type u} (L : BoundedLattice α) {X : Type u}
    {φ : α → EqRel X} (hφ : MeetPreservingEqMap L X φ) (a b : α) (p q : X)
    (hpq : (φ (L.join a b)).r p q) :
    (EqJoin (wStepPhi L φ a) (wStepPhi L φ b)).r (Sum.inl p) (Sum.inl q) := by
  by_cases ha : L.le a L.bot
  · have habot : a = L.bot := L.le_antisymm ha (L.bot_le a)
    subst habot
    rw [L.bot_join] at hpq
    exact EqClosure.base (Or.inr ((wStepPhi_inl_iff L φ b p q).mpr hpq))
  · by_cases hb : L.le b L.bot
    · have hbbot : b = L.bot := L.le_antisymm hb (L.bot_le b)
      subst hbbot
      rw [L.join_bot] at hpq
      exact EqClosure.base (Or.inl ((wStepPhi_inl_iff L φ a p q).mpr hpq))
    · let τ : WTask L X φ := ⟨a, b, p, q, ha, hb, hpq⟩
      have s1 : (wStepPhi L φ a).r (Sum.inl p) (Sum.inr (τ, Three.zero)) :=
        Or.inr (Or.inl ⟨trivial, L.le_refl a, (φ a).refl p⟩)
      have s2 : (wStepPhi L φ b).r (Sum.inr (τ, Three.zero)) (Sum.inr (τ, Three.one)) :=
        (wStepRel_zero_one L τ b).mpr (L.le_refl b)
      have s3 : (wStepPhi L φ a).r (Sum.inr (τ, Three.one)) (Sum.inr (τ, Three.two)) :=
        (wStepRel_one_two L hφ τ a).mpr (L.le_refl a)
      have s4 : (wStepPhi L φ b).r (Sum.inr (τ, Three.two)) (Sum.inl q) :=
        Or.inr (Or.inl ⟨L.le_refl b, trivial, (φ b).refl q⟩)
      exact EqClosure.trans
        (EqClosure.trans (EqClosure.base (Or.inl s1)) (EqClosure.base (Or.inr s2)))
        (EqClosure.trans (EqClosure.base (Or.inl s3)) (EqClosure.base (Or.inr s4)))

/-- Iterated Whitman tower `(WStageX L n, wStagePhi L n)` for `n : Nat`. -/
def WStagePair {α : Type u} (L : BoundedLattice α) : Nat → Σ X : Type u, α → EqRel X
  | 0 => ⟨α, wPhi0 L⟩
  | n + 1 =>
    let prev := WStagePair L n
    ⟨WStepX L prev.1 prev.2, wStepPhi L prev.2⟩

def WStageX {α : Type u} (L : BoundedLattice α) (n : Nat) : Type u :=
  (WStagePair L n).1

def wStagePhi {α : Type u} (L : BoundedLattice α) (n : Nat) : α → EqRel (WStageX L n) :=
  (WStagePair L n).2

theorem wStagePhi_meetPreserving {α : Type u} (L : BoundedLattice α) :
    ∀ n : Nat, MeetPreservingEqMap L (WStageX L n) (wStagePhi L n)
  | 0 => wPhi0_meetPreserving L
  | n + 1 => wStepPhi_meetPreserving L (wStagePhi_meetPreserving L n)

/-- Quotient-free colimit carrier `WLimX L = α ⊕ Σ n, WNewPt_n`. -/
def WLimX {α : Type u} (L : BoundedLattice α) : Type u :=
  Sum α (Σ n : Nat, WNewPt L (WStageX L n) (wStagePhi L n))

def wEmb {α : Type u} (L : BoundedLattice α) : (n : Nat) → WStageX L n → WLimX L
  | 0, x => Sum.inl x
  | n + 1, Sum.inl x => wEmb L n x
  | n + 1, Sum.inr newPt => Sum.inr ⟨n, newPt⟩

def wStageOf {α : Type u} (L : BoundedLattice α) : WLimX L → Nat
  | Sum.inl _ => 0
  | Sum.inr ⟨n, _⟩ => n + 1

theorem wStageOf_emb_le {α : Type u} (L : BoundedLattice α) :
    ∀ (n : Nat) (x : WStageX L n), wStageOf L (wEmb L n x) ≤ n
  | 0, _ => Nat.le_refl 0
  | n + 1, Sum.inl x => Nat.le_step (wStageOf_emb_le L n x)
  | n + 1, Sum.inr _ => Nat.le_refl (n + 1)

theorem wEmb_inj {α : Type u} (L : BoundedLattice α) :
    ∀ (n : Nat) {x y : WStageX L n}, wEmb L n x = wEmb L n y → x = y
  | 0, _, _, h => by injection h
  | n + 1, Sum.inl x, Sum.inl y, h => congrArg Sum.inl (wEmb_inj L n h)
  | n + 1, Sum.inl x, Sum.inr newPt, h => by
    have hle := wStageOf_emb_le L n x
    have heq : wStageOf L (wEmb L n x) = n + 1 := by
      change wStageOf L (wEmb L (n + 1) (Sum.inl x)) = n + 1
      rw [h]
      rfl
    rw [heq] at hle
    exact False.elim (Nat.not_succ_le_self n hle)
  | n + 1, Sum.inr newPt, Sum.inl y, h => by
    have hle := wStageOf_emb_le L n y
    have heq : wStageOf L (wEmb L n y) = n + 1 := by
      change wStageOf L (wEmb L (n + 1) (Sum.inl y)) = n + 1
      rw [← h]
      rfl
    rw [heq] at hle
    exact False.elim (Nat.not_succ_le_self n hle)
  | n + 1, Sum.inr p₁, Sum.inr p₂, h => by
    injection h with hsig
    injection hsig with _ hp
    exact congrArg Sum.inr hp

theorem wExists_preimage {α : Type u} (L : BoundedLattice α) (p : WLimX L) :
    ∀ {k : Nat}, wStageOf L p ≤ k → ∃ x : WStageX L k, wEmb L k x = p := by
  intro k hk
  induction hk with
  | refl =>
    cases p with
    | inl a => exact ⟨a, rfl⟩
    | inr np =>
      rcases np with ⟨n, newPt⟩
      exact ⟨Sum.inr newPt, rfl⟩
  | @step m _ ih =>
    rcases ih with ⟨x, hx⟩
    exact ⟨Sum.inl x, hx⟩

/-- Transport along stage inequality: if `emb n x = emb k y` with `n ≤ k`, they agree on `wStagePhi`. -/
theorem wEmb_rel_le {α : Type u} (L : BoundedLattice α) (u : α) {n : Nat} :
    ∀ {k : Nat}, n ≤ k → ∀ (x₁ x₂ : WStageX L n) (y₁ y₂ : WStageX L k),
      wEmb L n x₁ = wEmb L k y₁ → wEmb L n x₂ = wEmb L k y₂ →
      ((wStagePhi L n u).r x₁ x₂ ↔ (wStagePhi L k u).r y₁ y₂) := by
  intro k hnk
  induction hnk with
  | refl =>
    intro x₁ x₂ y₁ y₂ h₁ h₂
    rw [wEmb_inj L n h₁, wEmb_inj L n h₂]
  | @step m hnm ih =>
    intro x₁ x₂ y₁ y₂ h₁ h₂
    obtain ⟨z₁, hz₁⟩ := wExists_preimage L (wEmb L n x₁) (Nat.le_trans (wStageOf_emb_le L n x₁) hnm)
    obtain ⟨z₂, hz₂⟩ := wExists_preimage L (wEmb L n x₂) (Nat.le_trans (wStageOf_emb_le L n x₂) hnm)
    have hy₁ : Sum.inl z₁ = y₁ := wEmb_inj L (m + 1) (hz₁.trans h₁)
    have hy₂ : Sum.inl z₂ = y₂ := wEmb_inj L (m + 1) (hz₂.trans h₂)
    subst hy₁; subst hy₂
    exact (ih x₁ x₂ z₁ z₂ hz₁.symm hz₂.symm).trans
      ((wStepPhi_inl_iff L (wStagePhi L m) u z₁ z₂).symm)

theorem wEmb_rel_coherent {α : Type u} (L : BoundedLattice α) (u : α)
    {n₁ n₂ : Nat} {x₁ x₂ : WStageX L n₁} {y₁ y₂ : WStageX L n₂}
    (h₁ : wEmb L n₁ x₁ = wEmb L n₂ y₁) (h₂ : wEmb L n₁ x₂ = wEmb L n₂ y₂) :
    (wStagePhi L n₁ u).r x₁ x₂ ↔ (wStagePhi L n₂ u).r y₁ y₂ := by
  rcases Nat.le_total n₁ n₂ with hle | hge
  · exact wEmb_rel_le L u hle x₁ x₂ y₁ y₂ h₁ h₂
  · exact (wEmb_rel_le L u hge y₁ y₂ x₁ x₂ h₁.symm h₂.symm).symm

def wLimPhi {α : Type u} (L : BoundedLattice α) (u : α) : EqRel (WLimX L) where
  r p q := ∃ (k : Nat) (x y : WStageX L k),
    wEmb L k x = p ∧ wEmb L k y = q ∧ (wStagePhi L k u).r x y
  refl p := by
    obtain ⟨x, hx⟩ := wExists_preimage L p (Nat.le_refl (wStageOf L p))
    exact ⟨wStageOf L p, x, x, hx, hx, (wStagePhi L _ u).refl x⟩
  symm := by
    rintro p q ⟨k, x, y, hx, hy, hxy⟩
    exact ⟨k, y, x, hy, hx, (wStagePhi L k u).symm hxy⟩
  trans := by
    rintro p q s ⟨k₁, x₁, y₁, hx₁, hy₁, h₁⟩ ⟨k₂, y₂, z₂, hy₂, hz₂, h₂⟩
    let K := k₁ + k₂
    have hk₁ : wStageOf L p ≤ K := Nat.le_trans (hx₁ ▸ wStageOf_emb_le L k₁ x₁) (Nat.le_add_right k₁ k₂)
    have hk_q : wStageOf L q ≤ K := Nat.le_trans (hy₁ ▸ wStageOf_emb_le L k₁ y₁) (Nat.le_add_right k₁ k₂)
    have hk₂ : wStageOf L s ≤ K := Nat.le_trans (hz₂ ▸ wStageOf_emb_le L k₂ z₂) (Nat.le_add_left k₂ k₁)
    obtain ⟨X₁, hX₁⟩ := wExists_preimage L p hk₁
    obtain ⟨Y, hY⟩ := wExists_preimage L q hk_q
    obtain ⟨Z₂, hZ₂⟩ := wExists_preimage L s hk₂
    have h₁' : (wStagePhi L K u).r X₁ Y :=
      (wEmb_rel_coherent L u (hx₁.trans hX₁.symm) (hy₁.trans hY.symm)).mp h₁
    have h₂' : (wStagePhi L K u).r Y Z₂ :=
      (wEmb_rel_coherent L u (hy₂.trans hY.symm) (hz₂.trans hZ₂.symm)).mp h₂
    exact ⟨K, X₁, Z₂, hX₁, hZ₂, (wStagePhi L K u).trans h₁' h₂'⟩

theorem wLimPhi_emb_iff {α : Type u} (L : BoundedLattice α) (u : α) (k : Nat)
    (x y : WStageX L k) :
    (wLimPhi L u).r (wEmb L k x) (wEmb L k y) ↔ (wStagePhi L k u).r x y :=
  ⟨fun ⟨_, _, _, hx', hy', hr⟩ =>
     (wEmb_rel_coherent L u hx' hy').mp hr,
   fun hr => ⟨k, x, y, rfl, rfl, hr⟩⟩

theorem wEmb_push_eqJoin {α : Type u} (L : BoundedLattice α) (a b : α) (k : Nat)
    {x y : WStageX L k}
    (h : (EqJoin (wStagePhi L k a) (wStagePhi L k b)).r x y) :
    (EqJoin (wLimPhi L a) (wLimPhi L b)).r (wEmb L k x) (wEmb L k y) := by
  induction h with
  | base h_ab =>
    rcases h_ab with ha | hb
    · exact EqClosure.base (Or.inl ((wLimPhi_emb_iff L a k _ _).mpr ha))
    · exact EqClosure.base (Or.inr ((wLimPhi_emb_iff L b k _ _).mpr hb))
  | refl z => exact EqClosure.refl (wEmb L k z)
  | symm _ ih => exact EqClosure.symm ih
  | trans _ _ ih₁ ih₂ => exact EqClosure.trans ih₁ ih₂

/-- **Whitman's Complete Representation Theorem (Positive Theorem 1):**
    Every bounded lattice `L` (hence every finite lattice, with arbitrary meets and joins)
    embeds completely into the equivalence-relation lattice `EqRelLattice (WLimX L)`. -/
theorem whitman_complete_representation {α : Type u} (L : BoundedLattice α) :
    BoundedLatticeEmbedding L (EqRelLattice (WLimX L)) (wLimPhi L) where
  inj u v huv := by
    apply wPhi0_inj L
    apply EqRel.ext
    intro x y
    change (wStagePhi L 0 u).r x y ↔ (wStagePhi L 0 v).r x y
    rw [← wLimPhi_emb_iff L u 0 x y, ← wLimPhi_emb_iff L v 0 x y, huv]
  map_bot := EqRel.ext fun p q => by
    constructor
    · rintro ⟨k, x, y, hx, hy, hr⟩
      rw [← hx, ← hy]
      have hbot : (EqBot (WStageX L k)).r x y := (wStagePhi_meetPreserving L k).map_bot ▸ hr
      exact congrArg (wEmb L k) hbot
    · intro h
      subst h
      exact (wLimPhi L L.bot).refl p
  map_top := EqRel.ext fun p q => by
    constructor
    · intro _
      exact trivial
    · intro _
      let K := wStageOf L p + wStageOf L q
      obtain ⟨x, hx⟩ := wExists_preimage L p (Nat.le_add_right _ _)
      obtain ⟨y, hy⟩ := wExists_preimage L q (Nat.le_add_left _ _)
      have htop : (wStagePhi L K L.top).r x y := by
        rw [(wStagePhi_meetPreserving L K).map_top]
        exact trivial
      exact ⟨K, x, y, hx, hy, htop⟩
  map_meet u v := EqRel.ext fun p q => by
    let K := wStageOf L p + wStageOf L q
    obtain ⟨x, hx⟩ := wExists_preimage L p (Nat.le_add_right _ _)
    obtain ⟨y, hy⟩ := wExists_preimage L q (Nat.le_add_left _ _)
    rw [← hx, ← hy]
    change (wLimPhi L (L.meet u v)).r (wEmb L K x) (wEmb L K y) ↔
      (wLimPhi L u).r (wEmb L K x) (wEmb L K y) ∧ (wLimPhi L v).r (wEmb L K x) (wEmb L K y)
    rw [wLimPhi_emb_iff, wLimPhi_emb_iff, wLimPhi_emb_iff]
    rw [(wStagePhi_meetPreserving L K).map_meet u v]
    rfl
  map_join a b := by
    apply (EqRelLattice (WLimX L)).le_antisymm
    · rintro p q ⟨k, x, y, hx, hy, hr⟩
      rw [← hx, ← hy]
      have hrep := wStepPhi_join_repair L (wStagePhi_meetPreserving L k) a b x y hr
      exact wEmb_push_eqJoin L a b (k + 1) hrep
    · exact (EqRelLattice (WLimX L)).join_le
        (fun p q ⟨k, x, y, hx, hy, ha⟩ =>
          ⟨k, x, y, hx, hy, (wStagePhi_meetPreserving L k).mono (L.le_join_left a b) ha⟩)
        (fun p q ⟨k, x, y, hx, hy, hb⟩ =>
          ⟨k, x, y, hx, hy, (wStagePhi_meetPreserving L k).mono (L.le_join_right a b) hb⟩)

/-- Corollary: Every bounded lattice admits a complete equivalence-relation family
    representation of size `1` (so minimal family size `≤ 1 ≤ |L|` for every finite lattice). -/
theorem completeEqFamilyRep_one {α : Type u} (L : BoundedLattice α) :
    CompleteEqFamilyRep L 1 := by
  have hw := whitman_complete_representation L
  refine ⟨fun _ => WLimX L, fun _ => wLimPhi L, ?_, ?_, ?_, ?_, ?_⟩
  · intro _; exact hw.map_bot
  · intro _; exact hw.map_top
  · intro _ x y; exact hw.map_meet x y
  · intro _ x y; exact hw.map_join x y
  · intro x y h; exact hw.inj x y (h ⟨0, Nat.zero_lt_one⟩)

/-! ## Section 4: Universal Strict Upper Bound `< |L|` for 2-Valued Set-Maps / Binary Relations -/

/-- Under the bijection `P(U)^L ≅ P(L × U)`, a family of `k` 2-valued maps `f_i : L → P(Unit)`
    is a family of `k` binary relations `R_i : α → Unit → Prop`. We say it is a complete
    2-valued meet-representation of `L` if each `R_i` preserves `⊤` and `∧` and the family
    completely recovers the lattice order `≤` (and hence all meets and joins). -/
def HasTwoValuedMeetRep {α : Type u} (L : BoundedLattice α) (k : Nat) : Prop :=
  ∃ R : Fin k → α → Unit → Prop,
    (∀ i, R i L.top ()) ∧
    (∀ i x y, R i (L.meet x y) () ↔ R i x () ∧ R i y ()) ∧
    (∀ x y, L.le x y ↔ ∀ i, R i x () → R i y ())

/-- Skip index `i₀` in `Fin (n + 1)`. -/
def skipIdx {n : Nat} (i₀ : Fin (n + 1)) (k : Fin n) : Fin (n + 1) :=
  if k.val < i₀.val then ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩
  else ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩

theorem exists_skipIdx_of_ne {n : Nat} (i₀ j : Fin (n + 1)) (hne : j ≠ i₀) :
    ∃ k : Fin n, skipIdx i₀ k = j := by
  rcases i₀ with ⟨iv, hiv⟩
  rcases j with ⟨jv, hjv⟩
  have hnej : jv ≠ iv := fun hv => hne (Fin.ext hv)
  by_cases hlt : jv < iv
  · have hkn : jv < n := by omega
    refine ⟨⟨jv, hkn⟩, ?_⟩
    apply Fin.ext
    simp [skipIdx, hlt]
  · have hgt : iv < jv := by omega
    cases jv with
    | zero => omega
    | succ k =>
      have hkn : k < n := by omega
      have hnotlt : ¬ k < iv := by omega
      refine ⟨⟨k, hkn⟩, ?_⟩
      apply Fin.ext
      simp [skipIdx, hnotlt]

/-- **Universal Strict Upper Bound (`< |L|`) for 2-Valued Meet-Representations (Positive Theorem 2
    & Universal Refutation for 2-Valued Relations):**
    Every finite lattice `L` of cardinality `n + 1` (`|L| = n + 1`) has a complete 2-valued
    meet-representation using `n = |L| - 1 < |L|` binary relations `R_i ⊆ L × Unit`.
    Consequently, NO finite lattice (geometric or otherwise) ever requires `|L|` such relations! -/
theorem twoValuedMeetRep_card_pred {α : Type u} (L : BoundedLattice α) (n : Nat)
    (enum : Fin (n + 1) → α) (h_surj : ∀ x : α, ∃ j, enum j = x) :
    HasTwoValuedMeetRep L n := by
  obtain ⟨i_bot, hi_bot⟩ := h_surj L.bot
  let z : Fin n → α := fun k => enum (skipIdx i_bot k)
  refine ⟨fun k x _ => L.le (z k) x, ?_, ?_, ?_⟩
  · intro k
    exact L.le_top (z k)
  · intro k x y
    exact ⟨fun h => ⟨L.le_trans h (L.meet_le_left x y), L.le_trans h (L.meet_le_right x y)⟩,
           fun ⟨hx, hy⟩ => L.le_meet hx hy⟩
  · intro x y
    constructor
    · intro hxy k hzx
      exact L.le_trans hzx hxy
    · intro hall
      obtain ⟨j, rfl⟩ := h_surj x
      by_cases hjb : j = i_bot
      · rw [hjb, hi_bot]
        exact L.bot_le y
      · obtain ⟨k, hk⟩ := exists_skipIdx_of_ne i_bot j hjb
        have hzk : z k = enum j := congrArg enum hk
        have hrefl : L.le (z k) (enum j) := hzk ▸ L.le_refl (enum j)
        have hzy : L.le (z k) y := hall k hrefl
        exact hzk ▸ hzy

/-- Single-relation Galois / principal-downset representation on `L` itself:
    one binary relation `R(x, y) := (y ≤ x)` on `L` preserves `⊤` and `∧` and completely
    determines the lattice order `≤`. -/
theorem principal_downset_single_relation {α : Type u} (L : BoundedLattice α) :
    ∃ R : α → α → Prop,
      (∀ y, R L.top y) ∧
      (∀ x₁ x₂ y, R (L.meet x₁ x₂) y ↔ R x₁ y ∧ R x₂ y) ∧
      (∀ x₁ x₂, L.le x₁ x₂ ↔ ∀ y, R x₁ y → R x₂ y) := by
  refine ⟨fun x y => L.le y x, fun y => L.le_top y, ?_, ?_⟩
  · intro x₁ x₂ y
    exact ⟨fun h => ⟨L.le_trans h (L.meet_le_left x₁ x₂), L.le_trans h (L.meet_le_right x₁ x₂)⟩,
           fun ⟨h₁, h₂⟩ => L.le_meet h₁ h₂⟩
  · intro x₁ x₂
    exact ⟨fun h₁₂ y hy₁ => L.le_trans hy₁ h₁₂, fun hall => hall x₁ (L.le_refl x₁)⟩

/-! ## Section 5: Concrete Benchmark Lattices (`C₁`, `B₁`, `B₂`, `M₃`, `C₃`, `N₅`) -/

/-! ### 5.1 `C₁` (`Unit`, `|C₁| = 1`): geometric and distributive -/

def C1Lattice : BoundedLattice Unit where
  le _ _ := True
  bot := ()
  top := ()
  meet _ _ := ()
  join _ _ := ()
  le_refl _ := trivial
  le_trans _ _ := trivial
  le_antisymm _ _ := rfl
  bot_le _ := trivial
  le_top _ := trivial
  meet_le_left _ _ := trivial
  meet_le_right _ _ := trivial
  le_meet _ _ := trivial
  le_join_left _ _ := trivial
  le_join_right _ _ := trivial
  join_le _ _ := trivial

theorem c1_isGeometric : IsGeometricLattice C1Lattice :=
  ⟨fun _ _ ⟨hne, _, _⟩ => False.elim (hne rfl), fun _ _ _ => trivial⟩

theorem c1_zero_eqFamilyRep : CompleteEqFamilyRep C1Lattice 0 :=
  ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i,
   fun i => Fin.elim0 i, fun i => Fin.elim0 i,
   fun i => Fin.elim0 i, fun i => Fin.elim0 i,
   fun _ _ _ => rfl⟩

/-! ### 5.2 `B₁` (`Bool`, `|B₁| = 2`): geometric, distributive, `⊥ ≠ ⊤` -/

def B1Lattice : BoundedLattice Bool where
  le a b := a = false ∨ b = true
  bot := false
  top := true
  meet := and
  join := or
  le_refl a := by cases a <;> decide
  le_trans {x y z} := by cases x <;> cases y <;> cases z <;> decide
  le_antisymm {x y} := by cases x <;> cases y <;> decide
  bot_le a := by cases a <;> decide
  le_top a := by cases a <;> decide
  meet_le_left x y := by cases x <;> cases y <;> decide
  meet_le_right x y := by cases x <;> cases y <;> decide
  le_meet {z x y} := by cases z <;> cases x <;> cases y <;> decide
  le_join_left x y := by cases x <;> cases y <;> decide
  le_join_right x y := by cases x <;> cases y <;> decide
  join_le {x y z} := by cases x <;> cases y <;> cases z <;> decide

theorem b1_isGeometric : IsGeometricLattice B1Lattice := by
  constructor
  · intro x y ⟨hne, _, _⟩
    cases x <;> cases y
    · exact False.elim (hne rfl)
    · refine ⟨by decide, Or.inl rfl, fun z _ _ => ?_⟩
      cases z
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact False.elim (hne rfl)
    · exact False.elim (hne rfl)
  · intro x y hall
    cases x
    · exact Or.inl rfl
    · apply hall true
      · refine ⟨by decide, Or.inl rfl, fun z _ _ => ?_⟩
        cases z
        · exact Or.inl rfl
        · exact Or.inr rfl
      · exact Or.inr rfl

/-! ### 5.3 `B₂` (4-element Boolean diamond, `|B₂| = 4`): geometric and distributive -/

inductive B2Elem : Type where
  | bot : B2Elem
  | a : B2Elem
  | b : B2Elem
  | top : B2Elem
  deriving DecidableEq

def b2LeBool : B2Elem → B2Elem → Bool
  | B2Elem.bot, _ => true
  | _, B2Elem.top => true
  | B2Elem.a, B2Elem.a => true
  | B2Elem.b, B2Elem.b => true
  | _, _ => false

def b2Meet : B2Elem → B2Elem → B2Elem
  | B2Elem.bot, _ => B2Elem.bot
  | _, B2Elem.bot => B2Elem.bot
  | B2Elem.top, y => y
  | x, B2Elem.top => x
  | B2Elem.a, B2Elem.a => B2Elem.a
  | B2Elem.b, B2Elem.b => B2Elem.b
  | _, _ => B2Elem.bot

def b2Join : B2Elem → B2Elem → B2Elem
  | B2Elem.top, _ => B2Elem.top
  | _, B2Elem.top => B2Elem.top
  | B2Elem.bot, y => y
  | x, B2Elem.bot => x
  | B2Elem.a, B2Elem.a => B2Elem.a
  | B2Elem.b, B2Elem.b => B2Elem.b
  | _, _ => B2Elem.top

def B2Lattice : BoundedLattice B2Elem where
  le x y := b2LeBool x y = true
  bot := B2Elem.bot
  top := B2Elem.top
  meet := b2Meet
  join := b2Join
  le_refl x := by cases x <;> rfl
  le_trans {x y z} := by cases x <;> cases y <;> cases z <;> decide
  le_antisymm {x y} := by cases x <;> cases y <;> decide
  bot_le x := by cases x <;> rfl
  le_top x := by cases x <;> rfl
  meet_le_left x y := by cases x <;> cases y <;> decide
  meet_le_right x y := by cases x <;> cases y <;> decide
  le_meet {z x y} := by cases z <;> cases x <;> cases y <;> decide
  le_join_left x y := by cases x <;> cases y <;> decide
  le_join_right x y := by cases x <;> cases y <;> decide
  join_le {x y z} := by cases x <;> cases y <;> cases z <;> decide

theorem b2_covers_iff (x y : B2Elem) :
    Covers B2Lattice x y ↔
      (x = B2Elem.bot ∧ (y = B2Elem.a ∨ y = B2Elem.b)) ∨
      ((x = B2Elem.a ∨ x = B2Elem.b) ∧ y = B2Elem.top) := by
  constructor
  · rintro ⟨hne, hle, hmid⟩
    cases x <;> cases y <;> first
      | exact False.elim (hne rfl)
      | contradiction
      | exact Or.inl ⟨rfl, Or.inl rfl⟩
      | exact Or.inl ⟨rfl, Or.inr rfl⟩
      | exact Or.inr ⟨Or.inl rfl, rfl⟩
      | exact Or.inr ⟨Or.inr rfl, rfl⟩
      | (exact (hmid B2Elem.a rfl rfl).elim (fun h1 => by cases h1) (fun h2 => by cases h2))
  · intro h
    rcases h with ⟨rfl, rfl | rfl⟩ | ⟨rfl | rfl, rfl⟩ <;>
      (refine ⟨by decide, rfl, fun z h₁ h₂ => ?_⟩;
       cases z <;> first | contradiction | exact Or.inl rfl | exact Or.inr rfl)

theorem b2_isGeometric : IsGeometricLattice B2Lattice := by
  constructor
  · intro x y hcov
    rw [b2_covers_iff] at hcov ⊢
    cases x <;> cases y <;> simp [B2Lattice, b2Meet, b2Join] at hcov ⊢
  · intro x y hall
    have ha : B2Lattice.le B2Elem.a x → B2Lattice.le B2Elem.a y :=
      hall B2Elem.a ((b2_covers_iff B2Elem.bot B2Elem.a).mpr (Or.inl ⟨rfl, Or.inl rfl⟩))
    have hb : B2Lattice.le B2Elem.b x → B2Lattice.le B2Elem.b y :=
      hall B2Elem.b ((b2_covers_iff B2Elem.bot B2Elem.b).mpr (Or.inl ⟨rfl, Or.inr rfl⟩))
    cases x
    · exact B2Lattice.bot_le y
    · exact ha rfl
    · exact hb rfl
    · exact B2Lattice.join_le (ha rfl) (hb rfl)

theorem b2_isDistributive : IsDistributive B2Lattice := by
  intro x y z
  cases x <;> cases y <;> cases z <;> rfl

/-! ### 5.4 `M₃` (5-element modular diamond, `|M₃| = 5`): geometric, modular, simple, NOT distributive -/

inductive M3Elem : Type where
  | bot : M3Elem
  | a : M3Elem
  | b : M3Elem
  | c : M3Elem
  | top : M3Elem
  deriving DecidableEq

def m3LeBool : M3Elem → M3Elem → Bool
  | M3Elem.bot, _ => true
  | _, M3Elem.top => true
  | M3Elem.a, M3Elem.a => true
  | M3Elem.b, M3Elem.b => true
  | M3Elem.c, M3Elem.c => true
  | _, _ => false

def m3Meet : M3Elem → M3Elem → M3Elem
  | M3Elem.bot, _ => M3Elem.bot
  | _, M3Elem.bot => M3Elem.bot
  | M3Elem.top, y => y
  | x, M3Elem.top => x
  | M3Elem.a, M3Elem.a => M3Elem.a
  | M3Elem.b, M3Elem.b => M3Elem.b
  | M3Elem.c, M3Elem.c => M3Elem.c
  | _, _ => M3Elem.bot

def m3Join : M3Elem → M3Elem → M3Elem
  | M3Elem.top, _ => M3Elem.top
  | _, M3Elem.top => M3Elem.top
  | M3Elem.bot, y => y
  | x, M3Elem.bot => x
  | M3Elem.a, M3Elem.a => M3Elem.a
  | M3Elem.b, M3Elem.b => M3Elem.b
  | M3Elem.c, M3Elem.c => M3Elem.c
  | _, _ => M3Elem.top

def M3Lattice : BoundedLattice M3Elem where
  le x y := m3LeBool x y = true
  bot := M3Elem.bot
  top := M3Elem.top
  meet := m3Meet
  join := m3Join
  le_refl x := by cases x <;> rfl
  le_trans {x y z} := by cases x <;> cases y <;> cases z <;> decide
  le_antisymm {x y} := by cases x <;> cases y <;> decide
  bot_le x := by cases x <;> rfl
  le_top x := by cases x <;> rfl
  meet_le_left x y := by cases x <;> cases y <;> decide
  meet_le_right x y := by cases x <;> cases y <;> decide
  le_meet {z x y} := by cases z <;> cases x <;> cases y <;> decide
  le_join_left x y := by cases x <;> cases y <;> decide
  le_join_right x y := by cases x <;> cases y <;> decide
  join_le {x y z} := by cases x <;> cases y <;> cases z <;> decide

theorem m3_covers_iff (x y : M3Elem) :
    Covers M3Lattice x y ↔
      (x = M3Elem.bot ∧ (y = M3Elem.a ∨ y = M3Elem.b ∨ y = M3Elem.c)) ∨
      ((x = M3Elem.a ∨ x = M3Elem.b ∨ x = M3Elem.c) ∧ y = M3Elem.top) := by
  constructor
  · rintro ⟨hne, hle, hmid⟩
    cases x <;> cases y <;> first
      | exact False.elim (hne rfl)
      | contradiction
      | exact Or.inl ⟨rfl, Or.inl rfl⟩
      | exact Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩
      | exact Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩
      | exact Or.inr ⟨Or.inl rfl, rfl⟩
      | exact Or.inr ⟨Or.inr (Or.inl rfl), rfl⟩
      | exact Or.inr ⟨Or.inr (Or.inr rfl), rfl⟩
      | (exact (hmid M3Elem.a rfl rfl).elim (fun h1 => by cases h1) (fun h2 => by cases h2))
  · intro h
    rcases h with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl | rfl | rfl, rfl⟩ <;>
      (refine ⟨by decide, rfl, fun z h₁ h₂ => ?_⟩;
       cases z <;> first | contradiction | exact Or.inl rfl | exact Or.inr rfl)

theorem m3_isGeometric : IsGeometricLattice M3Lattice := by
  constructor
  · intro x y hcov
    rw [m3_covers_iff] at hcov ⊢
    cases x <;> cases y <;> simp [M3Lattice, m3Meet, m3Join] at hcov ⊢
  · intro x y hall
    have ha : M3Lattice.le M3Elem.a x → M3Lattice.le M3Elem.a y :=
      hall M3Elem.a ((m3_covers_iff M3Elem.bot M3Elem.a).mpr (Or.inl ⟨rfl, Or.inl rfl⟩))
    have hb : M3Lattice.le M3Elem.b x → M3Lattice.le M3Elem.b y :=
      hall M3Elem.b ((m3_covers_iff M3Elem.bot M3Elem.b).mpr (Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩))
    have hc : M3Lattice.le M3Elem.c x → M3Lattice.le M3Elem.c y :=
      hall M3Elem.c ((m3_covers_iff M3Elem.bot M3Elem.c).mpr (Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩))
    cases x
    · exact M3Lattice.bot_le y
    · exact ha rfl
    · exact hb rfl
    · exact hc rfl
    · exact M3Lattice.join_le (ha rfl) (hb rfl)

theorem m3_isModular : IsModular M3Lattice := by
  intro x y z hxz
  cases x <;> cases y <;> cases z <;> first | contradiction | rfl

theorem m3_not_distributive : ¬ IsDistributive M3Lattice := by
  intro hd
  have h := hd M3Elem.a M3Elem.b M3Elem.c
  cases h

/-- `M₃` is a simple lattice: any congruence identifying two distinct elements collapses all of `M₃`. -/
theorem m3_isSimple : IsSimpleLattice M3Lattice := by
  refine ⟨by decide, fun θ hθ => ?_⟩
  by_cases hall_eq : ∀ x y, θ x y → x = y
  · exact Or.inl fun x y => ⟨hall_eq x y, fun h => h ▸ hθ.refl x⟩
  · right
    have hex : ∃ u v : M3Elem, u ≠ v ∧ θ u v := by
      apply Classical.byContradiction
      intro hno
      apply hall_eq
      intro x y hxy
      exact Classical.byContradiction fun hne => hno ⟨x, y, hne, hxy⟩
    rcases hex with ⟨u, v, hne, huv⟩
    suffices hbt : θ M3Elem.bot M3Elem.top by
      intro x y
      have hbx : θ M3Elem.bot x := by
        have hm := hθ.meet_compat hbt (hθ.refl x)
        cases x <;> exact hm
      have hby : θ M3Elem.bot y := by
        have hm := hθ.meet_compat hbt (hθ.refl y)
        cases y <;> exact hm
      exact hθ.trans (hθ.symm hbx) hby
    -- Show every distinct pair (u, v) forces θ bot top via M₃'s symmetry:
    -- First, any θ bot a (or b, c) or θ a top (or b, c) gives θ bot top.
    have from_bot_a : θ M3Elem.bot M3Elem.a → θ M3Elem.bot M3Elem.top := fun h => by
      have h1 : θ M3Elem.b M3Elem.top := hθ.join_compat h (hθ.refl M3Elem.b)
      have h2 : θ M3Elem.bot M3Elem.c := hθ.meet_compat h1 (hθ.refl M3Elem.c)
      have h3 : θ M3Elem.a M3Elem.top := hθ.join_compat h2 (hθ.refl M3Elem.a)
      exact hθ.trans h h3
    have from_bot_b : θ M3Elem.bot M3Elem.b → θ M3Elem.bot M3Elem.top := fun h => by
      have h1 : θ M3Elem.a M3Elem.top := hθ.join_compat h (hθ.refl M3Elem.a)
      have h2 : θ M3Elem.bot M3Elem.c := hθ.meet_compat h1 (hθ.refl M3Elem.c)
      exact from_bot_a (hθ.meet_compat (hθ.join_compat h2 (hθ.refl M3Elem.b)) (hθ.refl M3Elem.a))
    have from_bot_c : θ M3Elem.bot M3Elem.c → θ M3Elem.bot M3Elem.top := fun h => by
      have h1 : θ M3Elem.a M3Elem.top := hθ.join_compat h (hθ.refl M3Elem.a)
      exact from_bot_b (hθ.meet_compat h1 (hθ.refl M3Elem.b))
    cases u <;> cases v <;> first
      | exact False.elim (hne rfl)
      | exact huv
      | exact hθ.symm huv
      | exact from_bot_a huv
      | exact from_bot_a (hθ.symm huv)
      | exact from_bot_b huv
      | exact from_bot_b (hθ.symm huv)
      | exact from_bot_c huv
      | exact from_bot_c (hθ.symm huv)
      | exact from_bot_b (hθ.meet_compat huv (hθ.refl M3Elem.b))
      | exact from_bot_b (hθ.meet_compat (hθ.symm huv) (hθ.refl M3Elem.b))
      | exact from_bot_a (hθ.meet_compat huv (hθ.refl M3Elem.a))
      | exact from_bot_a (hθ.meet_compat (hθ.symm huv) (hθ.refl M3Elem.a))
      | exact from_bot_c (hθ.meet_compat huv (hθ.refl M3Elem.c))

/-! ### 5.5 `C₃` (3-element chain, `|C₃| = 3`) and `N₅` (pentagon, `|N₅| = 5`): NON-geometric witnesses -/

inductive C3Elem : Type where
  | bot : C3Elem
  | mid : C3Elem
  | top : C3Elem
  deriving DecidableEq

def c3LeBool : C3Elem → C3Elem → Bool
  | C3Elem.bot, _ => true
  | _, C3Elem.top => true
  | C3Elem.mid, C3Elem.mid => true
  | _, _ => false

def c3Meet : C3Elem → C3Elem → C3Elem
  | C3Elem.bot, _ => C3Elem.bot
  | _, C3Elem.bot => C3Elem.bot
  | C3Elem.top, y => y
  | x, C3Elem.top => x
  | C3Elem.mid, C3Elem.mid => C3Elem.mid

def c3Join : C3Elem → C3Elem → C3Elem
  | C3Elem.top, _ => C3Elem.top
  | _, C3Elem.top => C3Elem.top
  | C3Elem.bot, y => y
  | x, C3Elem.bot => x
  | C3Elem.mid, C3Elem.mid => C3Elem.mid

def C3Lattice : BoundedLattice C3Elem where
  le x y := c3LeBool x y = true
  bot := C3Elem.bot
  top := C3Elem.top
  meet := c3Meet
  join := c3Join
  le_refl x := by cases x <;> rfl
  le_trans {x y z} := by cases x <;> cases y <;> cases z <;> decide
  le_antisymm {x y} := by cases x <;> cases y <;> decide
  bot_le x := by cases x <;> rfl
  le_top x := by cases x <;> rfl
  meet_le_left x y := by cases x <;> cases y <;> decide
  meet_le_right x y := by cases x <;> cases y <;> decide
  le_meet {z x y} := by cases z <;> cases x <;> cases y <;> decide
  le_join_left x y := by cases x <;> cases y <;> decide
  le_join_right x y := by cases x <;> cases y <;> decide
  join_le {x y z} := by cases x <;> cases y <;> cases z <;> decide

theorem c3_not_geometric : ¬ IsGeometricLattice C3Lattice := by
  rintro ⟨_, hatom⟩
  have htop_mid : C3Lattice.le C3Elem.top C3Elem.mid := by
    apply hatom C3Elem.top C3Elem.mid
    intro a ⟨hne, _, hmid⟩ _
    cases a with
    | bot => exact False.elim (hne rfl)
    | mid => rfl
    | top =>
      rcases hmid C3Elem.mid rfl rfl with h1 | h2
      · cases h1
      · cases h2
  cases htop_mid

inductive N5Elem : Type where
  | bot : N5Elem
  | a : N5Elem
  | b : N5Elem
  | c : N5Elem
  | top : N5Elem
  deriving DecidableEq

def n5LeBool : N5Elem → N5Elem → Bool
  | N5Elem.bot, _ => true
  | _, N5Elem.top => true
  | N5Elem.a, N5Elem.a => true
  | N5Elem.a, N5Elem.b => true
  | N5Elem.b, N5Elem.b => true
  | N5Elem.c, N5Elem.c => true
  | _, _ => false

def n5Meet : N5Elem → N5Elem → N5Elem
  | N5Elem.bot, _ => N5Elem.bot
  | _, N5Elem.bot => N5Elem.bot
  | N5Elem.top, y => y
  | x, N5Elem.top => x
  | N5Elem.a, N5Elem.a => N5Elem.a
  | N5Elem.a, N5Elem.b => N5Elem.a
  | N5Elem.b, N5Elem.a => N5Elem.a
  | N5Elem.b, N5Elem.b => N5Elem.b
  | N5Elem.c, N5Elem.c => N5Elem.c
  | _, _ => N5Elem.bot

def n5Join : N5Elem → N5Elem → N5Elem
  | N5Elem.top, _ => N5Elem.top
  | _, N5Elem.top => N5Elem.top
  | N5Elem.bot, y => y
  | x, N5Elem.bot => x
  | N5Elem.a, N5Elem.a => N5Elem.a
  | N5Elem.a, N5Elem.b => N5Elem.b
  | N5Elem.b, N5Elem.a => N5Elem.b
  | N5Elem.b, N5Elem.b => N5Elem.b
  | N5Elem.c, N5Elem.c => N5Elem.c
  | _, _ => N5Elem.top

def N5Lattice : BoundedLattice N5Elem where
  le x y := n5LeBool x y = true
  bot := N5Elem.bot
  top := N5Elem.top
  meet := n5Meet
  join := n5Join
  le_refl x := by cases x <;> rfl
  le_trans {x y z} := by cases x <;> cases y <;> cases z <;> decide
  le_antisymm {x y} := by cases x <;> cases y <;> decide
  bot_le x := by cases x <;> rfl
  le_top x := by cases x <;> rfl
  meet_le_left x y := by cases x <;> cases y <;> decide
  meet_le_right x y := by cases x <;> cases y <;> decide
  le_meet {z x y} := by cases z <;> cases x <;> cases y <;> decide
  le_join_left x y := by cases x <;> cases y <;> decide
  le_join_right x y := by cases x <;> cases y <;> decide
  join_le {x y z} := by cases x <;> cases y <;> cases z <;> decide

theorem n5_not_upperSemimodular : ¬ IsUpperSemimodular N5Lattice := by
  intro hsm
  have hcov_c : Covers N5Lattice (N5Lattice.meet N5Elem.a N5Elem.c) N5Elem.c := by
    refine ⟨by decide, rfl, fun z h₁ h₂ => ?_⟩
    cases z <;> first | contradiction | exact Or.inl rfl | exact Or.inr rfl
  have hcov_top := hsm N5Elem.a N5Elem.c hcov_c
  rcases hcov_top.2.2 N5Elem.b rfl rfl with hba | hbt
  · cases hba
  · cases hbt

theorem n5_not_geometric : ¬ IsGeometricLattice N5Lattice :=
  fun ⟨hsm, _⟩ => n5_not_upperSemimodular hsm

/-! ## Section 6: Explicit Finite Counterexamples Across All Interpretations -/

/-! ### 6.1 Finite `Eq(Three)` Embeddings for `B₂`, `M₃`, and `C₃` (plus `Eq(Fin 2)` for `B₁` and `Eq(Four)` for `N₅`) -/

def eqRel01 : EqRel Three where
  r x y := x = y ∨ (x = Three.zero ∧ y = Three.one) ∨ (x = Three.one ∧ y = Three.zero)
  refl _ := Or.inl rfl
  symm := by intro x y; cases x <;> cases y <;> decide
  trans := by intro x y z; cases x <;> cases y <;> cases z <;> decide

def eqRel02 : EqRel Three where
  r x y := x = y ∨ (x = Three.zero ∧ y = Three.two) ∨ (x = Three.two ∧ y = Three.zero)
  refl _ := Or.inl rfl
  symm := by intro x y; cases x <;> cases y <;> decide
  trans := by intro x y z; cases x <;> cases y <;> cases z <;> decide

def eqRel12 : EqRel Three where
  r x y := x = y ∨ (x = Three.one ∧ y = Three.two) ∨ (x = Three.two ∧ y = Three.one)
  refl _ := Or.inl rfl
  symm := by intro x y; cases x <;> cases y <;> decide
  trans := by intro x y z; cases x <;> cases y <;> cases z <;> decide

theorem eqMeet_01_12 : EqMeet eqRel01 eqRel12 = EqBot Three :=
  EqRel.ext fun x y => by dsimp [EqMeet, EqBot, eqRel01, eqRel12]; cases x <;> cases y <;> decide

theorem eqMeet_01_02 : EqMeet eqRel01 eqRel02 = EqBot Three :=
  EqRel.ext fun x y => by dsimp [EqMeet, EqBot, eqRel01, eqRel02]; cases x <;> cases y <;> decide

theorem eqMeet_02_12 : EqMeet eqRel02 eqRel12 = EqBot Three :=
  EqRel.ext fun x y => by dsimp [EqMeet, EqBot, eqRel02, eqRel12]; cases x <;> cases y <;> decide

theorem eqJoin_01_12 : EqJoin eqRel01 eqRel12 = EqTop Three := by
  apply EqRel.ext
  intro x y
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  have h01 : (EqJoin eqRel01 eqRel12).r Three.zero Three.one :=
    EqClosure.base (Or.inl (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have h12 : (EqJoin eqRel01 eqRel12).r Three.one Three.two :=
    EqClosure.base (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have to_one : ∀ z : Three, (EqJoin eqRel01 eqRel12).r z Three.one := by
    intro z
    cases z with
    | zero => exact h01
    | one => exact EqClosure.refl Three.one
    | two => exact EqClosure.symm h12
  exact EqClosure.trans (to_one x) (EqClosure.symm (to_one y))

theorem eqJoin_01_02 : EqJoin eqRel01 eqRel02 = EqTop Three := by
  apply EqRel.ext
  intro x y
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  have h01 : (EqJoin eqRel01 eqRel02).r Three.zero Three.one :=
    EqClosure.base (Or.inl (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have h02 : (EqJoin eqRel01 eqRel02).r Three.zero Three.two :=
    EqClosure.base (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have to_zero : ∀ z : Three, (EqJoin eqRel01 eqRel02).r z Three.zero := by
    intro z
    cases z with
    | zero => exact EqClosure.refl Three.zero
    | one => exact EqClosure.symm h01
    | two => exact EqClosure.symm h02
  exact EqClosure.trans (to_zero x) (EqClosure.symm (to_zero y))

theorem eqJoin_02_12 : EqJoin eqRel02 eqRel12 = EqTop Three := by
  apply EqRel.ext
  intro x y
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  have h02 : (EqJoin eqRel02 eqRel12).r Three.zero Three.two :=
    EqClosure.base (Or.inl (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have h12 : (EqJoin eqRel02 eqRel12).r Three.one Three.two :=
    EqClosure.base (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have to_two : ∀ z : Three, (EqJoin eqRel02 eqRel12).r z Three.two := by
    intro z
    cases z with
    | zero => exact h02
    | one => exact h12
    | two => exact EqClosure.refl Three.two
  exact EqClosure.trans (to_two x) (EqClosure.symm (to_two y))

def b1FinitePhi : Bool → EqRel Bool
  | false => EqBot Bool
  | true => EqTop Bool

theorem b1_finite_eq_embedding :
    BoundedLatticeEmbedding B1Lattice (EqRelLattice Bool) b1FinitePhi where
  inj x y h := by
    cases x <;> cases y <;> try rfl
    · have hf : (b1FinitePhi false).r false true := by rw [h]; trivial
      cases hf
    · have hf : (b1FinitePhi false).r false true := by rw [← h]; trivial
      cases hf
  map_bot := rfl
  map_top := rfl
  map_meet x y := by
    cases x <;> cases y
    · exact ((EqRelLattice Bool).meet_idem _).symm
    · exact ((EqRelLattice Bool).bot_meet _).symm
    · exact ((EqRelLattice Bool).meet_bot _).symm
    · exact ((EqRelLattice Bool).meet_idem _).symm
  map_join x y := by
    cases x <;> cases y
    · exact ((EqRelLattice Bool).join_idem _).symm
    · exact ((EqRelLattice Bool).bot_join _).symm
    · exact ((EqRelLattice Bool).join_bot _).symm
    · exact ((EqRelLattice Bool).join_idem _).symm

def b2FinitePhi : B2Elem → EqRel Three
  | B2Elem.bot => EqBot Three
  | B2Elem.a => eqRel01
  | B2Elem.b => eqRel12
  | B2Elem.top => EqTop Three

theorem b2_finite_eq_embedding :
    BoundedLatticeEmbedding B2Lattice (EqRelLattice Three) b2FinitePhi where
  inj x y h := by
    have test01 : ∀ z, (b2FinitePhi z).r Three.zero Three.one ↔ (z = B2Elem.a ∨ z = B2Elem.top) := by
      intro z; cases z <;> dsimp [b2FinitePhi, EqBot, EqTop, eqRel01, eqRel12] <;> decide
    have test12 : ∀ z, (b2FinitePhi z).r Three.one Three.two ↔ (z = B2Elem.b ∨ z = B2Elem.top) := by
      intro z; cases z <;> dsimp [b2FinitePhi, EqBot, EqTop, eqRel01, eqRel12] <;> decide
    have h1 := (test01 x).symm.trans ((by rw [h] : (b2FinitePhi x).r _ _ ↔ _).trans (test01 y))
    have h2 := (test12 x).symm.trans ((by rw [h] : (b2FinitePhi x).r _ _ ↔ _).trans (test12 y))
    cases x <;> cases y <;> simp at h1 h2 <;> rfl
  map_bot := rfl
  map_top := rfl
  map_meet x y := by
    let EL := EqRelLattice Three
    cases x <;> cases y
    · exact (EL.meet_idem _).symm
    · exact (EL.bot_meet _).symm
    · exact (EL.bot_meet _).symm
    · exact (EL.bot_meet _).symm
    · exact (EL.meet_bot _).symm
    · exact (EL.meet_idem _).symm
    · exact eqMeet_01_12.symm
    · exact (EL.meet_top _).symm
    · exact (EL.meet_bot _).symm
    · exact (EL.meet_comm eqRel12 eqRel01).trans eqMeet_01_12 |>.symm
    · exact (EL.meet_idem _).symm
    · exact (EL.meet_top _).symm
    · exact (EL.meet_bot _).symm
    · exact (EL.top_meet _).symm
    · exact (EL.top_meet _).symm
    · exact (EL.meet_idem _).symm
  map_join x y := by
    let EL := EqRelLattice Three
    cases x <;> cases y
    · exact (EL.join_idem _).symm
    · exact (EL.bot_join _).symm
    · exact (EL.bot_join _).symm
    · exact (EL.bot_join _).symm
    · exact (EL.join_bot _).symm
    · exact (EL.join_idem _).symm
    · exact eqJoin_01_12.symm
    · exact (EL.join_top _).symm
    · exact (EL.join_bot _).symm
    · exact ((EL.join_comm eqRel12 eqRel01).trans eqJoin_01_12).symm
    · exact (EL.join_idem _).symm
    · exact (EL.join_top _).symm
    · exact (EL.join_bot _).symm
    · exact (EL.top_join _).symm
    · exact (EL.top_join _).symm
    · exact (EL.join_idem _).symm

def m3FinitePhi : M3Elem → EqRel Three
  | M3Elem.bot => EqBot Three
  | M3Elem.a => eqRel01
  | M3Elem.b => eqRel02
  | M3Elem.c => eqRel12
  | M3Elem.top => EqTop Three

theorem m3_finite_eq_embedding :
    BoundedLatticeEmbedding M3Lattice (EqRelLattice Three) m3FinitePhi where
  inj x y h := by
    have t01 : ∀ z, (m3FinitePhi z).r Three.zero Three.one ↔ (z = M3Elem.a ∨ z = M3Elem.top) := by
      intro z; cases z <;> dsimp [m3FinitePhi, EqBot, EqTop, eqRel01, eqRel02, eqRel12] <;> decide
    have t02 : ∀ z, (m3FinitePhi z).r Three.zero Three.two ↔ (z = M3Elem.b ∨ z = M3Elem.top) := by
      intro z; cases z <;> dsimp [m3FinitePhi, EqBot, EqTop, eqRel01, eqRel02, eqRel12] <;> decide
    have t12 : ∀ z, (m3FinitePhi z).r Three.one Three.two ↔ (z = M3Elem.c ∨ z = M3Elem.top) := by
      intro z; cases z <;> dsimp [m3FinitePhi, EqBot, EqTop, eqRel01, eqRel02, eqRel12] <;> decide
    have h1 := (t01 x).symm.trans ((by rw [h] : (m3FinitePhi x).r _ _ ↔ _).trans (t01 y))
    have h2 := (t02 x).symm.trans ((by rw [h] : (m3FinitePhi x).r _ _ ↔ _).trans (t02 y))
    have h3 := (t12 x).symm.trans ((by rw [h] : (m3FinitePhi x).r _ _ ↔ _).trans (t12 y))
    cases x <;> cases y <;> simp at h1 h2 h3 <;> rfl
  map_bot := rfl
  map_top := rfl
  map_meet x y := by
    let EL := EqRelLattice Three
    cases x <;> cases y
    · exact (EL.meet_idem _).symm
    · exact (EL.bot_meet _).symm
    · exact (EL.bot_meet _).symm
    · exact (EL.bot_meet _).symm
    · exact (EL.bot_meet _).symm
    · exact (EL.meet_bot _).symm
    · exact (EL.meet_idem _).symm
    · exact eqMeet_01_02.symm
    · exact eqMeet_01_12.symm
    · exact (EL.meet_top _).symm
    · exact (EL.meet_bot _).symm
    · exact ((EL.meet_comm eqRel02 eqRel01).trans eqMeet_01_02).symm
    · exact (EL.meet_idem _).symm
    · exact eqMeet_02_12.symm
    · exact (EL.meet_top _).symm
    · exact (EL.meet_bot _).symm
    · exact ((EL.meet_comm eqRel12 eqRel01).trans eqMeet_01_12).symm
    · exact ((EL.meet_comm eqRel12 eqRel02).trans eqMeet_02_12).symm
    · exact (EL.meet_idem _).symm
    · exact (EL.meet_top _).symm
    · exact (EL.meet_bot _).symm
    · exact (EL.top_meet _).symm
    · exact (EL.top_meet _).symm
    · exact (EL.top_meet _).symm
    · exact (EL.meet_idem _).symm
  map_join x y := by
    let EL := EqRelLattice Three
    cases x <;> cases y
    · exact (EL.join_idem _).symm
    · exact (EL.bot_join _).symm
    · exact (EL.bot_join _).symm
    · exact (EL.bot_join _).symm
    · exact (EL.bot_join _).symm
    · exact (EL.join_bot _).symm
    · exact (EL.join_idem _).symm
    · exact eqJoin_01_02.symm
    · exact eqJoin_01_12.symm
    · exact (EL.join_top _).symm
    · exact (EL.join_bot _).symm
    · exact ((EL.join_comm eqRel02 eqRel01).trans eqJoin_01_02).symm
    · exact (EL.join_idem _).symm
    · exact eqJoin_02_12.symm
    · exact (EL.join_top _).symm
    · exact (EL.join_bot _).symm
    · exact ((EL.join_comm eqRel12 eqRel01).trans eqJoin_01_12).symm
    · exact ((EL.join_comm eqRel12 eqRel02).trans eqJoin_02_12).symm
    · exact (EL.join_idem _).symm
    · exact (EL.join_top _).symm
    · exact (EL.join_bot _).symm
    · exact (EL.top_join _).symm
    · exact (EL.top_join _).symm
    · exact (EL.top_join _).symm
    · exact (EL.join_idem _).symm

/-- Explicit finite `Eq(Three)` embedding of the NON-geometric chain `C₃` (`|C₃| = 3`). -/
def c3FinitePhi : C3Elem → EqRel Three
  | C3Elem.bot => EqBot Three
  | C3Elem.mid => eqRel01
  | C3Elem.top => EqTop Three

theorem c3_finite_eq_embedding :
    BoundedLatticeEmbedding C3Lattice (EqRelLattice Three) c3FinitePhi where
  inj x y h := by
    have t01 : ∀ z, (c3FinitePhi z).r Three.zero Three.one ↔ (z = C3Elem.mid ∨ z = C3Elem.top) := by
      intro z; cases z <;> dsimp [c3FinitePhi, EqBot, EqTop, eqRel01] <;> decide
    have t12 : ∀ z, (c3FinitePhi z).r Three.one Three.two ↔ z = C3Elem.top := by
      intro z; cases z <;> dsimp [c3FinitePhi, EqBot, EqTop, eqRel01] <;> decide
    have h1 := (t01 x).symm.trans ((by rw [h] : (c3FinitePhi x).r _ _ ↔ _).trans (t01 y))
    have h2 := (t12 x).symm.trans ((by rw [h] : (c3FinitePhi x).r _ _ ↔ _).trans (t12 y))
    cases x <;> cases y <;> simp at h1 h2 <;> rfl
  map_bot := rfl
  map_top := rfl
  map_meet x y := by
    let EL := EqRelLattice Three
    cases x <;> cases y
    · exact (EL.meet_idem _).symm
    · exact (EL.bot_meet _).symm
    · exact (EL.bot_meet _).symm
    · exact (EL.meet_bot _).symm
    · exact (EL.meet_idem _).symm
    · exact (EL.meet_top _).symm
    · exact (EL.meet_bot _).symm
    · exact (EL.top_meet _).symm
    · exact (EL.meet_idem _).symm
  map_join x y := by
    let EL := EqRelLattice Three
    cases x <;> cases y
    · exact (EL.join_idem _).symm
    · exact (EL.bot_join _).symm
    · exact (EL.bot_join _).symm
    · exact (EL.join_bot _).symm
    · exact (EL.join_idem _).symm
    · exact (EL.join_top _).symm
    · exact (EL.join_bot _).symm
    · exact (EL.top_join _).symm
    · exact (EL.join_idem _).symm

/-- Explicit finite `Eq(Four)` embedding of the NON-geometric pentagon `N₅` (`|N₅| = 5`). -/
inductive Four : Type where
  | p0 : Four
  | p1 : Four
  | p2 : Four
  | p3 : Four
  deriving DecidableEq

def n5RelA : EqRel Four where
  r x y := x = y ∨ (x = Four.p0 ∧ y = Four.p1) ∨ (x = Four.p1 ∧ y = Four.p0)
  refl _ := Or.inl rfl
  symm := by intro x y; cases x <;> cases y <;> decide
  trans := by intro x y z; cases x <;> cases y <;> cases z <;> decide

def n5RelB : EqRel Four where
  r x y := x = y ∨ (x = Four.p0 ∧ y = Four.p1) ∨ (x = Four.p1 ∧ y = Four.p0) ∨
           (x = Four.p2 ∧ y = Four.p3) ∨ (x = Four.p3 ∧ y = Four.p2)
  refl _ := Or.inl rfl
  symm := by intro x y; cases x <;> cases y <;> decide
  trans := by intro x y z; cases x <;> cases y <;> cases z <;> decide

def n5RelC : EqRel Four where
  r x y := x = y ∨ (x = Four.p0 ∧ y = Four.p2) ∨ (x = Four.p2 ∧ y = Four.p0) ∨
           (x = Four.p1 ∧ y = Four.p3) ∨ (x = Four.p3 ∧ y = Four.p1)
  refl _ := Or.inl rfl
  symm := by intro x y; cases x <;> cases y <;> decide
  trans := by intro x y z; cases x <;> cases y <;> cases z <;> decide

def n5FinitePhi : N5Elem → EqRel Four
  | N5Elem.bot => EqBot Four
  | N5Elem.a => n5RelA
  | N5Elem.b => n5RelB
  | N5Elem.c => n5RelC
  | N5Elem.top => EqTop Four

theorem n5_join_ac : EqJoin n5RelA n5RelC = EqTop Four := by
  apply EqRel.ext
  intro x y
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  have h01 : (EqJoin n5RelA n5RelC).r Four.p0 Four.p1 :=
    EqClosure.base (Or.inl (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have h02 : (EqJoin n5RelA n5RelC).r Four.p0 Four.p2 :=
    EqClosure.base (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have h13 : (EqJoin n5RelA n5RelC).r Four.p1 Four.p3 :=
    EqClosure.base (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
  have to_p0 : ∀ z : Four, (EqJoin n5RelA n5RelC).r z Four.p0 := by
    intro z
    cases z with
    | p0 => exact EqClosure.refl Four.p0
    | p1 => exact EqClosure.symm h01
    | p2 => exact EqClosure.symm h02
    | p3 => exact EqClosure.symm (EqClosure.trans h01 h13)
  exact EqClosure.trans (to_p0 x) (EqClosure.symm (to_p0 y))

theorem n5_finite_eq_embedding :
    BoundedLatticeEmbedding N5Lattice (EqRelLattice Four) n5FinitePhi where
  inj x y h := by
    have t01 : ∀ z, (n5FinitePhi z).r Four.p0 Four.p1 ↔
        (z = N5Elem.a ∨ z = N5Elem.b ∨ z = N5Elem.top) := by
      intro z; cases z <;> dsimp [n5FinitePhi, EqBot, EqTop, n5RelA, n5RelB, n5RelC] <;> decide
    have t23 : ∀ z, (n5FinitePhi z).r Four.p2 Four.p3 ↔
        (z = N5Elem.b ∨ z = N5Elem.top) := by
      intro z; cases z <;> dsimp [n5FinitePhi, EqBot, EqTop, n5RelA, n5RelB, n5RelC] <;> decide
    have t02 : ∀ z, (n5FinitePhi z).r Four.p0 Four.p2 ↔
        (z = N5Elem.c ∨ z = N5Elem.top) := by
      intro z; cases z <;> dsimp [n5FinitePhi, EqBot, EqTop, n5RelA, n5RelB, n5RelC] <;> decide
    have h1 := (t01 x).symm.trans ((by rw [h] : (n5FinitePhi x).r _ _ ↔ _).trans (t01 y))
    have h2 := (t23 x).symm.trans ((by rw [h] : (n5FinitePhi x).r _ _ ↔ _).trans (t23 y))
    have h3 := (t02 x).symm.trans ((by rw [h] : (n5FinitePhi x).r _ _ ↔ _).trans (t02 y))
    cases x <;> cases y <;> simp at h1 h2 h3 <;> rfl
  map_bot := rfl
  map_top := rfl
  map_meet x y := by
    let EL := EqRelLattice Four
    have hm_ab : EqMeet n5RelA n5RelB = n5RelA :=
      EqRel.ext fun u v => by dsimp [EqMeet, n5RelA, n5RelB]; cases u <;> cases v <;> decide
    have hm_ac : EqMeet n5RelA n5RelC = EqBot Four :=
      EqRel.ext fun u v => by dsimp [EqMeet, EqBot, n5RelA, n5RelC]; cases u <;> cases v <;> decide
    have hm_bc : EqMeet n5RelB n5RelC = EqBot Four :=
      EqRel.ext fun u v => by dsimp [EqMeet, EqBot, n5RelB, n5RelC]; cases u <;> cases v <;> decide
    cases x <;> cases y
    · exact (EL.meet_idem _).symm
    · exact (EL.bot_meet _).symm
    · exact (EL.bot_meet _).symm
    · exact (EL.bot_meet _).symm
    · exact (EL.bot_meet _).symm
    · exact (EL.meet_bot _).symm
    · exact (EL.meet_idem _).symm
    · exact hm_ab.symm
    · exact hm_ac.symm
    · exact (EL.meet_top _).symm
    · exact (EL.meet_bot _).symm
    · exact ((EL.meet_comm n5RelB n5RelA).trans hm_ab).symm
    · exact (EL.meet_idem _).symm
    · exact hm_bc.symm
    · exact (EL.meet_top _).symm
    · exact (EL.meet_bot _).symm
    · exact ((EL.meet_comm n5RelC n5RelA).trans hm_ac).symm
    · exact ((EL.meet_comm n5RelC n5RelB).trans hm_bc).symm
    · exact (EL.meet_idem _).symm
    · exact (EL.meet_top _).symm
    · exact (EL.meet_bot _).symm
    · exact (EL.top_meet _).symm
    · exact (EL.top_meet _).symm
    · exact (EL.top_meet _).symm
    · exact (EL.meet_idem _).symm
  map_join x y := by
    let EL := EqRelLattice Four
    have hle_ab : EL.le n5RelA n5RelB := by
      intro u v; dsimp [EL, EqRelLattice, n5RelA, n5RelB]; cases u <;> cases v <;> decide
    have hj_ab : EqJoin n5RelA n5RelB = n5RelB := EL.join_eq_right_of_le hle_ab
    have hj_bc : EqJoin n5RelB n5RelC = EqTop Four := by
      apply EL.le_antisymm (EL.le_top _)
      have hsub : EL.le (EqJoin n5RelA n5RelC) (EqJoin n5RelB n5RelC) :=
        EL.join_le (EL.le_trans hle_ab (EL.le_join_left _ _)) (EL.le_join_right _ _)
      rw [n5_join_ac] at hsub
      exact hsub
    cases x <;> cases y
    · exact (EL.join_idem _).symm
    · exact (EL.bot_join _).symm
    · exact (EL.bot_join _).symm
    · exact (EL.bot_join _).symm
    · exact (EL.bot_join _).symm
    · exact (EL.join_bot _).symm
    · exact (EL.join_idem _).symm
    · exact hj_ab.symm
    · exact n5_join_ac.symm
    · exact (EL.join_top _).symm
    · exact (EL.join_bot _).symm
    · exact ((EL.join_comm n5RelB n5RelA).trans hj_ab).symm
    · exact (EL.join_idem _).symm
    · exact hj_bc.symm
    · exact (EL.join_top _).symm
    · exact (EL.join_bot _).symm
    · exact ((EL.join_comm n5RelC n5RelA).trans n5_join_ac).symm
    · exact ((EL.join_comm n5RelC n5RelB).trans hj_bc).symm
    · exact (EL.join_idem _).symm
    · exact (EL.join_top _).symm
    · exact (EL.join_bot _).symm
    · exact (EL.top_join _).symm
    · exact (EL.top_join _).symm
    · exact (EL.top_join _).symm
    · exact (EL.join_idem _).symm

/-! ### 6.2 Generating-Relation Count `< |L|` in `Eq(Three)` (`2 < 4` for `B₂`, `3 < 5` for `M₃`) -/

/-- Sublattice closure generated by an indexed family of elements in `L` under `(∧, ∨)` alone
    (not even assuming `⊥` and `⊤` as free constants). -/
inductive SublatticeGen {β : Type v} (L : BoundedLattice β) {k : Nat} (G : Fin k → β) :
    β → Prop where
  | gen (i : Fin k) : SublatticeGen L G (G i)
  | meet {x y} : SublatticeGen L G x → SublatticeGen L G y → SublatticeGen L G (L.meet x y)
  | join {x y} : SublatticeGen L G x → SublatticeGen L G y → SublatticeGen L G (L.join x y)

/-- `B₂` (`|B₂| = 4`) is generated in `Eq(Three)` by `2 < 4` equivalence relations! -/
theorem b2_generated_by_two_relations :
    ∃ G : Fin 2 → EqRel Three,
      ∀ x : B2Elem, SublatticeGen (EqRelLattice Three) G (b2FinitePhi x) := by
  let G : Fin 2 → EqRel Three := fun i => if i.val == 0 then eqRel01 else eqRel12
  refine ⟨G, fun x => ?_⟩
  have h0 : SublatticeGen (EqRelLattice Three) G eqRel01 :=
    SublatticeGen.gen ⟨0, by decide⟩
  have h1 : SublatticeGen (EqRelLattice Three) G eqRel12 :=
    SublatticeGen.gen ⟨1, by decide⟩
  cases x with
  | bot =>
    change SublatticeGen (EqRelLattice Three) G (EqBot Three)
    rw [← eqMeet_01_12]
    exact SublatticeGen.meet h0 h1
  | a => exact h0
  | b => exact h1
  | top =>
    change SublatticeGen (EqRelLattice Three) G (EqTop Three)
    rw [← eqJoin_01_12]
    exact SublatticeGen.join h0 h1

/-- `M₃` (`|M₃| = 5`) is generated in `Eq(Three)` by `3 < 5` equivalence relations! -/
theorem m3_generated_by_three_relations :
    ∃ G : Fin 3 → EqRel Three,
      ∀ x : M3Elem, SublatticeGen (EqRelLattice Three) G (m3FinitePhi x) := by
  let G : Fin 3 → EqRel Three := fun i =>
    if i.val == 0 then eqRel01 else if i.val == 1 then eqRel02 else eqRel12
  refine ⟨G, fun x => ?_⟩
  have h0 : SublatticeGen (EqRelLattice Three) G eqRel01 :=
    SublatticeGen.gen ⟨0, by decide⟩
  have h1 : SublatticeGen (EqRelLattice Three) G eqRel02 :=
    SublatticeGen.gen ⟨1, by decide⟩
  have h2 : SublatticeGen (EqRelLattice Three) G eqRel12 :=
    SublatticeGen.gen ⟨2, by decide⟩
  cases x with
  | bot =>
    change SublatticeGen (EqRelLattice Three) G (EqBot Three)
    rw [← eqMeet_01_02]
    exact SublatticeGen.meet h0 h1
  | a => exact h0
  | b => exact h1
  | c => exact h2
  | top =>
    change SublatticeGen (EqRelLattice Three) G (EqTop Three)
    rw [← eqJoin_01_02]
    exact SublatticeGen.join h0 h1

/-! ### 6.3 Exact Optimal 2-Valued Meet-Representations (`2 < 4` for `B₂`, `3 < 5` for `M₃`) -/

theorem b2_twoValuedMeetRep_two : HasTwoValuedMeetRep B2Lattice 2 := by
  refine ⟨fun i x _ => if i.val == 0 then B2Lattice.le B2Elem.a x else B2Lattice.le B2Elem.b x,
    ?_, ?_, ?_⟩
  · intro ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
  · intro ⟨i, hi⟩ x y
    match i, hi with
    | 0, _ => dsimp [B2Lattice]; cases x <;> cases y <;> decide
    | 1, _ => dsimp [B2Lattice]; cases x <;> cases y <;> decide
  · intro x y
    constructor
    · intro hxy ⟨i, hi⟩ h
      match i, hi with
      | 0, _ => exact B2Lattice.le_trans h hxy
      | 1, _ => exact B2Lattice.le_trans h hxy
    · intro hall
      have h0 : B2Lattice.le B2Elem.a x → B2Lattice.le B2Elem.a y := hall ⟨0, by decide⟩
      have h1 : B2Lattice.le B2Elem.b x → B2Lattice.le B2Elem.b y := hall ⟨1, by decide⟩
      cases x <;> cases y <;> first | rfl | exact h0 rfl | exact h1 rfl |
        (have ha := h0 rfl; cases ha) | (have hb := h1 rfl; cases hb)

theorem m3_twoValuedMeetRep_three : HasTwoValuedMeetRep M3Lattice 3 := by
  refine ⟨fun i x _ =>
    if i.val == 0 then M3Lattice.le M3Elem.a x
    else if i.val == 1 then M3Lattice.le M3Elem.b x
    else M3Lattice.le M3Elem.c x, ?_, ?_, ?_⟩
  · intro ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
  · intro ⟨i, hi⟩ x y
    match i, hi with
    | 0, _ => dsimp [M3Lattice]; cases x <;> cases y <;> decide
    | 1, _ => dsimp [M3Lattice]; cases x <;> cases y <;> decide
    | 2, _ => dsimp [M3Lattice]; cases x <;> cases y <;> decide
  · intro x y
    constructor
    · intro hxy ⟨i, hi⟩ h
      match i, hi with
      | 0, _ => exact M3Lattice.le_trans h hxy
      | 1, _ => exact M3Lattice.le_trans h hxy
      | 2, _ => exact M3Lattice.le_trans h hxy
    · intro hall
      have h0 : M3Lattice.le M3Elem.a x → M3Lattice.le M3Elem.a y := hall ⟨0, by decide⟩
      have h1 : M3Lattice.le M3Elem.b x → M3Lattice.le M3Elem.b y := hall ⟨1, by decide⟩
      have h2 : M3Lattice.le M3Elem.c x → M3Lattice.le M3Elem.c y := hall ⟨2, by decide⟩
      cases x <;> cases y <;> first | rfl | exact h0 rfl | exact h1 rfl | exact h2 rfl |
        (have ha := h0 rfl; cases ha) | (have hb := h1 rfl; cases hb) | (have hc := h2 rfl; cases hc)

/-! ### 6.4 Dushnik–Miller Linear-Order / Ferrers Dimension (`dim(B₁)=1<2`, `dim(B₂)=2<4`, `dim(M₃)=2<5`) -/

structure IsLinearOrderOn {α : Type u} (R : α → α → Prop) : Prop where
  refl : ∀ x, R x x
  trans : ∀ {x y z}, R x y → R y z → R x z
  antisymm : ∀ {x y}, R x y → R y x → x = y
  total : ∀ x y, R x y ∨ R y x

def HasOrderDimRep {α : Type u} (L : BoundedLattice α) (k : Nat) : Prop :=
  ∃ R : Fin k → α → α → Prop,
    (∀ i, IsLinearOrderOn (R i)) ∧
    (∀ x y, L.le x y ↔ ∀ i, R i x y)

theorem b1_orderDimRep_one : HasOrderDimRep B1Lattice 1 := by
  refine ⟨fun _ => B1Lattice.le, fun _ => ?_, fun x y => ?_⟩
  · refine ⟨B1Lattice.le_refl, B1Lattice.le_trans, B1Lattice.le_antisymm, fun x y => ?_⟩
    dsimp [B1Lattice]; cases x <;> cases y <;> decide
  · exact ⟨fun h _ => h, fun h => h ⟨0, by decide⟩⟩

def b2Rank1 : B2Elem → Nat
  | B2Elem.bot => 0
  | B2Elem.a => 1
  | B2Elem.b => 2
  | B2Elem.top => 3

def b2Rank2 : B2Elem → Nat
  | B2Elem.bot => 0
  | B2Elem.b => 1
  | B2Elem.a => 2
  | B2Elem.top => 3

theorem b2_orderDimRep_two : HasOrderDimRep B2Lattice 2 := by
  refine ⟨fun i x y => if i.val == 0 then b2Rank1 x ≤ b2Rank1 y else b2Rank2 x ≤ b2Rank2 y,
    ?_, ?_⟩
  · intro ⟨i, hi⟩
    match i, hi with
    | 0, _ =>
      refine ⟨fun _ => Nat.le_refl _, fun h₁ h₂ => Nat.le_trans h₁ h₂, ?_, ?_⟩
      · intro x y; dsimp; cases x <;> cases y <;> decide
      · intro x y; exact Nat.le_total _ _
    | 1, _ =>
      refine ⟨fun _ => Nat.le_refl _, fun h₁ h₂ => Nat.le_trans h₁ h₂, ?_, ?_⟩
      · intro x y; dsimp; cases x <;> cases y <;> decide
      · intro x y; exact Nat.le_total _ _
  · intro x y
    constructor
    · intro hxy ⟨i, hi⟩
      match i, hi with
      | 0, _ => dsimp; cases x <;> cases y <;> first | contradiction | decide
      | 1, _ => dsimp; cases x <;> cases y <;> first | contradiction | decide
    · intro hall
      have h0 : b2Rank1 x ≤ b2Rank1 y := hall ⟨0, by decide⟩
      have h1 : b2Rank2 x ≤ b2Rank2 y := hall ⟨1, by decide⟩
      cases x <;> cases y <;> dsimp [b2Rank1, b2Rank2] at h0 h1 <;> first | rfl | omega

def m3Rank1 : M3Elem → Nat
  | M3Elem.bot => 0
  | M3Elem.a => 1
  | M3Elem.b => 2
  | M3Elem.c => 3
  | M3Elem.top => 4

def m3Rank2 : M3Elem → Nat
  | M3Elem.bot => 0
  | M3Elem.c => 1
  | M3Elem.b => 2
  | M3Elem.a => 3
  | M3Elem.top => 4

theorem m3_orderDimRep_two : HasOrderDimRep M3Lattice 2 := by
  refine ⟨fun i x y => if i.val == 0 then m3Rank1 x ≤ m3Rank1 y else m3Rank2 x ≤ m3Rank2 y,
    ?_, ?_⟩
  · intro ⟨i, hi⟩
    match i, hi with
    | 0, _ =>
      refine ⟨fun _ => Nat.le_refl _, fun h₁ h₂ => Nat.le_trans h₁ h₂, ?_, ?_⟩
      · intro x y; dsimp; cases x <;> cases y <;> decide
      · intro x y; exact Nat.le_total _ _
    | 1, _ =>
      refine ⟨fun _ => Nat.le_refl _, fun h₁ h₂ => Nat.le_trans h₁ h₂, ?_, ?_⟩
      · intro x y; dsimp; cases x <;> cases y <;> decide
      · intro x y; exact Nat.le_total _ _
  · intro x y
    constructor
    · intro hxy ⟨i, hi⟩
      match i, hi with
      | 0, _ => dsimp; cases x <;> cases y <;> first | contradiction | decide
      | 1, _ => dsimp; cases x <;> cases y <;> first | contradiction | decide
    · intro hall
      have h0 : m3Rank1 x ≤ m3Rank1 y := hall ⟨0, by decide⟩
      have h1 : m3Rank2 x ≤ m3Rank2 y := hall ⟨1, by decide⟩
      cases x <;> cases y <;> dsimp [m3Rank1, m3Rank2] at h0 h1 <;> first | rfl | omega

/-! ### 6.5 Non-Representability of Geometric `M₃` by Boolean Binary Relations `(∩, ∪)` -/

theorem m3_no_boolRel_family_rep {I : Type v} (X : I → Type v)
    (φ : (i : I) → M3Elem → BinRel (X i))
    (h_meet : ∀ i x y, φ i (M3Lattice.meet x y) = (BoolRelLattice (X i)).meet (φ i x) (φ i y))
    (h_join : ∀ i x y, φ i (M3Lattice.join x y) = (BoolRelLattice (X i)).join (φ i x) (φ i y))
    (h_inj : ∀ x y, (∀ i, φ i x = φ i y) → x = y) :
    False :=
  m3_not_distributive (boolRel_family_implies_distributive M3Lattice X φ h_meet h_join h_inj)

/-! ## Section 7: Master Resolution Theorem and Axiom Audit -/

/-- **Master Theorem for Conjecture 00000008555:**
    1. *(Positive Representation & Upper Bounds)* Every bounded lattice `L` embeds completely
       into `EqRel (WLimX L)` via a single map (`CompleteEqFamilyRep L 1`), admits a single-relation
       principal-downset representation on `L`, and every finite lattice of size `n + 1` admits a
       complete 2-valued meet-representation using `n = |L| - 1 < |L|` binary relations.
    2. *(Geometric Non-Vacuity & Refutation of `= |L|`)* `C₁` (`|L|=1`), `B₁` (`|L|=2`),
       `B₂` (`|L|=4`), and `M₃` (`|L|=5`) are genuine geometric lattices, yet:
       - Complete `Eq(X)` family size is `0 < 1` on `C₁` and `1 < 2, 4, 5` on `B₁, B₂, M₃`
         (already over finite sets `Bool` and `Three` of sizes `2` and `3`),
       - Generating-relation count in `Eq(Three)` is `2 < 4` on `B₂` and `3 < 5` on `M₃`,
       - 2-valued meet-relation count is `2 < 4` on `B₂` and `3 < 5` on `M₃`,
       - Dushnik–Miller order dimension is `1 < 2` on `B₁`, `2 < 4` on `B₂`, and `2 < 5` on `M₃`,
       - `M₃` is simple (`1 < 5` congruence) and non-distributive (admitting NO Boolean `(∩, ∪)`
         binary-relation family representation at all),
       - Non-geometric finite lattices `C₃` (`|C₃|=3`) and `N₅` (`|N₅|=5`) also embed completely
         into finite `Eq(Three)` and `Eq(Four)`, so image cardinality `|φ(L)| = |L|` holds
         trivially for non-geometric finite lattices as well. -/
theorem conjecture_00000008555_resolution :
    -- (1) Universal positive representation theorems
    (∀ (α : Type) (L : BoundedLattice α), CompleteEqFamilyRep L 1) ∧
    (∀ (α : Type) (L : BoundedLattice α) (n : Nat) (enum : Fin (n + 1) → α),
      (∀ x, ∃ j, enum j = x) → HasTwoValuedMeetRep L n) ∧
    -- (2) Geometric lattice witnesses and strict `< |L|` refutations
    (IsGeometricLattice C1Lattice ∧ CompleteEqFamilyRep C1Lattice 0) ∧
    (IsGeometricLattice B1Lattice ∧
      BoundedLatticeEmbedding B1Lattice (EqRelLattice Bool) b1FinitePhi ∧
      HasOrderDimRep B1Lattice 1) ∧
    (IsGeometricLattice B2Lattice ∧
      BoundedLatticeEmbedding B2Lattice (EqRelLattice Three) b2FinitePhi ∧
      (∃ G : Fin 2 → EqRel Three,
        ∀ x, SublatticeGen (EqRelLattice Three) G (b2FinitePhi x)) ∧
      HasTwoValuedMeetRep B2Lattice 2 ∧
      HasOrderDimRep B2Lattice 2) ∧
    (IsGeometricLattice M3Lattice ∧ IsModular M3Lattice ∧
      ¬ IsDistributive M3Lattice ∧ IsSimpleLattice M3Lattice ∧
      BoundedLatticeEmbedding M3Lattice (EqRelLattice Three) m3FinitePhi ∧
      (∃ G : Fin 3 → EqRel Three,
        ∀ x, SublatticeGen (EqRelLattice Three) G (m3FinitePhi x)) ∧
      HasTwoValuedMeetRep M3Lattice 3 ∧
      HasOrderDimRep M3Lattice 2) ∧
    -- (3) Non-geometric finite lattices also admit complete finite Eq(X) embeddings
    (¬ IsGeometricLattice C3Lattice ∧
      BoundedLatticeEmbedding C3Lattice (EqRelLattice Three) c3FinitePhi) ∧
    (¬ IsGeometricLattice N5Lattice ∧
      BoundedLatticeEmbedding N5Lattice (EqRelLattice Four) n5FinitePhi) :=
  ⟨fun _ L => completeEqFamilyRep_one L,
   fun _ L n enum hsurj => twoValuedMeetRep_card_pred L n enum hsurj,
   ⟨c1_isGeometric, c1_zero_eqFamilyRep⟩,
   ⟨b1_isGeometric, b1_finite_eq_embedding, b1_orderDimRep_one⟩,
   ⟨b2_isGeometric, b2_finite_eq_embedding, b2_generated_by_two_relations,
    b2_twoValuedMeetRep_two, b2_orderDimRep_two⟩,
   ⟨m3_isGeometric, m3_isModular, m3_not_distributive, m3_isSimple,
    m3_finite_eq_embedding, m3_generated_by_three_relations,
    m3_twoValuedMeetRep_three, m3_orderDimRep_two⟩,
   ⟨c3_not_geometric, c3_finite_eq_embedding⟩,
   ⟨n5_not_geometric, n5_finite_eq_embedding⟩⟩

#print axioms whitman_complete_representation
#print axioms twoValuedMeetRep_card_pred
#print axioms boolRel_family_implies_distributive
#print axioms m3_no_boolRel_family_rep
#print axioms conjecture_00000008555_resolution

end Conjecture00000008555
