/-
  Disproof of conjecture `00000008848`: formalisation of clause (a).

  Conjecture (as filed):

    Definition: fixed points of order-preserving maps.
    Conjecture: minimal and maximal fixed points of order-preserving maps
    always exist; and monotone iterations of the sub/supersolution method
    approximate them in countably many steps.

  The file specifies no poset (no "complete lattice", no boundedness) and
  states no sub/supersolution hypothesis for the first clause, so its
  quantifier ranges over all order-preserving self-maps of ordered sets.

  This file formalises, in CORE LEAN ONLY (`import Std`, no Mathlib, no
  `sorry`), the refutation of clause (a):

  * `refutes_least_fixed_point` — the shift map `f x = x + 1` on `ℤ` is
    order-preserving and has NO fixed point at all, so the universal claim
    "every order-preserving self-map of an ordered set has a least fixed
    point" is false.  The same witness refutes the greatest-fixed-point
    version.

  * `refutes_least_fixed_point_with_fixpoint` — even granting the existence
    of at least one fixed point, the universal claim is false: the identity
    map on `ℤ` is order-preserving, every point is fixed, yet the fixed-point
    set `ℤ` has neither a least nor a greatest element.  This is the
    NON-VACUOUS witness and the primary one for clause (a).

  Clause (b) — that the sub/supersolution iteration reaches the extremal
  fixed point in countably many steps — is NOT formalised here: core Lean has
  no ordinals or cardinals, so the witness `ω₁ + 1` is argued in the LaTeX
  prose (`main.tex`) and in `reproduce.py`.  See `README.md` in this directory
  and the submission `README.md` for the honest reading caveat.
-/

import Std

set_option maxRecDepth 1000000

namespace Tlmc8848

/-! ## The primary, non-vacuous witness: the identity map on `ℤ` -/

/-- `IsFixed g y` means that `y` is a fixed point of `g`. -/
def IsFixed {α : Type} (g : α → α) (y : α) : Prop := g y = y

/-- The fixed-point set of the identity map on `ℤ` is all of `ℤ`. -/
theorem id_isFixed (y : Int) : IsFixed (α := Int) id y := rfl

/-- If a *least* fixed point of the identity on `ℤ` existed, it would force a
contradiction: any `m` is fixed, so `m - 1` is also fixed, and `m ≤ m - 1` is
impossible. -/
theorem id_no_least_fixed :
    ¬ ∃ m : Int, IsFixed (α := Int) id m ∧ ∀ y : Int, IsFixed (α := Int) id y → m ≤ y := by
  rintro ⟨m, _, hmin⟩
  have h : m ≤ m - 1 := hmin (m - 1) rfl
  omega

/-- Likewise there is no *greatest* fixed point of the identity on `ℤ`. -/
theorem id_no_greatest_fixed :
    ¬ ∃ M : Int, IsFixed (α := Int) id M ∧ ∀ y : Int, IsFixed (α := Int) id y → y ≤ M := by
  rintro ⟨M, _, hmax⟩
  have h : M + 1 ≤ M := hmax (M + 1) rfl
  omega

/-- The identity map on `ℤ` is order-preserving. -/
theorem id_mono : ∀ a b : Int, a ≤ b → id a ≤ id b := by
  intro a b h
  exact h

/-- Clause (a), least-fixed-point half, refuted **non-vacuously**: even if one
assumes that the order-preserving map has at least one fixed point, a least
fixed point need not exist.  Witness: `id` on `ℤ`. -/
theorem refutes_least_fixed_point_with_fixpoint :
    ¬ (∀ (α : Type) [LE α] (g : α → α),
        (∀ a b : α, a ≤ b → g a ≤ g b) →
        (∃ x : α, g x = x) →
        ∃ m : α, g m = m ∧ ∀ y : α, g y = y → m ≤ y) := by
  intro H
  obtain ⟨m, _, hmin⟩ := H Int id id_mono ⟨0, rfl⟩
  have h : m ≤ m - 1 := hmin (m - 1) rfl
  omega

/-- Clause (a), greatest-fixed-point half, refuted **non-vacuously**, by the
same identity-map witness. -/
theorem refutes_greatest_fixed_point_with_fixpoint :
    ¬ (∀ (α : Type) [LE α] (g : α → α),
        (∀ a b : α, a ≤ b → g a ≤ g b) →
        (∃ x : α, g x = x) →
        ∃ M : α, g M = M ∧ ∀ y : α, g y = y → y ≤ M) := by
  intro H
  obtain ⟨M, _, hmax⟩ := H Int id id_mono ⟨0, rfl⟩
  have h : M + 1 ≤ M := hmax (M + 1) rfl
  omega

/-! ## The literal reading: the shift map `f x = x + 1` on `ℤ` -/

/-- The successor map `f(x) = x + 1` on `ℤ`. -/
def f : Int → Int := fun x => x + 1

/-- `f` is order-preserving for the usual order on `ℤ`. -/
theorem f_mono : ∀ a b : Int, a ≤ b → f a ≤ f b := by
  intro a b h
  dsimp [f]
  exact Int.add_le_add_right h 1

/-- `f` has no fixed point: `f x = x` would force `x + 1 = x`. -/
theorem f_fixfree : ∀ x : Int, f x ≠ x := by
  intro x h
  dsimp [f] at h
  omega

/-- There is no fixed point of `f` at all. -/
theorem no_fixed_at_all : ¬ ∃ x : Int, f x = x := by
  rintro ⟨x, hx⟩
  exact f_fixfree x hx

/-- There is no least fixed point of `f` (there is none at all). -/
theorem f_no_least_fixed :
    ¬ ∃ m : Int, IsFixed f m ∧ ∀ y : Int, IsFixed f y → m ≤ y := by
  rintro ⟨m, hm, _⟩
  exact f_fixfree m hm

/-- There is no greatest fixed point of `f` either. -/
theorem f_no_greatest_fixed :
    ¬ ∃ M : Int, IsFixed f M ∧ ∀ y : Int, IsFixed f y → y ≤ M := by
  rintro ⟨M, hM, _⟩
  exact f_fixfree M hM

/-- Clause (a), least-fixed-point half, refuted under the literal reading
(no existence of fixed points assumed): "a least fixed point always exists"
is false already for order-preserving self-maps of a totally ordered type.
Witness: the shift map on `ℤ`. -/
theorem refutes_least_fixed_point :
    ¬ (∀ (α : Type) [LE α] (g : α → α),
        (∀ a b : α, a ≤ b → g a ≤ g b) →
        ∃ m : α, g m = m ∧ ∀ y : α, g y = y → m ≤ y) := by
  intro H
  obtain ⟨m, hm, _⟩ := H Int f f_mono
  exact f_fixfree m hm

/-- Clause (a), greatest-fixed-point half, refuted under the literal reading,
by the same shift-map witness. -/
theorem refutes_greatest_fixed_point :
    ¬ (∀ (α : Type) [LE α] (g : α → α),
        (∀ a b : α, a ≤ b → g a ≤ g b) →
        ∃ M : α, g M = M ∧ ∀ y : α, g y = y → y ≤ M) := by
  intro H
  obtain ⟨M, hM, _⟩ := H Int f f_mono
  exact f_fixfree M hM

/-! ## Packaged refutations of clause (a) -/

/-- Clause (a) is false on both halves under the literal reading. -/
theorem clause_a_false :
    (¬ (∀ (α : Type) [LE α] (g : α → α),
          (∀ a b : α, a ≤ b → g a ≤ g b) →
          ∃ m : α, g m = m ∧ ∀ y : α, g y = y → m ≤ y)) ∧
    (¬ (∀ (α : Type) [LE α] (g : α → α),
          (∀ a b : α, a ≤ b → g a ≤ g b) →
          ∃ M : α, g M = M ∧ ∀ y : α, g y = y → y ≤ M)) :=
  ⟨refutes_least_fixed_point, refutes_greatest_fixed_point⟩

/-- Clause (a) is false on both halves **even when a fixed point is assumed to
exist** (the non-vacuous reading); witness: `id` on `ℤ`. -/
theorem clause_a_false_with_fixpoint :
    (¬ (∀ (α : Type) [LE α] (g : α → α),
          (∀ a b : α, a ≤ b → g a ≤ g b) →
          (∃ x : α, g x = x) →
          ∃ m : α, g m = m ∧ ∀ y : α, g y = y → m ≤ y)) ∧
    (¬ (∀ (α : Type) [LE α] (g : α → α),
          (∀ a b : α, a ≤ b → g a ≤ g b) →
          (∃ x : α, g x = x) →
          ∃ M : α, g M = M ∧ ∀ y : α, g y = y → y ≤ M)) :=
  ⟨refutes_least_fixed_point_with_fixpoint,
    refutes_greatest_fixed_point_with_fixpoint⟩

/-- Explicit fixed-point-set formulation for the primary witness: the set of
fixed points of `id` on `ℤ` is `univ`, and it has no least element. -/
theorem id_fixset_unbounded_below (m : Int) : ∃ y : Int, id y = y ∧ y < m :=
  ⟨m - 1, rfl, by omega⟩

/-- And no greatest element. -/
theorem id_fixset_unbounded_above (M : Int) : ∃ y : Int, id y = y ∧ M < y :=
  ⟨M + 1, rfl, by omega⟩

end Tlmc8848
