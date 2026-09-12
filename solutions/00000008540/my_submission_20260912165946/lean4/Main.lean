/-
  Disproof of conjecture 00000008540.

      "The congruence lattice of a finite lattice is Boolean exactly when the
       lattice is of subdirectly irreducible type; the number of congruences is
       at most 2^(n-1), and the bound is optimal."

  The smallest counterexample is the three-element chain C3.

  Formalised here:

  * `con_complete`  -- C3 has exactly the four congruences listed below.
  * `code_inj`, `code_surj`, `code_le` -- Con(C3) is order-isomorphic to
    `Bool × Bool`, the four-element Boolean lattice 2^2.
  * `relAlpha_isAtom`, `relBeta_isAtom`, `atom_only_two` -- Con(C3) has exactly
    two atoms, so C3 is not subdirectly irreducible.

  Core Lean 4 only -- no Mathlib dependency.  Congruences are represented as
  `Bool`-valued relations so that every condition is a decidable proposition and
  `decide` can discharge the concrete instances.
-/

namespace Tlmc8540

/-! ## The three-element chain C3 -/

/-- Meet (infimum) in the chain `0 < 1 < 2`, on `Fin 3`. -/
abbrev meet (x y : Fin 3) : Fin 3 := if x.val ≤ y.val then x else y

/-- Join (supremum) in the chain `0 < 1 < 2`, on `Fin 3`. -/
abbrev join (x y : Fin 3) : Fin 3 := if x.val ≤ y.val then y else x

theorem meet_0_1 : meet (0 : Fin 3) 1 = 0 := by decide

theorem meet_2_1 : meet (2 : Fin 3) 1 = 1 := by decide

theorem join_0_1 : join (0 : Fin 3) 1 = 1 := by decide

theorem join_2_1 : join (2 : Fin 3) 1 = 2 := by decide

/-! ## Congruences of C3

A congruence is an equivalence relation compatible with `meet` and `join`.  We
write it as a `Bool`-valued relation `f`, so that `f x y = true` is the assertion
`x ~ y` and every clause below is a decidable proposition. -/

/-- A lattice congruence on the chain `0 < 1 < 2`, as a `Bool`-valued relation. -/
abbrev IsCongruence (f : Fin 3 → Fin 3 → Bool) : Prop :=
  (∀ x, f x x = true) ∧
  (∀ x y, f x y = f y x) ∧
  (∀ x y z, f x y = true → f y z = true → f x z = true) ∧
  (∀ x y z, f x y = true →
    f (meet x z) (meet y z) = true ∧ f (join x z) (join y z) = true)

/-- The diagonal congruence. -/
abbrev relBot (x y : Fin 3) : Bool := decide (x = y)

/-- The congruence identifying `0` and `1`. -/
abbrev relAlpha (x y : Fin 3) : Bool :=
  decide (x = y) || (decide (x = 0) && decide (y = 1)) || (decide (x = 1) && decide (y = 0))

/-- The congruence identifying `1` and `2`. -/
abbrev relBeta (x y : Fin 3) : Bool :=
  decide (x = y) || (decide (x = 1) && decide (y = 2)) || (decide (x = 2) && decide (y = 1))

/-- The total congruence. -/
abbrev relTop (_ _ : Fin 3) : Bool := true

theorem relBot_isCongruence : IsCongruence relBot := by decide

theorem relAlpha_isCongruence : IsCongruence relAlpha := by decide

theorem relBeta_isCongruence : IsCongruence relBeta := by decide

theorem relTop_isCongruence : IsCongruence relTop := by decide

/-! ## The structure of congruences on a chain -/

/-- In a congruence on a chain, `0 ~ 2` holds exactly when both `0 ~ 1` and
`1 ~ 2` hold.  This is the chain case of "every congruence class is an interval":
if `0 ~ 2` then `0 ~ 1`, because `meet 0 1 = 0` and `meet 2 1 = 1`, and
`1 ~ 2`, because `join 0 1 = 1` and `join 2 1 = 2`. -/
theorem f02_eq (f : Fin 3 → Fin 3 → Bool) (h : IsCongruence f) :
    f 0 2 = (f 0 1 && f 1 2) := by
  cases c1 : f 0 1
  · cases c2 : f 1 2
    · have e : f 0 2 = false := by
        cases c : f 0 2
        · rfl
        · have hc := (h.2.2.2 0 2 1 c).1
          rw [meet_0_1, meet_2_1] at hc
          rw [c1] at hc
          exact absurd hc (by decide)
      exact e.trans rfl
    · have e : f 0 2 = false := by
        cases c : f 0 2
        · rfl
        · have hc := (h.2.2.2 0 2 1 c).1
          rw [meet_0_1, meet_2_1] at hc
          rw [c1] at hc
          exact absurd hc (by decide)
      exact e.trans rfl
  · cases c2 : f 1 2
    · have e : f 0 2 = false := by
        cases c : f 0 2
        · rfl
        · have hc := (h.2.2.2 0 2 1 c).2
          rw [join_0_1, join_2_1] at hc
          rw [c2] at hc
          exact absurd hc (by decide)
      exact e.trans rfl
    · have e : f 0 2 = true := h.2.2.1 0 1 2 c1 c2
      exact e.trans rfl

/-- A congruence on the chain is determined by whether it identifies `0` with `1`
and `1` with `2`. -/
theorem determined (f g : Fin 3 → Fin 3 → Bool)
    (hf : IsCongruence f) (hg : IsCongruence g)
    (h1 : f 0 1 = g 0 1) (h2 : f 1 2 = g 1 2) : f = g := by
  have e02 : f 0 2 = g 0 2 := by rw [f02_eq f hf, f02_eq g hg, h1, h2]
  funext x y
  match x, y with
  | 0, 0 => rw [hf.1 0, hg.1 0]
  | 0, 1 => exact h1
  | 0, 2 => exact e02
  | 1, 0 => rw [← hf.2.1 0 1, ← hg.2.1 0 1]; exact h1
  | 1, 1 => rw [hf.1 1, hg.1 1]
  | 1, 2 => exact h2
  | 2, 0 => rw [← hf.2.1 0 2, ← hg.2.1 0 2]; exact e02
  | 2, 1 => rw [← hf.2.1 1 2, ← hg.2.1 1 2]; exact h2
  | 2, 2 => rw [hf.1 2, hg.1 2]

/-- **C3 has exactly four congruences.**  Every congruence is one of
`relBot`, `relAlpha`, `relBeta`, `relTop`. -/
theorem con_complete (f : Fin 3 → Fin 3 → Bool) (h : IsCongruence f) :
    f = relBot ∨ f = relAlpha ∨ f = relBeta ∨ f = relTop := by
  cases c1 : f 0 1
  · cases c2 : f 1 2
    · exact Or.inl (determined f relBot h relBot_isCongruence
        (c1.trans (by decide)) (c2.trans (by decide)))
    · exact Or.inr (Or.inr (Or.inl (determined f relBeta h relBeta_isCongruence
        (c1.trans (by decide)) (c2.trans (by decide)))))
  · cases c2 : f 1 2
    · exact Or.inr (Or.inl (determined f relAlpha h relAlpha_isCongruence
        (c1.trans (by decide)) (c2.trans (by decide))))
    · exact Or.inr (Or.inr (Or.inr (determined f relTop h relTop_isCongruence
        (c1.trans (by decide)) (c2.trans (by decide)))))

/-! ## The four congruences are distinct

`DecidableEq (Fin 3 → Fin 3 → Bool)` is not available, so distinctness is shown
by exhibiting a pair on which the two relations disagree. -/

theorem relBot_ne_relAlpha : relBot ≠ relAlpha := by
  intro h
  exact absurd (congrArg (fun k : Fin 3 → Fin 3 → Bool => k (0 : Fin 3) 1) h) (by decide)

theorem relBot_ne_relBeta : relBot ≠ relBeta := by
  intro h
  exact absurd (congrArg (fun k : Fin 3 → Fin 3 → Bool => k (1 : Fin 3) 2) h) (by decide)

theorem relBot_ne_relTop : relBot ≠ relTop := by
  intro h
  exact absurd (congrArg (fun k : Fin 3 → Fin 3 → Bool => k (0 : Fin 3) 1) h) (by decide)

theorem relAlpha_ne_relBeta : relAlpha ≠ relBeta := by
  intro h
  exact absurd (congrArg (fun k : Fin 3 → Fin 3 → Bool => k (0 : Fin 3) 1) h) (by decide)

theorem relAlpha_ne_relTop : relAlpha ≠ relTop := by
  intro h
  exact absurd (congrArg (fun k : Fin 3 → Fin 3 → Bool => k (1 : Fin 3) 2) h) (by decide)

theorem relBeta_ne_relTop : relBeta ≠ relTop := by
  intro h
  exact absurd (congrArg (fun k : Fin 3 → Fin 3 → Bool => k (0 : Fin 3) 1) h) (by decide)

theorem relAlpha_ne_relBot : relAlpha ≠ relBot := fun h => relBot_ne_relAlpha h.symm

theorem relBeta_ne_relBot : relBeta ≠ relBot := fun h => relBot_ne_relBeta h.symm

/-! ## The order on congruences -/

/-- `f ≤ g` when every pair identified by `f` is also identified by `g`. -/
abbrev le (f g : Fin 3 → Fin 3 → Bool) : Prop := ∀ x y, f x y = true → g x y = true

/-- The code of a congruence: the pair `(0 ~ 1 ?, 1 ~ 2 ?)`.  By `determined`
this loses no information on congruences. -/
abbrev code (f : Fin 3 → Fin 3 → Bool) : Bool × Bool := (f 0 1, f 1 2)

/-- The componentwise order on `Bool × Bool` (`false < true`), i.e. the order of
the four-element Boolean lattice `2^2`. -/
abbrev codeLe (a b : Bool × Bool) : Prop := (a.1 = true → b.1 = true) ∧ (a.2 = true → b.2 = true)

theorem le_refl (f : Fin 3 → Fin 3 → Bool) : le f f := fun _ _ h => h

theorem le_bot (f : Fin 3 → Fin 3 → Bool) (h : IsCongruence f) : le relBot f := by
  rcases con_complete f h with hb | ha | hbe | ht
  · rw [hb]; decide
  · rw [ha]; decide
  · rw [hbe]; decide
  · rw [ht]; decide

theorem le_top (f : Fin 3 → Fin 3 → Bool) (_h : IsCongruence f) : le f relTop :=
  fun _ _ _ => rfl

theorem code_relBot : code relBot = (false, false) := by decide

theorem code_relAlpha : code relAlpha = (true, false) := by decide

theorem code_relBeta : code relBeta = (false, true) := by decide

theorem code_relTop : code relTop = (true, true) := by decide

/-! ## Con(C3) is the Boolean lattice 2^2 -/

/-- The code determines the congruence. -/
theorem code_inj {f g : Fin 3 → Fin 3 → Bool} (hf : IsCongruence f) (hg : IsCongruence g)
    (h : code f = code g) : f = g :=
  determined f g hf hg (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- Every pair arises as the code of a congruence. -/
theorem code_surj (c : Bool × Bool) :
    ∃ f : Fin 3 → Fin 3 → Bool, IsCongruence f ∧ code f = c := by
  rcases c with ⟨c1, c2⟩
  cases c1 <;> cases c2
  · exact ⟨relBot, relBot_isCongruence, by decide⟩
  · exact ⟨relBeta, relBeta_isCongruence, by decide⟩
  · exact ⟨relAlpha, relAlpha_isCongruence, by decide⟩
  · exact ⟨relTop, relTop_isCongruence, by decide⟩

/-- The code is an order isomorphism. -/
theorem code_le {f g : Fin 3 → Fin 3 → Bool} (hf : IsCongruence f) (hg : IsCongruence g) :
    le f g ↔ codeLe (code f) (code g) := by
  rcases con_complete f hf with hf' | hf' | hf' | hf' <;>
  rcases con_complete g hg with hg' | hg' | hg' | hg' <;>
  rw [hf', hg'] <;>
  decide

/-! ## C3 is not subdirectly irreducible

For a finite lattice, subdirect irreducibility is equivalent to the congruence
lattice having exactly one atom.  `Con(C3)` has two. -/

/-- `f` is an atom of `Con(C3)`: a congruence covering the bottom. -/
abbrev IsAtom (f : Fin 3 → Fin 3 → Bool) : Prop :=
  IsCongruence f ∧ f ≠ relBot ∧ ∀ g, IsCongruence g → le g f → g = relBot ∨ g = f

theorem relAlpha_isAtom : IsAtom relAlpha := by
  refine ⟨relAlpha_isCongruence, relAlpha_ne_relBot, ?_⟩
  intro g hg hle
  rcases con_complete g hg with hb | ha | hbe | ht
  · exact Or.inl hb
  · exact Or.inr ha
  · rw [hbe] at hle; exact absurd hle (by decide)
  · rw [ht] at hle; exact absurd hle (by decide)

theorem relBeta_isAtom : IsAtom relBeta := by
  refine ⟨relBeta_isCongruence, relBeta_ne_relBot, ?_⟩
  intro g hg hle
  rcases con_complete g hg with hb | ha | hbe | ht
  · exact Or.inl hb
  · rw [ha] at hle; exact absurd hle (by decide)
  · exact Or.inr hbe
  · rw [ht] at hle; exact absurd hle (by decide)

/-- These are the only two atoms: `relTop` is above both, so it is not one. -/
theorem atom_only_two (f : Fin 3 → Fin 3 → Bool) (h : IsAtom f) :
    f = relAlpha ∨ f = relBeta := by
  rcases con_complete f h.1 with hb | ha | hbe | ht
  · exact absurd hb h.2.1
  · exact Or.inl ha
  · exact Or.inr hbe
  · exfalso
    rw [ht] at h
    rcases h.2.2 relAlpha relAlpha_isCongruence (by decide) with h1 | h1
    · exact relAlpha_ne_relBot h1
    · exact relAlpha_ne_relTop h1

/-- **Conjecture 00000008540 is false.**

`Con(C3)` is the four-element Boolean lattice `2^2` -- the code map is a
bijection onto `Bool × Bool` that preserves and reflects the order -- while `C3`
is not subdirectly irreducible, because `Con(C3)` has exactly two atoms
(`relAlpha` and `relBeta`) rather than one.  The counting clause `2^(n-1)` is not
touched: `|Con(C3)| = 4 = 2^2`. -/
theorem conjecture_00000008540_false :
    (∀ f, IsCongruence f → ∀ g, IsCongruence g → (le f g ↔ codeLe (code f) (code g))) ∧
    (∀ c : Bool × Bool, ∃ f : Fin 3 → Fin 3 → Bool, IsCongruence f ∧ code f = c) ∧
    (∀ f, IsCongruence f → ∀ g, IsCongruence g → code f = code g → f = g) ∧
    IsAtom relAlpha ∧ IsAtom relBeta ∧
    (∀ f, IsAtom f → f = relAlpha ∨ f = relBeta) ∧
    relAlpha ≠ relBeta :=
  ⟨fun _ hf _ hg => code_le hf hg,
   code_surj,
   fun _ hf _ hg h => code_inj hf hg h,
   relAlpha_isAtom,
   relBeta_isAtom,
   atom_only_two,
   relAlpha_ne_relBeta⟩

end Tlmc8540
