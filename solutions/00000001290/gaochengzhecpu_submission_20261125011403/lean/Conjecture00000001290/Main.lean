/-
  Conjecture 00000001290 — Master Resolution Theorems
  "The generating function of Sprague–Grundy values is rational
   if and only if the game is short and local (a rationality criterion)."

  Core Lean 4.19.0 (zero external dependencies)
-/
import Conjecture00000001290.Counterexamples

namespace Conjecture00000001290

/-! ### Candidate Formal Statements of Conjecture 00000001290 Across All Conventions -/

/-- Interpretation 1A: Value OGF + bounded-step locality (among all impartial games). -/
def Conjecture_BoundedStep_OGF : Prop :=
  ∀ G : ImpartialGame, HasRationalGrundyOGF G ↔ (G.IsShort ∧ G.IsBoundedStepLocal)

/-- Interpretation 1B: Value OGF + bounded-step locality (restricted to short games). -/
def Conjecture_ShortRestricted_BoundedStep_OGF : Prop :=
  ∀ G : ImpartialGame, G.IsShort → (HasRationalGrundyOGF G ↔ G.IsBoundedStepLocal)

/-- Interpretation 2A: Value OGF + bounded-outdegree locality. -/
def Conjecture_BoundedOutDegree_OGF : Prop :=
  ∀ G : ImpartialGame, HasRationalGrundyOGF G ↔ (G.IsShort ∧ G.IsBoundedOutDegree)

/-- Interpretation 2B: Value OGF + bounded-outdegree locality (restricted to short games). -/
def Conjecture_ShortRestricted_BoundedOutDegree_OGF : Prop :=
  ∀ G : ImpartialGame, G.IsShort → (HasRationalGrundyOGF G ↔ G.IsBoundedOutDegree)

/-- Interpretation 3A: Value OGF + translation-invariant finite subtraction locality. -/
def Conjecture_FiniteSubtraction_OGF : Prop :=
  ∀ G : ImpartialGame, HasRationalGrundyOGF G ↔ (G.IsShort ∧ G.IsFiniteSubtractionGame)

/-- Interpretation 3B: Value OGF + finite subtraction locality (restricted to short games). -/
def Conjecture_ShortRestricted_FiniteSubtraction_OGF : Prop :=
  ∀ G : ImpartialGame, G.IsShort → (HasRationalGrundyOGF G ↔ G.IsFiniteSubtractionGame)

/-- Interpretation 4: Rationality directly over `ℚ[x]` (`IsRationalOGF_Q`) + bounded-step locality. -/
def Conjecture_BoundedStep_OGF_Q : Prop :=
  ∀ G : ImpartialGame,
    (∃ g : Nat → Nat, G.IsGrundySeq g ∧ IsRationalOGF_Q (grundyIntSeq g)) ↔
    (G.IsShort ∧ G.IsBoundedStepLocal)

/-- Interpretation 5A: Grundy-fiber indicator GFs + bounded-step locality. -/
def Conjecture_BoundedStep_Fibers : Prop :=
  ∀ G : ImpartialGame, HasAllRationalGrundyFibers G ↔ (G.IsShort ∧ G.IsBoundedStepLocal)

/-- Interpretation 5B: Grundy-fiber indicator GFs + bounded-outdegree locality. -/
def Conjecture_BoundedOutDegree_Fibers : Prop :=
  ∀ G : ImpartialGame, HasAllRationalGrundyFibers G ↔ (G.IsShort ∧ G.IsBoundedOutDegree)

/-- Interpretation 5C: Grundy-fiber indicator GFs + finite subtraction locality. -/
def Conjecture_FiniteSubtraction_Fibers : Prop :=
  ∀ G : ImpartialGame, HasAllRationalGrundyFibers G ↔ (G.IsShort ∧ G.IsFiniteSubtractionGame)

/-- Interpretation 6A: `P`-position indicator GF (`v = 0`) + bounded-step locality. -/
def Conjecture_BoundedStep_PPositions : Prop :=
  ∀ G : ImpartialGame, HasRationalPPositionOGF G ↔ (G.IsShort ∧ G.IsBoundedStepLocal)

/-- Interpretation 6B: `P`-position indicator GF (`v = 0`) + finite subtraction locality. -/
def Conjecture_FiniteSubtraction_PPositions : Prop :=
  ∀ G : ImpartialGame, HasRationalPPositionOGF G ↔ (G.IsShort ∧ G.IsFiniteSubtractionGame)

/-! ### Complete Disproof of Every Interpretation of Conjecture 00000001290 -/

theorem disproof_Conjecture_ShortRestricted_BoundedStep_OGF :
    ¬ Conjecture_ShortRestricted_BoundedStep_OGF := by
  intro h
  exact nimGame_not_boundedStepLocal ((h nimGame nimGame_isShort).mp nimGame_rational_ogf)

theorem disproof_Conjecture_BoundedStep_OGF :
    ¬ Conjecture_BoundedStep_OGF := by
  intro h
  exact nimGame_not_boundedStepLocal ((h nimGame).mp nimGame_rational_ogf).2

theorem disproof_Conjecture_ShortRestricted_BoundedOutDegree_OGF :
    ¬ Conjecture_ShortRestricted_BoundedOutDegree_OGF := by
  intro h
  exact nimGame_not_boundedOutDegree ((h nimGame nimGame_isShort).mp nimGame_rational_ogf)

theorem disproof_Conjecture_BoundedOutDegree_OGF :
    ¬ Conjecture_BoundedOutDegree_OGF := by
  intro h
  exact nimGame_not_boundedOutDegree ((h nimGame).mp nimGame_rational_ogf).2

theorem disproof_Conjecture_ShortRestricted_FiniteSubtraction_OGF :
    ¬ Conjecture_ShortRestricted_FiniteSubtraction_OGF := by
  intro h
  exact oddSubGame_not_finiteSubtraction
    ((h oddSubGame oddSubGame_isShort).mp oddSubGame_rational_ogf)

theorem disproof_Conjecture_FiniteSubtraction_OGF :
    ¬ Conjecture_FiniteSubtraction_OGF := by
  intro h
  exact oddSubGame_not_finiteSubtraction ((h oddSubGame).mp oddSubGame_rational_ogf).2

theorem disproof_Conjecture_BoundedStep_OGF_Q :
    ¬ Conjecture_BoundedStep_OGF_Q := by
  intro h
  rcases nimGame_rational_ogf with ⟨g, hg, hrat⟩
  have hratQ : IsRationalOGF_Q (grundyIntSeq g) := (isRationalOGF_iff_Q _).mpr hrat
  exact nimGame_not_boundedStepLocal ((h nimGame).mp ⟨g, hg, hratQ⟩).2

theorem disproof_Conjecture_BoundedStep_Fibers :
    ¬ Conjecture_BoundedStep_Fibers := by
  intro h
  exact nimGame_not_boundedStepLocal ((h nimGame).mp nimGame_rational_fibers).2

theorem disproof_Conjecture_BoundedOutDegree_Fibers :
    ¬ Conjecture_BoundedOutDegree_Fibers := by
  intro h
  exact nimGame_not_boundedOutDegree ((h nimGame).mp nimGame_rational_fibers).2

theorem disproof_Conjecture_FiniteSubtraction_Fibers :
    ¬ Conjecture_FiniteSubtraction_Fibers := by
  intro h
  exact oddSubGame_not_finiteSubtraction ((h oddSubGame).mp oddSubGame_rational_fibers).2

theorem disproof_Conjecture_BoundedStep_PPositions :
    ¬ Conjecture_BoundedStep_PPositions := by
  intro h
  rcases nimGame_rational_fibers with ⟨g, hg, hfib⟩
  exact nimGame_not_boundedStepLocal ((h nimGame).mp ⟨g, hg, hfib 0⟩).2

theorem disproof_Conjecture_FiniteSubtraction_PPositions :
    ¬ Conjecture_FiniteSubtraction_PPositions := by
  intro h
  rcases oddSubGame_rational_fibers with ⟨g, hg, hfib⟩
  exact oddSubGame_not_finiteSubtraction ((h oddSubGame).mp ⟨g, hg, hfib 0⟩).2

/-! ### Sharp Directional Breakdown: Necessity Fails Everywhere; Sufficiency Splits Cleanly -/

/-- Necessity (`Rational GF → Local`) fails even for short games with bounded periodic Grundy values. -/
theorem necessity_local_fails_bounded_periodic :
    ∃ G : ImpartialGame,
      G.IsShort ∧ HasRationalGrundyOGF G ∧ HasAllRationalGrundyFibers G ∧
      ¬ G.IsBoundedStepLocal ∧ ¬ G.IsBoundedOutDegree ∧ ¬ G.IsFiniteSubtractionGame :=
  ⟨oddSubGame,
   oddSubGame_isShort,
   oddSubGame_rational_ogf,
   oddSubGame_rational_fibers,
   oddSubGame_not_boundedStepLocal,
   oddSubGame_not_boundedOutDegree,
   oddSubGame_not_finiteSubtraction⟩

/-- Necessity (`Rational GF → Short`) fails even for step-1 local, bounded-degree games. -/
theorem necessity_short_fails_even_when_local :
    ∃ G : ImpartialGame,
      G.IsBoundedStepLocal ∧ G.IsBoundedOutDegree ∧
      HasRationalGrundyOGF G ∧ HasAllRationalGrundyFibers G ∧ ¬ G.IsShort :=
  ⟨loopyStep1Game,
   loopyStep1Game_boundedStepLocal,
   loopyStep1Game_boundedOutDegree,
   loopyStep1Game_rational_ogf,
   loopyStep1Game_rational_fibers,
   loopyStep1Game_not_isShort⟩

/-- Sufficiency (`Short ∧ Local → Rational GF`) ALSO fails under bounded-step and bounded-degree
    locality without translation invariance (for value OGF, fiber GFs, and `P`-position GF). -/
theorem sufficiency_fails_for_boundedStep_and_boundedOutDegree :
    ∃ G : ImpartialGame,
      G.IsShort ∧ G.IsBoundedStepLocal ∧ G.IsBoundedOutDegree ∧
      ¬ HasRationalGrundyOGF G ∧ ¬ HasAllRationalGrundyFibers G ∧
      ¬ HasRationalPPositionOGF G :=
  ⟨lacunaryLocalGame,
   lacunaryLocalGame_isShort,
   lacunaryLocalGame_boundedStepLocal,
   lacunaryLocalGame_boundedOutDegree,
   lacunaryLocalGame_not_rational_ogf,
   lacunaryLocalGame_not_rational_fibers,
   lacunaryLocalGame_not_rational_pPositions⟩

/-- Positive Theorem (Non-Vacuity & Exact Scope of Sufficiency):
    For 1D translation-invariant finite subtraction games, sufficiency DOES hold. -/
theorem sufficiency_holds_for_finiteSubtraction :
    ∀ G : ImpartialGame, G.IsFiniteSubtractionGame →
      G.IsShort ∧ G.IsBoundedStepLocal ∧ G.IsBoundedOutDegree ∧
      HasRationalGrundyOGF G ∧ HasAllRationalGrundyFibers G :=
  fun _ hfin =>
    ⟨finiteSubtraction_isShort hfin,
     finiteSubtraction_boundedStepLocal hfin,
     finiteSubtraction_boundedOutDegree hfin,
     (finiteSubtraction_rational_ogf hfin).1,
     (finiteSubtraction_rational_ogf hfin).2⟩

/-- Master Resolution Theorem for Conjecture 00000001290. -/
theorem conjecture_00000001290_false :
    ¬ Conjecture_BoundedStep_OGF ∧
    ¬ Conjecture_BoundedOutDegree_OGF ∧
    ¬ Conjecture_FiniteSubtraction_OGF ∧
    ¬ Conjecture_BoundedStep_OGF_Q ∧
    ¬ Conjecture_BoundedStep_Fibers ∧
    ¬ Conjecture_BoundedOutDegree_Fibers ∧
    ¬ Conjecture_FiniteSubtraction_Fibers ∧
    ¬ Conjecture_BoundedStep_PPositions ∧
    ¬ Conjecture_FiniteSubtraction_PPositions :=
  ⟨disproof_Conjecture_BoundedStep_OGF,
   disproof_Conjecture_BoundedOutDegree_OGF,
   disproof_Conjecture_FiniteSubtraction_OGF,
   disproof_Conjecture_BoundedStep_OGF_Q,
   disproof_Conjecture_BoundedStep_Fibers,
   disproof_Conjecture_BoundedOutDegree_Fibers,
   disproof_Conjecture_FiniteSubtraction_Fibers,
   disproof_Conjecture_BoundedStep_PPositions,
   disproof_Conjecture_FiniteSubtraction_PPositions⟩

end Conjecture00000001290
