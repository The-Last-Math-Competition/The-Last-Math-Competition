/-
  Formalisation of the *logical* falsity of conjecture 00000007121 as written.

  The catalogue entry asserts, in one sentence:

    "The Hirsch conjecture's diameter upper bound of face count minus dimension
     holds, and the counterexample to the bound is the high-dimensional double
     configuration."

  Read literally this conjoins
    (a) the bound HOLDS, with
    (b) a COUNTEREXAMPLE to the bound EXISTS,
  which cannot both be true.

  This file formalises only that logical inconsistency. It does NOT formalise,
  and does not claim to reproduce, the mathematical counterexample of Santos
  (Annals of Mathematics 176 (2012), 383-412): a 43-dimensional polytope with
  86 facets and diameter 44 > 86 - 43 = 43. That is a literature result quoted
  in main.tex and is deliberately not asserted here.

  Core Lean only (`import Std`); no Mathlib, no `sorry`, no `axiom`,
  no `native_decide`.
-/
import Std

namespace Hirsch7121

/-- The Hirsch bound as an abstract proposition over `Nat`:

    "for every polytope, diameter ≤ (number of facets) − (dimension)".

    `d` = dimension, `f` = number of facets, `diam` = graph diameter.
    (This is the pure arithmetic skeleton; no polytope structure is
    formalised.) -/
def HirschBoundHolds : Prop := ∀ d f diam : Nat, diam ≤ f - d

/-- A counterexample to the bound exists: some `d`, `f`, `diam` with
    `f - d < diam`, i.e. `diam > f - d`. -/
def CounterexampleExists : Prop := ∃ d f diam : Nat, f - d < diam

/-- Pure propositional logic: no proposition is both true and false. -/
theorem conjunction_is_contradictory (P : Prop) : ¬ (P ∧ ¬P) :=
  fun h => h.2 h.1

/-- Instantiating the pure-logic fact at the Hirsch bound. -/
theorem hirsch_and_negation_contradictory :
    ¬ (HirschBoundHolds ∧ ¬ HirschBoundHolds) :=
  conjunction_is_contradictory HirschBoundHolds

/-- A counterexample entails the negation of the bound. -/
theorem counterexample_refutes_bound (h : CounterexampleExists) :
    ¬ HirschBoundHolds := by
  intro hb
  obtain ⟨d, f, diam, hlt⟩ := h
  exact absurd (hb d f diam) (Nat.not_le.mpr hlt)

/-- The statement **as written** is false: the bound cannot hold while a
    counterexample exists. Kernel-checkable contradiction over `Nat`. -/
theorem hirsch_as_written_false :
    ¬ (HirschBoundHolds ∧ CounterexampleExists) := by
  intro h
  exact counterexample_refutes_bound h.2 h.1

/-- Final collected result for conjecture 00000007121:

    (i)  the two conjuncts of the statement as written cannot both hold, and
    (ii) any exhibited counterexample entails that the bound fails. -/
theorem conjecture_00000007121_false :
    ¬ (HirschBoundHolds ∧ CounterexampleExists) ∧
      (CounterexampleExists → ¬ HirschBoundHolds) :=
  ⟨hirsch_as_written_false, counterexample_refutes_bound⟩

end Hirsch7121
