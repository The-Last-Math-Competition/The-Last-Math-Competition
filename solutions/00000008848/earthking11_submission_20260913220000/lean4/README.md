# Lean 4 formalisation — disproof of conjecture `00000008848`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main`
in `lakefile.toml` (project name `tlmc8848`).

This directory formalises **clause (a)** of the conjecture, fully. Clause (b)
is *not* formalised here, because core Lean has no ordinals or cardinals; it is
argued in the LaTeX prose (`../main.tex`) and in `../reproduce.py`. See the
scope note at the end.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of Mathlib dependencies.

## The statement being refuted

The conjecture as filed is:

> **Definition:** Fixed points of order-preserving maps.
> **Conjecture:** Minimal and maximal fixed points of order-preserving maps
> always exist; and monotone iterations of the sub/supersolution method
> approximate them in countably many steps.

The file specifies **no poset** — no "complete lattice", no boundedness — and
states **no sub/supersolution hypothesis** for the first clause. Its first
clause therefore quantifies over *all order-preserving self-maps of ordered
sets*:

```lean
¬ (∀ (α : Type) [LE α] (g : α → α),
      (∀ a b : α, a ≤ b → g a ≤ g b) →
      ∃ m : α, g m = m ∧ ∀ y : α, g y = y → m ≤ y)   -- "least fixed point always exists"
```

and analogously for the greatest fixed point. Both halves are refuted in
`Main.lean`.

## What is formalised

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `IsFixed` | `def IsFixed (g : α → α) (y : α) : Prop := g y = y` | fixed-point predicate |
| `id_isFixed` | `IsFixed id y` for every `y : Int` | every point of `ℤ` is fixed by `id` |
| `id_mono` | `∀ a b, a ≤ b → id a ≤ id b` | `id` is order-preserving |
| `id_no_least_fixed` | `¬ ∃ m : Int, IsFixed id m ∧ ∀ y, IsFixed id y → m ≤ y` | `id` on `ℤ` has **no least** fixed point |
| `id_no_greatest_fixed` | `¬ ∃ M : Int, IsFixed id M ∧ ∀ y, IsFixed id y → y ≤ M` | `id` on `ℤ` has **no greatest** fixed point |
| `id_fixset_unbounded_below` | `∀ m, ∃ y, id y = y ∧ y < m` | fixed-point set is unbounded below |
| `id_fixset_unbounded_above` | `∀ M, ∃ y, id y = y ∧ M < y` | fixed-point set is unbounded above |
| `refutes_least_fixed_point_with_fixpoint` | the universal least-fixed-point claim, **assuming a fixed point exists**, is false | primary, non-vacuous refutation of clause (a) |
| `refutes_greatest_fixed_point_with_fixpoint` | same for the greatest fixed point | primary, non-vacuous refutation |
| `f` | `def f : Int → Int := fun x => x + 1` | the shift map |
| `f_mono` | `∀ a b, a ≤ b → f a ≤ f b` | `f` is order-preserving |
| `f_fixfree` | `∀ x : Int, f x ≠ x` | `f` has no fixed point |
| `no_fixed_at_all` | `¬ ∃ x : Int, f x = x` | fixed-point set of `f` is empty |
| `f_no_least_fixed` / `f_no_greatest_fixed` | no extremal fixed point of `f` | literal reading |
| `refutes_least_fixed_point` / `refutes_greatest_fixed_point` | universal claim false under the literal (no-existence-assumed) reading | shift-map witness |
| `clause_a_false` | conjunction of both literal refutations | clause (a) false, both halves |
| `clause_a_false_with_fixpoint` | conjunction of both non-vacuous refutations | clause (a) false even assuming a fixed point |

## Proof strategy

- **Non-vacuous witness (`id` on `ℤ`).** `IsFixed id y` is definitionally
  `y = y`, so `id_isFixed` is `rfl`. Given a claimed least fixed point `m`,
  `m - 1` is also fixed, so minimality gives `m ≤ m - 1`, which `omega`
  refutes. Symmetrically `m + 1` refutes a claimed greatest fixed point. This
  witness is non-vacuous: at least one fixed point exists (all of them do).
- **Literal witness (`f x = x + 1` on `ℤ`).** Monotonicity is
  `Int.add_le_add_right h 1`; fix-freeness is `omega` after `dsimp [f]`.
  Instantiating the universal claim at `Int, f, f_mono` yields a fixed point
  of `f`, contradicting `f_fixfree`.
- All arithmetic is `Int`/`omega`; no `Set`, `Monotone`, `OrderHom`,
  `Finset`, `ZMod`, `Ordinal`, or `Cardinal` is used (none is available in
  core Lean in the needed form).

## Axiom audit

`lake env lean Check.lean` reports:

```
'Tlmc8848.id_isFixed' does not depend on any axioms
'Tlmc8848.id_no_least_fixed' depends on axioms: [propext, Quot.sound]
'Tlmc8848.id_no_greatest_fixed' depends on axioms: [propext, Quot.sound]
'Tlmc8848.id_mono' does not depend on any axioms
'Tlmc8848.refutes_least_fixed_point_with_fixpoint' depends on axioms: [propext, Quot.sound]
'Tlmc8848.refutes_greatest_fixed_point_with_fixpoint' depends on axioms: [propext, Quot.sound]
'Tlmc8848.f_mono' depends on axioms: [propext]
'Tlmc8848.f_fixfree' depends on axioms: [propext, Quot.sound]
'Tlmc8848.refutes_least_fixed_point' depends on axioms: [propext, Quot.sound]
'Tlmc8848.refutes_greatest_fixed_point' depends on axioms: [propext, Quot.sound]
'Tlmc8848.clause_a_false' depends on axioms: [propext, Quot.sound]
'Tlmc8848.clause_a_false_with_fixpoint' depends on axioms: [propext, Quot.sound]
```

No `sorryAx` appears. The only axioms are `propext` and `Quot.sound`, both
core Lean axioms.

## Scope note and honest reading caveat

- **No poset is specified in the conjecture.** A charitable reading supplies
  "complete lattice" (or at least a poset with the relevant sups/infs and a
  sub/supersolution hypothesis). Under that reading, clause (a) becomes the
  Knaster–Tarski theorem and is *true*, and the two `ℤ` witnesses above fall
  outside its scope (the argument type is not complete).
- **Therefore, under a charitable complete-lattice reading, the disproof of
  the conjunction rests on clause (b), argued in prose.** Clause (b) claims
  that the monotone sub/supersolution iteration reaches the extremal fixed
  point in *countably many* steps. The witness `ω₁ + 1` with
  `f(α) = α + 1` for `α < ω₁`, `f(ω₁) = ω₁` is a complete lattice on which
  `f` is order-preserving with unique fixed point `ω₁`; the iteration from the
  subsolution `0` reaches `ω₁` only at stage `ω₁`, i.e. in uncountably many
  steps. A sup-continuity hypothesis (absent from the file) would be needed.
- **Clause (a) is fully formalised; clause (b) is not.** Core Lean has no
  ordinals or cardinals, so `ω₁ + 1` cannot be stated in this project. The
  clause-(b) argument lives in `../main.tex` (rigorous prose) and `../reproduce.py`
  (a clearly-labelled finite simulation plus the standard argument, not a
  computation of the ordinal iteration).
- Under the **literal** reading (no completeness, no fixed-point existence
  assumed), clause (a) is outright false and is refuted here by the shift map;
  the non-vacuous reading is refuted by `id` on `ℤ`.

## Environment

Lean 4.33.1, Lake, no Mathlib. `lake build` needs no cache download (there are
no dependencies and no manifest beyond the empty one Lake creates).
