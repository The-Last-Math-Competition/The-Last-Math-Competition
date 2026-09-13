# Lean 4 component — conjecture 00000007121

Toolchain: `leanprover/lean4:v4.33.1` (exact, see `lean-toolchain`).
Library: `Main` (see `lakefile.toml`). Core Lean only: `import Std`, no Mathlib.

## What is formalised

Only the **logical inconsistency of the statement as written**.

The catalogue entry asserts, in one sentence, that the Hirsch bound *holds*
**and** that a *counterexample* to it exists. `HirschBoundHolds` is modelled as
the arithmetic skeleton

```lean
def HirschBoundHolds : Prop := ∀ d f diam : Nat, diam ≤ f - d
```

and `CounterexampleExists` as

```lean
def CounterexampleExists : Prop := ∃ d f diam : Nat, f - d < diam
```

The main results are:

| theorem | content |
|---|---|
| `conjunction_is_contradictory` | pure logic: `¬ (P ∧ ¬P)` for any `P : Prop` |
| `hirsch_and_negation_contradictory` | the above instantiated at `HirschBoundHolds` |
| `counterexample_refutes_bound` | `CounterexampleExists → ¬ HirschBoundHolds` |
| `hirsch_as_written_false` | `¬ (HirschBoundHolds ∧ CounterexampleExists)` |
| `conjecture_00000007121_false` | the two facts above, collected |

## What is NOT formalised — read this

* **The mathematical refutation is not formalised here.** Santos (Annals of
  Mathematics **176** (2012), 383–412) constructed a 43-dimensional polytope
  with 86 facets and graph diameter 44 > 86 − 43 = 43, disproving the Hirsch
  conjecture. This is a literature result; it is quoted in `../main.tex` and in
  `../reproduce.py`, and is deliberately **not** asserted as a theorem in this
  Lean development.
* No polytope, graph, or combinatorial type is modelled. `HirschBoundHolds`
  and `CounterexampleExists` are uninterpreted arithmetic propositions; the
  Lean content is the propositional/arithmetic contradiction between them.
* The name "high-dimensional double configuration" appearing in the catalogue
  entry is **not** the standard name for Santos's object (the standard notions
  are Hirsch polytopes / spindles and the Klee–Walkup and Santos
  constructions). See the caveat in `../README.md`.

## Build

```sh
export PATH="/opt/homebrew/bin:$PATH"
cd lean4
lake build          # build the Main library
lake env lean Check.lean   # statement + axiom audit
```

`Check.lean` runs `#print axioms` on every headline theorem; the expected
result is that none depends on `sorryAx` or any custom axiom.
