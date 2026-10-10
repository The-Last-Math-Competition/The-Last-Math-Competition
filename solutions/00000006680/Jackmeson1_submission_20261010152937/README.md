# Prove conjecture 00000006680: finite transport problems with equal value and different dual structure

Finite discrete Kantorovich transport on 2x2 with marginals (1/2,1/2) and cost [[0,0],[a,b]], 0 <= a <= b.
- Same optimal value a/2 for (a,a) and (a,b), a < b, with no duality gap (explicit dual potentials).
- Dual structure: for a=b the optimal dual is unique modulo the gauge (u+t, v-t); for a<b it is not.
- Support: the family of optimal-plan supports differs (full support is optimal only for a=b); for the zero-cost pair
  (a=0) the cost supports also differ (empty vs {(1,1)}). A nonzero pair (a=1) is also proved.
- Main theorems: `C6680.main : Claim` (ConjectureA and ConjectureB, both readings of "support"), `C6680.main_nonzero`.
- Lean reuse: the 2x2 plan parametrisation is adapted from our accepted solution of conjecture 00000006320.
- Only propext, Classical.choice, Quot.sound; no sorry, no native_decide.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture6680/Basic.lean` |
| `lean/Conjecture6680/Statement.lean` | the formal statement alone: Mathlib imports and definitions only, ending in `Claim : Prop` (read this file to check faithfulness) |
| `lean/StatementCheck.lean` | machine check that a main theorem has type exactly `Claim` (`verification/statement.txt`) |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000006680.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C6680.main`, `C6680.main_nonzero`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
lake env lean StatementCheck.lean
```

## Eligibility

Checked before opening the pull request (2026-10-10): no solution folder for 00000006680 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
