# Disprove conjecture 00000000957: a doubled Mercedes-Benz frame is a local minimum of the frame potential but not a repeated orthonormal basis

The conjecture says local minima of the frame potential FP(Phi) = sum_{i,j} <phi_i,phi_j>^2 on frames of integer redundancy r are r-fold repetitions of an orthonormal basis, and that this classification is complete.

Counterexample: d = 2, r = 3, N = 6, the unit vectors at angles 0, 60, 120 degrees, each taken twice.

- Lean proves the identity FP = N^2/2 + ((sum cos 2t_i)^2 + (sum sin 2t_i)^2)/2 for unit-norm tuples in R^2, so FP >= N^2/2 = 18 everywhere on the unit-norm 6-tuples.
- The doubled Mercedes-Benz frame has both sums equal to 0, so it attains FP = 18: a global, hence local, minimum (`IsLocalMin` in the subtype topology). It is a frame (lower bound 3).
- It is not a signed r-fold repetition of an orthonormal basis: phi_0 and phi_1 have inner product 1/2, but vectors +-e_a, +-e_b have inner product in {0, +-1}.

Main theorems: `C957.main : C957.Claim` (= `not C957.Conjecture`), with `C957.mb_isLocalMin`, `C957.mb_isFrame`, `C957.mb_not_repeated`, `C957.fp_eq`.
Axioms: propext, Classical.choice, Quot.sound only. Reading: unit-norm frames, universal over d and r (the "classification is complete" clause); the true converse (repeated ONBs are minima) is not disputed.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture957/Basic.lean` |
| `lean/Conjecture957/Statement.lean` | the formal statement alone: Mathlib imports and definitions only, ending in `Claim : Prop` (read this file to check faithfulness) |
| `lean/StatementCheck.lean` | machine check that a main theorem has type exactly `Claim` (`verification/statement.txt`) |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000957.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C957.main`.

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

Checked before opening the pull request (2026-10-10): no solution folder for 00000000957 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
