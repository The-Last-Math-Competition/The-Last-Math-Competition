# Disprove conjecture 00000004391: the half graph does not minimize the spectral radius at fixed edge density

Refutes the minimum clause of the conjecture (hence the conjunction with the twin-clique maximum clause, which is not formalized).

- Graphon = symmetric measurable `W : [0,1]^2 -> [0,1]`; density = `int int W`; operator `(T_W f)(x) = int_0^1 W(x,y) f(y) dy`; eigenvalue = real `lam` with `f` in `L^2`, not a.e. zero, `T_W f = lam f` a.e.; spectral radius = sSup of eigenvalues ("largest eigenvalue"), and also the sSup of `|lam|` as a second reading.
- The constant graphon `p` has density `p` and spectral radius exactly `p` (eigenfunction 1, plus the bound `|lam| <= c` for `W <= c`).
- Half graph `1[x+y<=1]` (density 1/2) has the eigenfunction `cos(pi x/2)` with eigenvalue `2/pi > 1/2`; the bipartite half graph (density 1/4) has eigenvalue `1/pi > 1/4`. So neither minimizes at its density.
- Both radius readings and both half-graph conventions are refuted.
- Main theorem: `C4391.main : C4391.Claim` (`Claim := not Conjecture`). Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture4391/Basic.lean` |
| `lean/Conjecture4391/Statement.lean` | the formal statement alone: Mathlib imports and definitions only, ending in `Claim : Prop` (read this file to check faithfulness) |
| `lean/StatementCheck.lean` | machine check that a main theorem has type exactly `Claim` (`verification/statement.txt`) |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000004391.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C4391.main`.

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

Checked before opening the pull request (2026-10-10): no solution folder for 00000004391 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
