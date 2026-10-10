# Disprove conjecture 00000001305: the Kobayashi pseudodistance of C^2 minus Z^2 vanishes identically

- **Reading.** D = C^2 \ Z^2; d_K = Kobayashi pseudodistance (infimum over finite holomorphic unit-disc chains in D of the sum of Poincare distances artanh|(a-b)/(1-conj(a)b)|). "Degenerates in a direction" = d_K = 0 between points differing only in that coordinate; "non-degenerate" = d_K > 0 between distinct such points. Both assignments of horizontal/vertical to the two coordinates are refuted.
- **Result.** d_K(p,q) = 0 for all p, q in D. In particular (i,0),(i,1) and (0,i),(1,i) are at distance 0, so the claimed non-degeneration in the "vertical" direction fails (and by the coordinate swap there is no asymmetry).
- **Idea.** Any two distinct points of D lie on an entire curve in D (only countably many parameters s are bad in the family t -> (p1+t u1, p2+t u2 + s t(t-1))); rescaling t -> R t gives a disc joining them at parameters 0 and 1/R, so d_K <= artanh(1/R) -> 0. For the example above the curve is just z -> (i, R z).
- **Lean.** d_K is built from the definition (inductive chain predicate, infimum in ENNReal), not assumed. `C1305.Claim` = not (ReadingA or ReadingB) and d_K = 0 on D.
- **Main theorem.** `C1305.main` (also `C1305.dK_eq_zero`).
- **Not formalised.** The infinitesimal Kobayashi-Royden metric reading (same discs, vertical derivative R, so it also vanishes); argued in proof.tex only.
- **Lean build.** Lean 4.33.1, Mathlib v4.33.1, 208 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture1305/Basic.lean` |
| `lean/Conjecture1305/Statement.lean` | the formal statement alone: Mathlib imports and definitions only, ending in `Claim : Prop` (read this file to check faithfulness) |
| `lean/StatementCheck.lean` | machine check that a main theorem has type exactly `Claim` (`verification/statement.txt`) |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000001305.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C1305.main`, `C1305.dK_eq_zero`.

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

Checked before opening the pull request (2026-10-10): no solution folder for 00000001305 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
