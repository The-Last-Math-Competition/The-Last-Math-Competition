# Disprove conjecture 00000001463: lambda(ell_infty^n) = 1, so ell_infty^n does not attain c*sqrt(n)

Reading: lambda(E) is the standard absolute projection constant: the supremum, over Banach spaces X containing an isometric copy j(E), of the infimum of ||P|| over bounded projections P of X onto j(E). ell_p^n is K^n with the p-norm (Mathlib `PiLp`), K = R or C.

The conjecture asserts one constant c with sup_p lambda(ell_p^n) = c sqrt(n) and lambda(ell_1^n)/(c sqrt n) -> 1 and lambda(ell_infty^n)/(c sqrt n) -> 1.

- Lean proves lambda(ell_infty^n) <= 1 (Hahn-Banach: extend each coordinate functional of the copy to X, then P = j o (g_i)_i has norm <= 1) and lambda >= 0.
- Hence for every real c (c < 0, c = 0, c > 0) lambda(ell_infty^n)/(c sqrt n) does not tend to 1, for K = R and K = C.
- The weaker reading "lambda(ell_infty^n) >= kappa sqrt n for some kappa > 0 and all n >= 1" is refuted as well.
- Not addressed: relative projection constants (fixed superspace), and the claims about ell_1^n and the exact supremum (not needed for the refutation).

Main theorem: `C1463.main : Claim`, where `Claim` is the conjunction of the four negations (ConjSharp and ConjOrder, over R and C). Lean 4 / Mathlib v4.33.1, no sorry.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture1463/Basic.lean` |
| `lean/Conjecture1463/Statement.lean` | the formal statement alone: Mathlib imports and definitions only, ending in `Claim : Prop` (read this file to check faithfulness) |
| `lean/StatementCheck.lean` | machine check that a main theorem has type exactly `Claim` (`verification/statement.txt`) |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000001463.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C1463.main`.

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

Checked before opening the pull request (2026-10-10): no solution folder for 00000001463 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
