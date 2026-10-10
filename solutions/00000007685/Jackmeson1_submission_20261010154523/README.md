# Disprove conjecture 00000007685: the Jackson integral of theta_3(zq)/theta_3(z) has leading coefficient 2, not Gamma(1/4)^2/(2 pi^(3/2))

- **Claim refuted.** The conjunction "J_q transcendental for algebraic q AND leading Puiseux coefficient of J_q in q-1 is c = Gamma(1/4)^2/(2 pi^(3/2))" is false because the second conjunct fails. Transcendence is not addressed.
- **Objects.** theta(w) = sum_{n in Z} q^(n^2) w^n, T(z) = theta(zq)/theta(z), J_q = (1-q) sum_{n>=0} q^n T(q^n) (Jackson measure at z = 1), all built literally in Lean.
- **Closed form.** theta(q^2 w) = q^-1 w^-1 theta(w) gives b_{n+2} = q b_n for b_n = q^n T(q^n), hence J_q = r + 1/r with r = theta(q)/theta(1) (`J_eq`).
- **Bounds.** Termwise comparisons give 1/2 <= r <= 2, so 2 <= J_q <= 4 on (0,1) (`J_bounds`); in fact J_q -> 2.
- **Constant.** Gamma(5/4) <= 1 by convexity, Gamma(1/4) <= 4, pi^(3/2) > 4, so 0 < c < 2 (`c_bounds`).
- **Refutation.** For every real alpha, J_q/(1-q)^alpha cannot converge to L with |L| = c (cases alpha >0, =0, <0); the absolute value makes the branch of (q-1)^alpha irrelevant.
- **Main theorem.** `C7685.main : Claim`, where `Claim := not Conjecture`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 318 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture7685/Basic.lean` |
| `lean/Conjecture7685/Statement.lean` | the formal statement alone: Mathlib imports and definitions only, ending in `Claim : Prop` (read this file to check faithfulness) |
| `lean/StatementCheck.lean` | machine check that a main theorem has type exactly `Claim` (`verification/statement.txt`) |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000007685.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C7685.main`.

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

Checked before opening the pull request (2026-10-10): no solution folder for 00000007685 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
