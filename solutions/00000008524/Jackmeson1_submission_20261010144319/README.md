# Disprove conjecture 00000008524: differential dimension polynomial need not have degree = number of variables

Disproof of the clause "the degree of the differential dimension polynomial is the number of variables".

- Setting (Lean, `DRing n m`): `Q{y_1..y_n}` with `m` commuting derivations, `delta_k y_{j,theta} = y_{j,theta+e_k}`; differential ideal = ideal stable under all `delta_k`; `omega_I(t)` = Krull dimension of `Q[y_{j,theta}, |theta|<=t] / (I cap that ring)`; dimension polynomial = `P in Q[X]` with `omega_I(t) = P(t)` for large `t`.
- Witness: `n = m = 1`, the prime differential ideal `[y']` (kernel of `y_0 -> X, y_k -> 0`). Then `omega(t) = 1` for all `t`, so the dimension polynomial is the constant 1, of degree 0, not 1.
- Both readings of "number of variables" (derivations `m`, indeterminates `n`) are refuted; `C8524.not_conj` refutes every reading `N` with `N 1 1 != 0`.
- Not refuted: rational coefficients and the `1/N!` clause (both hold for the witness); a reading with `N 1 1 = 0`.
- Main theorems: `C8524.not_conj`, `C8524.main : Claim`. No axioms beyond propext, Classical.choice, Quot.sound.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture8524/Basic.lean` |
| `lean/Conjecture8524/Statement.lean` | the formal statement alone: Mathlib imports and definitions only, ending in `Claim : Prop` (read this file to check faithfulness) |
| `lean/StatementCheck.lean` | machine check that a main theorem has type exactly `Claim` (`verification/statement.txt`) |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000008524.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C8524.main`, `C8524.not_conj`.

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

Checked before opening the pull request (2026-10-10): no solution folder for 00000008524 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
