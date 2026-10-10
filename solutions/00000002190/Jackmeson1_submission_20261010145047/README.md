# Disprove conjecture 00000002190: Sperner capacity of C_{2k+1} is not cos(pi/(2k+1))

Lean-checked disproof (`C2190.main`, axioms: propext, Classical.choice, Quot.sound only).

- Reading: Sperner capacity of `C_{2k+1}` on `Fin (2k+1)` for ANY orientation of the cycle, as `lim u(M_n^(1/n))`, `M_n` the largest Sperner code in `G^n`, with `u` = identity (exponential), `logb 2` (bits), `log` (nats). The undirected zero-error Shannon capacity is also covered. The conjecture is for all `k >= 1`; it fails at `k = 1`, where `cos(pi/3) = 1/2`.
- Sperner: one arc `a -> b` gives the words over `{a,b}` of weight `n/2`; any two distinct such words have a coordinate `(a,b)`. So `M_n >= C(n, n/2) >= 2^n/(n+1)`, hence `liminf M_n^(1/n) >= 2`, i.e. capacity at least 2, 1 bit, ln 2 = 0.69 nats, each above 1/2.
- Shannon: `C_3 = K_3` has no non-adjacent distinct letters, so `M_n = 1` and the capacity is 1 (0 in logs), not 1/2.
- Not refuted: base-4 logarithm at k = 1 (cyclic triangle capacity 2 would give exactly 1/2), and natural-log units for k >= 2 individually (not needed, since the claim is for all k).
- Statement block is at the top of `Basic.lean`; proof.pdf has the details.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2190/Basic.lean` |
| `lean/Conjecture2190/Statement.lean` | the formal statement alone: Mathlib imports and definitions only, ending in `Claim : Prop` (read this file to check faithfulness) |
| `lean/StatementCheck.lean` | machine check that a main theorem has type exactly `Claim` (`verification/statement.txt`) |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002190.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2190.main`.

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

Checked before opening the pull request (2026-10-10): no solution folder for 00000002190 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
