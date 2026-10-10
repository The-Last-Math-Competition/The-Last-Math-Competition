# Disprove conjecture 00000000781: closed-subgroup lattice of 1+2Z_2 is not a quotient lattice of the integers

Lean statement and proof: `C781.main : C781.Claim`.

- Reading: the conjecture is taken for every prime p (neither the English nor the Chinese text restricts p); it fails at p = 2.
- `U1 p` is `1 + pZ_p` inside `Z_p^x` (units `u` with `p | u - 1`); the lattice is `ClosedSubgroup (U1 p)` ordered by inclusion (a lattice isomorphism is an order isomorphism).
- "Quotient lattice of the integers" is formalized as a surjective lattice-homomorphic image of (Z, <=), of the subgroup lattice of Z, of its dual (divisibility lattice), or the subgroup lattice of Z/nZ. All are proved distributive.
- In `1 + 2Z_2` the closed subgroups `H_a = {u = 1 or a mod 8}` for a = 3, 5, 7 form a diamond M3 (pairwise meets `1 + 8Z_2`, pairwise joins the whole group), so the lattice is not distributive.
- Not claimed: odd p (where the statement is plausibly true) and senses of "quotient lattice" outside the four listed.
- The valuation-stratification clauses are conjuncts, so refuting the existence of the isomorphism refutes them too.
- Main theorems: `C781.main`. Axioms: propext, Classical.choice, Quot.sound only.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture781/Basic.lean` |
| `lean/Conjecture781/Statement.lean` | the formal statement alone: Mathlib imports and definitions only, ending in `Claim : Prop` (read this file to check faithfulness) |
| `lean/StatementCheck.lean` | machine check that a main theorem has type exactly `Claim` (`verification/statement.txt`) |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000781.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C781.main`.

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

Checked before opening the pull request (2026-10-10): no solution folder for 00000000781 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
