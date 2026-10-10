# Disprove conjecture 00000003968: graceful-labeling counts of caterpillars have no rational generating function

Disproves the rationality of the ordinary generating function of the number of graceful labelings of n-vertex caterpillar trees, under four counting conventions.

- Caterpillar = tree with an induced path (spine, `pathGraph k`) such that every vertex is on it or adjacent to it. Graceful = bijection to `{0..n-1}` whose edge differences hit each of `1..n-1` exactly once.
- Conventions refuted (all formalized): (A) one representative per isomorphism class, graceful bijections counted; (B) pairs (caterpillar on `Fin n`, graceful bijection); (C) graceful caterpillar edge sets on `{0..n-1}` (labelings up to automorphism); (D) as (C) with a labeling identified with its complement `x -> n-1-x`.
- Core: for `n = 12 s` an explicit family of `s!` pairwise different graceful caterpillar edge sets, indexed by permutations of `Fin s` (zigzag spine plus `s` leaves whose attachment is permuted). Hence every count is at least `s!` (D: classes are told apart by the neighbours of vertex 0).
- A rational power series has at most exponentially growing coefficients (proved via the linear recurrence), contradicting `s! > M R^(12 s)` for large `s`.
- The "denominator given by the partition function of the spine length" clause is not formalized; refuting rationality refutes the conjunction.
- Not covered: exponential generating function; (A)/(B) with the complement identified (informally at most a factor 2).
- Main theorem: `C3968.main : C3968.Claim`. Axioms: standard only.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture3968/Basic.lean` |
| `lean/Conjecture3968/Statement.lean` | the formal statement alone: Mathlib imports and definitions only, ending in `Claim : Prop` (read this file to check faithfulness) |
| `lean/StatementCheck.lean` | machine check that a main theorem has type exactly `Claim` (`verification/statement.txt`) |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000003968.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C3968.main`.

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

Checked before opening the pull request (2026-10-10): no solution folder for 00000003968 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
