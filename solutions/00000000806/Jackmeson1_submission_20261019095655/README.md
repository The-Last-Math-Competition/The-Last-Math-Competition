# Disprove conjecture 00000000806: two equal disjoint disks have zero Dirichlet spectral gap ratio

The conjecture asserts that the ratio R = (lambda_2 - lambda_1)/lambda_1 of Dirichlet eigenvalues is maximal, with value 3/4, on a union of two equal disjoint disks. For such a union lambda_1 = lambda_2, so R = 0, not 3/4.

- Lean (`lean/Conjecture806/Basic.lean`, 417 lines) builds the objects: `testSpace` = C_c^infty(Omega) in the plane, Dirichlet energy and L2 norm as lintegrals, the Rayleigh quotient, `lam k Omega` by the Courant-Fischer min-max over k-dimensional subspaces, and `R`.
- `R_two_disks`: for all c1, c2, r with disjoint balls, `lam 1 = lam 2` and `R = 0`; `not_conjecture : not Conjecture` where `Conjecture` states the three clauses of the text.
- Proof: splitting a test function along the two disks, translation invariance, and a two-dimensional space spanned by a function and its translate on which the Rayleigh quotient is constant.
- `testSpace_ne_bot` shows the test space on a ball is nontrivial.
- Axioms: propext, Classical.choice, Quot.sound only.
- Convention: eigenvalues counted with multiplicity; the "distinct eigenvalues" reading is discussed in proof.tex but not formalized.
- Replaces closed PR #1051, whose Lean modelled the gap and ratio as natural-number subtraction.

**Previous submission and its error (README rule 2).** PR #1051 by quantumtool (closed, not merged) disproved this conjecture with a Lean project that the reviewer rejected: "the Lean project does not formalise the conjecture. The spectral gap and ratio are modelled as subtraction and a pair of natural numbers; no domain, Laplacian or eigenvalue is defined." This submission instead formalizes the actual objects: open subsets of the plane, the space of smooth compactly supported functions, the Dirichlet energy and Rayleigh quotient as Lebesgue integrals, the Dirichlet eigenvalues lambda_k by the Courant-Fischer min-max principle (counted with multiplicity), and the ratio R, and it proves from these definitions that R = 0 for every union of two disjoint open disks of equal radius.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture806/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000806.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C806.not_conjecture`, `C806.R_two_disks`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-19): no solution folder for 00000000806 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
