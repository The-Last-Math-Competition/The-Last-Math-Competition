# Disproof of conjecture `00000002733`

**Verdict: FALSE — dimension 4 already has (at least) three bistellar
classes, and the parity criterion fails.**

## The conjecture (verbatim from `conjectures/00000002733.md`)

> Definition: The T-construction and bistellar flips: elementary
> operations on combinatorial manifolds. Conjecture: Connectivity of
> bistellar flows: the number of bistellar equivalence classes of
> d-dimensional combinatorial manifolds is at most two for d ≥ 4, decided
> by the parity of middle Betti numbers; for d = 3 the class count has a
> logarithmic upper bound in the vertex count.

**Object consistency.** We attack exactly the d ≥ 4 clause: "at most two
bistellar classes, decided by middle-Betti parity". Bistellar equivalence
= PL homeomorphism (Pachner's theorem, classical).

## The refutation

In **d = 4**, the three closed combinatorial 4-manifolds

| manifold | χ (classical) | β₂ | parity of β₂ |
|---|---|---|---|
| S⁴ | **2** | 0 | even |
| ℂP² | **3** | 1 | odd |
| S²×S² | **4** | 2 | even |

have **pairwise distinct Euler characteristics** (2 ≠ 3 ≠ 4 ≠ 2). The
Euler characteristic is invariant under bistellar moves (equivalently
under PL homeomorphism — classical, cited), so these are **three distinct
bistellar classes**: at least 3 > 2 in dimension 4.

Moreover the parity criterion fails on the same triple: S⁴ and S²×S² both
have **even** middle Betti numbers (0 and 2), yet are inequivalent
(χ 2 ≠ 4).

Lean certifies the arithmetic (pairwise distinctness, 3 > 2, the evenness
pair, 2 ≠ 4); the Euler characteristics and invariance are classical cited
facts. All 7 theorems `does not depend on any axioms`.

## Reproduce

`python3 reproduce.py` — the three χ values from standard cell
decompositions (S⁴: one 0-cell + one 4-cell; ℂP²: cells in dimensions
0,2,4; S²×S²: product cells), pairwise distinctness, and the parity
failure. Exit 0.

## Boundary

Only the d ≥ 4 clause is refuted; the d = 3 logarithmic-bound clause is
not addressed.
