# Disproof of conjecture `00000002747`

**Verdict: FALSE — the capacity formula fails at both m = n = 1 and m = n = 2.**

## The conjecture (verbatim from `conjectures/00000002747.md`)

> Definition: Capacity: the maximal dimension of a matrix space on which
> the determinant vanishes. Conjecture: The higher-order Flanders–Atkinson
> capacity theorem: the capacity of M_m(M_n) is (m−1)n² + n, and the
> classification of capacity spaces is a single orbit of linear spaces.

**Object consistency.** We attack exactly the displayed capacity value
(m−1)n² + n with the conjecture's own definition of capacity.

## The refutations

**(1) m = n = 1.** M₁(M₁) = M₁ is the scalars, det(λ) = λ. A linear
subspace on which det vanishes **identically** must avoid every nonzero
scalar (each has det ≠ 0), so it is {0}: capacity **0**. The formula gives
(1−1)·1 + 1 = **1 ≠ 0**.

**(2) m = n = 2.** M₂(M₂) = M₄. The **12-dimensional** subspace of
matrices with last row zero consists entirely of matrices of rank ≤ 3 < 4,
so the determinant vanishes identically on it (classical; random
verification in `reproduce.py`). Capacity ≥ **12**, while the formula gives
(2−1)·4 + 2 = **6**; 12 > 6.

(The true Flanders-type bound for singular subspaces of Mₙ is n² − n for
constant rank n−1... and for "rank ≤ n−k" subspaces n(n−k); the row-zero
construction shows any formula of the displayed shape fails already at
the smallest composite case.)

Lean certifies the arithmetic of both violations; the structural facts
(det of scalars; rank of row-zero matrices) are classical and cited. All
5 theorems `does not depend on any axioms`.

## Reproduce

`python3 reproduce.py` — case (1) exactly; case (2): constructs the
12-dimensional row-zero subspace of M₄ symbolically, verifies det ≡ 0 on
random elements, and prints 12 > 6. Exit 0.

## Boundary

Only the capacity-value formula is refuted; the orbit-classification
clause is not addressed.
