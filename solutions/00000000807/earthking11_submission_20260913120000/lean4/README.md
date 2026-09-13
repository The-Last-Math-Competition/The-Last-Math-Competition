# Lean formalisation (conjecture 00000000807)

Toolchain: `leanprover/lean4:v4.33.1` (see `lean-toolchain`).
Core Lean only: `import Std`, **no Mathlib**, no `sorry`, no `axiom`,
no `native_decide`, no `ℝ`.

## Build

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd lean4 && lake build            # exit 0
lake env lean Check.lean          # axiom audit, no sorryAx / ofReduceBool
```

## What is formalised

The triangular lattice is realised by its Gram/quadratic form
`Q(a,b) = a² + ab + b²` on `ℤ²`, which stays in integer arithmetic.  The
square lattice is realised by `S(a,b) = a² + b²`.

* `tri_min` (`theorem`): for all integers `a b`, `(a,b) ≠ (0,0)` implies
  `1 ≤ Q a b`.  Positive definiteness, proved from the identity
  `4 * Q a b = (2a+b)² + 3b²` together with non-negativity of squares.
* `tri_six_shortest`: `Q a b = 1` iff `(a,b)` is one of the six pairs
  `(1,0), (-1,0), (0,1), (0,-1), (1,-1), (-1,1)`.
* `square_four_shortest`: `S a b = 1` iff `(a,b)` is one of the four pairs
  `(1,0), (-1,0), (0,1), (0,-1)`.
* `conjecture_00000000807_false`: collects `squareMult = 4`, `triMult = 6`,
  `4 < 6` and `∃ m, squareMult < m` (the triangular count strictly exceeds the
  square count, so the square torus is not the unique maximiser).

Supporting lemmas: `sq_nonneg` (`0 ≤ a*a`), `sq_le_one`
(`b*b ≤ 1 → b ∈ {-1,0,1}`), `sq_le_four` (`x*x ≤ 4 → -2 ≤ x ≤ 2`).
`Check.lean` runs `#print axioms` for each main theorem; the four theorems
depend only on the core axioms `propext, Classical.choice, Quot.sound`
(and `conjecture_00000000807_false` on none).  No `sorryAx`, no
`ofReduceBool`.

## What is NOT formalised in Lean

* The dual-lattice ↔ Laplace-eigenvalue-multiplicity correspondence
  (`mult(λ₁(T²))` equals the number of shortest non-zero dual vectors).
* The 60° / kissing-number upper bound (at most 6 shortest vectors; equality
  forces the triangular lattice).
* The classification of maximisers up to similarity.

These are stated mathematically in `../main.tex` (Section 2, the
dual-lattice relation (1); Section 5, Theorem 5.1 and its corollary) and
verified numerically with exact rational arithmetic in `../reproduce.py`
(triangular count 6 with common squared length 4/3, square count 4, generic
count 2, and the 60° separation of the six shortest vectors).  The Lean file
provides the exact integer shortest-vector counts on which the refutation
rests.
