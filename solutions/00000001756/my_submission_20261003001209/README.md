# Disproof of conjecture `00000001756`

**Verdict: FALSE — at n = 3 the hook-coprimality formula gives
d(3) = 3, but the true maximal unimodular submatrix order of the S₃
character table is d(3) = 2.**

## The conjecture (verbatim from `conjectures/00000001756.md`)

> Definition: A unimodular submatrix of the character table of S_n is a
> square submatrix with determinant ±1. Conjecture: Its maximal order
> d(n) is characterized by the hook-coprimality condition:
> d(n) = #{λ ⊢ n : hook(λ) pairwise coprime}, an explicit formula; a
> submatrix of that order can be selected from irreducible-character
> rows (sorted by dimension).

## The counterexample (n = 3)

The S₃ character table, rows sorted by dimension (trivial 1, sign 1,
standard 2), columns the conjugacy classes [e], [(12)], [(123)] —
values classical:

```
        |  1   1   2
        |  1  -1   1
        |  2   0  -1
```

1. **The formula's value: 3.** All three partitions of 3 have pairwise
   coprime hook multisets: (3) → hooks {3,2,1}; (2,1) → {3,1,1};
   (1,1,1) → {3,2,1}. So d_formula(3) = 3.
2. **The true maximum: 2.** S₃ has exactly 3 irreducible characters and
   3 conjugacy classes, so the ONLY order-3 square submatrix is the full
   table, whose determinant is 6 ≠ ±1. But order-2 unimodular submatrices
   exist: rows {trivial, standard} × columns {(12), (123)} gives
   det [[1,1],[0,−1]] = −1. Hence the true d(3) = 2.
3. **3 ≠ 2**, so the hook-coprimality "characterization" fails, and the
   claimed dim-sorted selection of an order-3 unimodular submatrix does
   not exist (the unique candidate has det 6).

## Verification

* `reproduce.py` — builds the S₃ character table, computes the
  determinant of every square submatrix (one 3×3, nine 2×2), finds max
  unimodular order 2; independently recomputes all hook multisets of
  the three partitions of 3 from the hook-length formula and counts 3
  pairwise-coprime ones.
* Lean 4 (core, v4.33.1) — `lean4/`: the table determinants (3×3 = 6;
  all nine 2×2, with −1 attained), the pairwise-coprime hook checks for
  all three partitions, and the refutation 3 ≠ 2. All 5 audited
  theorems report `does not depend on any axioms`. The character values
  and hook lengths used are the classical S₃ data.

## Boundary

Only n = 3 is needed to refute the displayed characterization; the
status of the formula at larger n is not addressed.
