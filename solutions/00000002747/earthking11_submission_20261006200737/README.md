# Disproof of conjecture `00000002747`

This submission refutes the conjecture's stated capacity formula at the smallest permitted positive parameters, `m = n = 1`, over the standard field `Q`.

## Mathematical argument

Under the standard interpretation, `M_1(M_1(Q))` is the one-dimensional vector space of `1 × 1` rational matrices. Its determinant is its unique entry. If a linear subspace has determinant zero on every member, each of its matrices has its only entry equal to zero. Therefore the only such subspace is `{0}`, and the maximum possible dimension (the capacity in the conjecture's definition) is `0`.

The proposed formula gives

`(m − 1)n² + n = (1 − 1)·1² + 1 = 1`.

Thus the formula asserts capacity `1` where the actual maximum is `0`. Since the conjecture asserts the capacity formula together with a classification clause, failure of the formula already disproves the conjunction; this submission makes no claim about the classification clause.

## Lean formalization

`lean/Main.lean` imports Mathlib's matrix determinant and finite-dimensional linear algebra. It defines the actual `1 × 1` rational matrix space, its determinant-zero subspaces, and the meaning of an attained maximum dimension. Lean proves that every determinant-zero subspace is bottom, has finrank `0`, that bottom is admissible, and that no maximum capacity can equal the displayed value `1`. There are no admissions, `sorry`, or additional axioms.

Build from this directory with `cd lean && lake build`.

## Relationship to the earlier closed submission

The earlier submission in PR #198 correctly identified the same `m = n = 1` mathematical counterexample, but it did not prove it in Lean: its Lean file contained only closed arithmetic statements such as `0 ≠ 1`, and its decisive facts about matrices, determinants, determinant-zero subspaces, and dimension were left in prose. Its `m = n = 2` row-zero-space claim was also not universally verified by the finite random checks in its Python script. This submission fixes the central completeness problem by formalizing the actual matrix space, determinant, admissible subspaces, their dimensions, and the maximum-capacity contradiction in Lean. The PDF and Lean proof correspond to the same `m = n = 1` argument.

The conjecture does not specify a base field or fully define its classification clause. This disproof uses the standard rational-matrix interpretation of the explicit capacity formula, and does not formalize or interpret the undefined classification clause.
