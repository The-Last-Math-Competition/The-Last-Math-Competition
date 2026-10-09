# Source-first semantic checklist: conjecture 00000001569

Recorded before seeing the candidate implementation or report.

## Sources and reading order

Only `ORIGINAL.md`, then `README.md`, then `README.zh-CN.md` in the supplied clean input directory were read. The two README versions agree on the pertinent solver and reviewer rules. The initial directory listing exposed filenames only. No prior solutions, other conjectures, private selection notes, thread inventory, internet mathematical solutions, or candidate proof contents were consulted.

## Interpretation fixed from the source

The statement says that an n-point set determines at least n² − O(n) distinct angle values, with claimed attainment by lattice families. It specifies no general-position, non-collinearity, convexity, lattice, or other restriction on the point set. The ambient dimension and angle convention are underspecified. The ordinary planar Euclidean interpretation is admissible and should be stated explicitly in a submission.

The natural angle set consists of numerical Euclidean angles at one point of a triple of distinct points of the set. Repeated occurrences of the same angle count once. For the usual unoriented convention angles lie in [0, π]; repeated endpoints and zero-length rays are unnecessary and should be excluded in the formal definition. If only nondegenerate angles in (0, π) are counted, a counterexample based on collinearity remains valid because deleting degenerate angle values only decreases the count. A claim about arbitrary distinct points cannot silently acquire an unstated non-collinearity condition.

The standard uniform asymptotic lower-bound clause has quantifier shape:

  ∃ C ≥ 0, ∃ N ∈ ℕ, ∀ n ≥ N, ∀ planar finite S with |S| = n,
    |Angles(S)| ≥ n² − C n.

Equivalently n can be replaced throughout by |S|. C and N must be independent of S and n. Merely disproving the exact bound n², or one fixed C, or a bound with threshold N = 0, is insufficient. A fully quantified disproof must provide, for every C ≥ 0 and every N, an n ≥ N and a genuine planar n-point set S violating the bound. Proving this for every real C is stronger and acceptable. If coefficients are natural or integer, the equivalence to real nonnegative C must be justified or the statement must directly quantify real C.

A simple family with arbitrarily large cardinality and a uniformly bounded angle set would defeat this clause. Collinear, distinct real planar points are permitted by the literal statement and have only 0 and π as usual unoriented angles. If degeneracies are excluded they determine no allowed angles. This observation is an independent source-first expectation, not a reading of a candidate implementation.

Because the conjecture asserts both the uniform lower bound and its lattice attainment, negating the universal lower bound already refutes the full conjunction. Such a disproof need not resolve or formalize the imprecise lattice-equidistribution assertion. It must explain that logical scope and must not claim an independent theorem about lattice attainment.

## Candidate review checks after release

1. Inspect the entire report, every submitted Lean source, configuration, and auxiliary program. Verify actual submitted files, not only a summary theorem.
2. Check that points live in the usual Euclidean plane with its Euclidean norm/inner product, and that the angle operation denotes actual geometric angle values rather than a surrogate label or arbitrary function.
3. Verify the angle set quantifies all qualifying triples from S, with distinct points and the intended vertex; count its distinct values by genuine finite-set cardinality.
4. Verify the witness family contains n distinct points for unbounded n; ensure formal coercions, filters, or set encodings do not change its cardinality.
5. Check the complete angle-containment calculation and every exceptional/zero-ray case.
6. Check the complete C and N quantifiers and strict violation |Angles(S)| < n² − Cn, or an equivalent contradiction; check small-n issues are bypassed correctly.
7. Check any final named conjecture predicate matches the source interpretation and is actually refuted. Definitions cannot build in witness properties or replace the intended conjecture with an unrelated proposition.
8. Confirm Lean compilation with the pinned Lean 4.19 / Mathlib 4.19 environment and no sorry, admitted goals, native_decide, unsafe proof shortcut, or added axioms. Inspect theorem axiom dependencies.
9. Check the prose/PDF agrees with Lean, explains the asymptotic quantifiers and angle convention, and makes no unjustified stronger claim.
10. Confirm required LaTeX source, PDF, Lean project, reproducibility instructions, and any computation sources are present. Run auxiliary code when supplied; a purely deductive proof needs no invented computational validation.
11. Honor submission scope: review artifacts here only; no repository, leaderboard, metadata, README, conjecture, PR, or external-message mutations are authorized by this review assignment.
