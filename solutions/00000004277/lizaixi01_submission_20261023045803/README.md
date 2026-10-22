# Disproof of 00000004277: an uncountable maximal height-type chain

The source asserts that every maximal chain of the type lattice has the countable order type omega followed by reverse omega. In the actual full standard height-type lattice, prime-indexed zero/infinity rational cuts give an injective monotone map from the reals. Its genuine range is an uncountable chain; an actual IsMaxChain extension remains uncountable and admits no order isomorphism with Nat ordinal-sum OrderDual Nat.

The formalization uses all characteristics (Nat with infinity)^Primes. The equivalence permits only finitely many changed finite coordinates, preserving the entire infinity pattern. The quotient preorder is proved equivalent to the standard order by pointwise-comparable equivalent representatives. A genuine Lattice instance and exact quotient coordinate minimum/maximum formulas are proved. This is the classical height-type lattice, called h-types in Bunina arXiv:2409.07728v1 section 3.3, pp. 4-5; it is not the lattice of complete first-order logical types.

Only the universal order-type necessary clause is refuted. The proof does not assert that the total number of maximal chains differs from continuum, or claim a Lean formalization of the separate rank-one group classification theorem. The original bilingual source is included.

## Reproduce

From lean/ with elan installed:

```sh
lake exe cache get
bash verify.sh
```

Lean 4.33.0 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d are pinned. A new root build, 25 transitive audits (22 theorems and three proof-bearing instances), and full official leanchecker --fresh Main replay are required. Complete LaTeX/PDF, source-bound receipts/logs and SHA256 manifest accompany the proof. No sorry, native_decide or additional axiom. Source/report/PDF reviewed by worker and separate supervising AI agent; organizer acceptance is pending.
