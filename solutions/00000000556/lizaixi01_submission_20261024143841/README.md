# Problem 00000000556: zero HH1 with infinite representation type

The nine-dimensional rational path algebra of the four-leaf extended-D4 star has actual first Hochschild cohomology zero and infinitely many pairwise nonisomorphic indecomposable six-dimensional modules. This refutes the printed necessary implication HH1=0 implies representation-finite, independently of every possible additional rigidity predicate.

The statement is treated as the printed general algebra assertion. The four arrows entering the central vertex violate the at-most-two-incoming condition for string algebras. This is not a counterexample to a version restricted to that subclass.

Lean constructs the native square-zero algebra and identifies its full basis with all actual `Quiver.Path` objects, with genuine concatenation and zero products of noncomposable paths. It constructs all degree-zero, one and two bar cochains, the actual tensor-Hom equivalence, standard coboundaries and native `ShortComplex.homology`. An explicit corrector obtained from every derivation's own values proves exactness and zero HH1.

Every member of the module family is a genuine finite-dimensional left module. All native algebra-linear morphisms are classified: distinct parameters have zero Hom, and every endomorphism is scalar. Actual complementary-submodule projections prove indecomposability. An injection from Q into the native linear-isomorphism quotient of all finite indecomposable module objects proves infinite representation type. Finite generation over the algebra is proved equivalent to finite rational dimension.

The closed, unmerged PR134 and its rejection/author-withdrawal comments are fully discussed in the report. That submission replaced rigidity by Frobenius/self-injective and used a Nat-pair certificate without the required field-based cohomology and module-category bridge. This proof attacks the other implication and does not assign a meaning to rigid.

The standard first Hochschild cochain model is Loday, Cyclic Homology, second edition, Section1.5, pages37-38. The actual low-degree complex sufficient for HH1 is formalized; no higher cohomology or general derived-functor comparison is asserted. The complete original bilingual source is in SOURCE.md.

Run inside lean/:

```
lean --version
lake build +Main
lake env lean -DwarningAsError=true Check.lean
lake env leanchecker --fresh Main
```

The project pins Lean4.33.0 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The dynamic ordinary axiom audit covers every namespace declaration and generated auxiliary. No sorry, native_decide or additional axioms are used. The full logs, source-bound execution receipts, actual CPU-mask samples and SHA-256 manifest are included. Production times do not establish a controlled research-efficiency gain. Organizer acceptance is pending.
