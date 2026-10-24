# Problem 00000000620: two integer Khovanov groups change

The counterexample addresses the printed alternating-knot clause, using standard unreduced normalized integral bigraded Khovanov groups. The positive closed two-braid with three crossings is connected and alternating. Reversing only its last over-under relation gives a diagram whose groups in bidegrees (2,5) and (3,9) vanish, whereas both original groups have explicit nonzero integer quotient classes.

The Lean construction starts from actual closure and crossing port pairings. It proves the oriented traversal, one component, alternating status and unique crossing flip. The eight-state smoothing circles in each diagram are identified with native graph connected components through checked paths and representative certificates. The native dual-number multiplication and comultiplication, actual circle tensor-product bases and unaffected-circle reindexing determine the complete signed differential. Both grading laws and square-zero are checked on every actual enhanced state.

The homology groups are native integer cycle submodules modulo the range of the complete incoming differential. An actual cycle and integer functional pairing -1 prove the first nonzero class; the all-positive top tensor and its coordinate probe prove the second. An integer right inverse of the changed cube's top differential proves its second-degree groups zero in every quantum degree; its third-degree chain groups are zero. Additive group isomorphisms are excluded in both stated bidegrees.

The identification with the standard Khovanov cube is the explicit published definition in Dror Bar-Natan's 2022-23 handout, cited in the report. This development does not formalize ambient isotopy of spatial embeddings or reprove the general Reidemeister theorem. Classification as a trefoil and recognition of the changed diagram as an unknot are unnecessary for these direct diagram computations. The separate nonalternating parenthesis is outside the conclusion.

The complete bilingual conjecture is preserved in SOURCE.md. The package contains report.tex, report.pdf and the pinned Lean project. Run these commands inside lean/:

```
lean --version
lake build +Main
lake env lean -DwarningAsError=true Check.lean
lake env leanchecker --fresh Main
```

Lean 4.33.0 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d are pinned. Check.lean emits ordinary axiom reports for every actual declaration in TLMC620, including all generated names, and checks namespace coverage. No sorry, native_decide or additional axioms are used. Source-bound execution receipts, complete logs and a hash manifest accompany the final proof package. Production timings are diagnostic and establish no controlled efficiency improvement.
