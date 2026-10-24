# Problem 00000000567

The printed formula fails for the ordinary finite-dimensional representation category of the no-arrow Dynkin quiver A1 and its actual Karoubi envelope. The quotient of all maximal-rigid objects by actual categorical isomorphism is infinite. With the conventional basic requirement the full quotient has cardinality one. The genuine Coxeter product is two, so both counting conventions contradict the first clause.

The proof uses the standard add-closure definition of maximal rigidity and also establishes both actual Ext¹-orthogonal equalities. It constructs the full quiver/path/functor category over C, native Karoubi completion, explicit range image and splitting of every idempotent, all-object projectivity and native derived-category Ext. Native finite biproducts, actual categorical retractions, basis classification and coordinate inclusion/projection establish the object and basic classification. All isomorphism quotients range over the complete category. The rank-one native RootPairing and Base, the actual basis/quiver-vertex identification, true simple-reflection product/order and eigen-exponent set derive the Coxeter data and product rather than assigning them.

This concerns the ordinary representation category printed in the source. It makes no claim against the Catalan enumeration in the derived orbit cluster category, and does not address the preprojective-algebra clause.

Files:

- `SOURCE.md`: the complete original bilingual statement and upstream revision.
- `report.tex`, `report.pdf`: complete mathematical argument, scope and primary references.
- `lean/Main.lean`: the complete proof, namespace `TLMC567`, main theorem `complete_counterexample`.
- `lean/Check.lean`: enumerates every owned namespace declaration, including generated declarations, and invokes ordinary `#print axioms` on all of them.
- `VERIFICATION.md` and `evidence/`: actual source-bound original command receipts, logs and complete resource samples.
- `SHA256SUMS.json`: hashes of every other package file.

The project pins Lean4.33.0 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. From `lean/`, run `lean --version`, `lake build +Main`, `lake env lean -DwarningAsError=true Check.lean`, and `lake env leanchecker --fresh Main`. The only allowed foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`.
