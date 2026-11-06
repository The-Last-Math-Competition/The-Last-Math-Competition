# Problem 00000002101

Under the usual golden-ratio convention phi=(1+sqrt5)/2, the printed explicit value phi^(1/2) and membership in the units of Q(sqrt5) are incompatible. Every complex square root of this actual number lies outside the actual quadratic field. This rules out a necessary conjunction in the statement.

The complete proof constructs the native QuadraticAlgebra Q5,0 and proves the rational nonsquare condition that supplies its genuine Field instance. Its actual basis has degree two. Native conjugation and the real/complex algebra embeddings are constructed, and both field ranges are proved equal to the full native IntermediateField.adjoin Q{sqrt5}; actual algebra equivalences identify the fields. The native Algebra.norm is connected to the determinant of actual left multiplication and to the quadratic norm and conjugation product. The golden element's native norm is computed as -1, and norm transport is proved also in the actual real and complex adjoined fields. A rational squared norm cannot be negative, excluding every field square root. The actual Real.sqrt value, positivity, square equation, both real/complex branches, every embedding-image obstruction and the actual complex-field-unit obstruction are proved.

Scope: phi denotes the usual golden ratio, which the report explicitly defines. This proves the impossibility of simultaneously satisfying the printed numerical-value and field-unit clauses. It does not assign or compute a Stokes constant, construct substitute Stokes data, disprove the field-unit assertion on its own, or dispute general DT-RH theory. A generic pointwise theorem applies to every possible scalar family. Bridgeland's actual Kronecker BPS data and RH jump formulation are cited for context, not as evidence that the printed numerical value is a true Stokes constant. No claim is made under an unstated different meaning of phi.

Files:

- `SOURCE.md`: complete original bilingual statement and upstream revision.
- `report.tex`, `report.pdf`: complete proof, precise numerical convention, scope and primary reference.
- `lean/Main.lean`: complete proof, namespace `TLMC2101`, main theorem `complete_counterexample`.
- `lean/Check.lean`: traverses the real imported environment and runs ordinary `#print axioms` on every owned declaration, including generated names.
- `VERIFICATION.md` and `evidence/`: original source-bound verification receipts, logs and full actual execution/resource data.
- `SHA256SUMS.json`: digests of every other package file.

Lean4.33.0 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d` are pinned. From `lean/`, run `lean --version`, `lake build +Main`, `lake env lean -DwarningAsError=true Check.lean`, and `lake env leanchecker --fresh Main`. Only `propext`, `Classical.choice` and `Quot.sound` are allowed foundational axioms.
