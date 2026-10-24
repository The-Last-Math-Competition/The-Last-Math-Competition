# Problem 00000001082

The printed MRD equivalence-class asymptotic fails at the standard full-dimension parameters (m,n,k)=(3,2,2). Here codes are F(q^3)-linear subspaces of F(q^3)^2, and k is dimension over the extension field. For every prime q the complete code universe contains exactly the full ambient subspace, whose true minimum rank distance is one and whose true size q^6 attains the rank-metric Singleton bound. Its actual standard linear rank-equivalence quotient therefore has cardinality one. The printed main term is q, and the native relative-error BigO assertion fails at arbitrarily large primes for every proposed bound and cutoff.

The proof constructs the genuine native finite field GaloisField p3 over ZMod p, its actual degree/cardinality and the full code subspace universe. Rank weight is the native base-field finrank of the coordinate span. The minimum is the infimum of all actual distances between distinct codewords, proved nonempty and attained at the real pair ((1,0),0). Module cardinality computes Singleton equality. Equivalence is the standard existence of an ambient extension-field linear equivalence preserving every actual rank weight and mapping the whole code onto the other. No arbitrary Setoid, assigned count or finite list of examples replaces these objects. The native prime-indexed IsBigO proof also excludes every eventual representation A(p)=p*(1+error(p)) with error=O(1/p).

Scope: the printed statement has no k<n or minimum-distance>1 condition. We take n=2<m=3, respecting the strict convention in the cited Morrison definition. The corresponding base-field matrix dimension is mk=6, not k=2. This disproves only the unrestricted printed asymptotic in the standard linear code model. It makes no Gabidulin-only classification claim, no claim about nontrivial-parameter variants, and does not formalize the unspecified cell-decomposition clause. The code universe is already a singleton before quotienting, so broader customary equivalences cannot change the count.

Files:

- `SOURCE.md`: complete original bilingual statement and upstream revision.
- `report.tex`, `report.pdf`: complete mathematical proof, conventions and primary references.
- `lean/Main.lean`: complete proof, namespace `TLMC1082`, main theorem `complete_counterexample`.
- `lean/Check.lean`: traverses the actual environment and runs ordinary `#print axioms` for every owned declaration, including generated names.
- `VERIFICATION.md` and `evidence/`: original source-bound command receipts, logs and complete actual execution/resource samples.
- `SHA256SUMS.json`: every other package file's SHA256 digest.

The project pins Lean4.33.0 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. From `lean/`, run `lean --version`, `lake build +Main`, `lake env lean -DwarningAsError=true Check.lean`, and `lake env leanchecker --fresh Main`. Only `propext`, `Classical.choice` and `Quot.sound` are allowed foundational axioms.
