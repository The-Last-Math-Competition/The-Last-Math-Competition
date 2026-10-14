# Conjecture 00000007302: the ordinary extreme-point density clause

This submission gives a formal counterexample to ordinary relative density of
the extreme points in a tensor nuclear-norm unit ball. The tensor space is the
actual real algebraic tensor product of three Euclidean two-dimensional spaces.
Its installed norm is proved equal to the infimum of the sums of products of
factor norms over all finite pure-tensor decompositions. The origin belongs to
the closed unit ball and lies outside the closure of its real extreme points.

The exact bilingual original is preserved in `conjecture.md`. Its convex-envelope
definition and additional parameter-space wording are incomplete. The result
addresses the ordinary necessary density clause. It does not reconstruct the
parameter-space clause, or assert a result about density of convex combinations
or density only in the boundary. See `report.pdf` and `report.tex` for the proof
and its interpretation limits.

The final Lean declarations are
`Conjecture7302.nuclear_extremePoints_not_relatively_dense` and
`Conjecture7302.nuclear_ball_counterexample`. This analytic proof needs no
numerical search or auxiliary numerical computation.

The project is pinned to Lean 4.19.0 and Mathlib revision
`c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0). All nine package revisions are
fixed in `lean/lake-manifest.json`; independently supplied copies are in
`evidence/expected-pins/`. From the package directory, with the pinned toolchain
and dependencies available:

```sh
cd lean
lake build
lake env lean -DwarningAsError=true DecompositionBridge.lean
lake env lean -DwarningAsError=true GenericExtreme.lean
lake env lean -DwarningAsError=true TensorNuclear.lean
lake env lean -DwarningAsError=true Conjecture7302.lean
lake env lean -DwarningAsError=true AxiomAudit.lean
lake env lean -DwarningAsError=true lakefile.lean
```

`AxiomAudit.lean` prints the axioms of all 21 selected capstones. The four
mathematical modules, this auxiliary, and all three project configuration files
are byte-identical to the independent review snapshot. `lean/.gitignore` excludes
local `.lake/` products. The package contains no dependency cache or compiled
Lean artifact.

`VERIFICATION.md` gives the full verification procedure, measured counts, and
trust limits. All 61 safe declaration roots use only `propext`, `Classical.choice`
and `Quot.sound`. The 15 generated unsafe compiler helpers, including three
unsafe specialization axioms, are explicitly inventoried outside every safe
root's closure. They are not proof assumptions.

`evidence/engineering-records.tar.gz` contains the complete retained raw
engineering records, including all 60 command receipts and their output, the
declaration graph, import identities, pinned-source inventories, controls and
runtime identities. `evidence/engineering-records-manifest.json` lists the path,
size and SHA-256 of every archived file. It excludes the private cloned project,
dependency caches and compiled artifacts. Unchanged generic verifier sources
are in `verification-tools-v2/`; final independent reviews are in
`evidence/reviews/`. The report's build receipt, log and four inspected page
images are in `evidence/report/`.

The source/report reviews and final all-page visual review are incorporated.
`package-preparation.json` records this assembly and its inputs; it is not a
replacement for the final package review or a fresh publication decision.
`SHA256SUMS` covers every package file except itself, including the preparation
record. The preparation record's content inventory excludes itself and
`SHA256SUMS`, preventing a hash cycle. From the package directory:

```sh
shasum -a 256 -c SHA256SUMS
```

The initial and final public-eligibility summaries are dated observations, not
maintainer acceptance. Publication requires the separate final package review
and a decision based on sufficiently current public state.
Historical receipts retain their original local paths for provenance; those
paths are not prerequisites for the portable `lake build` commands above.
