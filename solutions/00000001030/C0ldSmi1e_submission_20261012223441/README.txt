CONJECTURE 00000001030 — SPHERICAL 5-DESIGNS

Result

The ordinary minimum is attained and equals 12. Every twelve-point design is
orthogonally congruent to the displayed normalized icosahedron. If the original
parenthetical instead excludes icosahedral designs, an attained minimum of 12
is false: every remaining design has at least 13 points. We do not assert that
13 is attained or determine the exact minimum of that excluded class.

Read report.pdf (with matching report.tex) for the complete mathematical proof,
scope discussion, and correspondence with Lean. conjecture.md preserves the
exact bilingual repository statement. The definition uses distinct, equally
weighted points and every real polynomial of total degree at most five,
integrated against proved normalized two-dimensional Hausdorff surface measure
on the Euclidean unit sphere. The final theorems have no extra moment premises.

Reproduce the Lean proof

Install the Lean toolchain manager elan, then from this submission directory:

  cd lean
  lake exe cache get
  lake --wfail build
  lake env lean -DwarningAsError=true Audit.lean
  lake env lean -DwarningAsError=true Conjecture1030/SphereMomentsAudit.lean

The cache command is optional if dependencies are already built. Initial
dependency acquisition requires network access. lean-toolchain pins Lean
4.19.0. lake-manifest.json pins Mathlib v4.19.0 at
c44e0c8ee63ca166450922a373c7409c5d26b00b and every transitive package revision.
Do not run lake update as part of reproducing these pinned results.

The default library imports every mathematical module through Theorem.lean.
Audit.lean queries the measure bridges and main theorem axiom dependencies.
The separate sphere-moment audit also queries the general integration bridge.
The only permitted theorem axioms are propext, Classical.choice, and Quot.sound.

Exact auxiliary computations

From this submission's auxiliary directory:

  python3 check_icosahedron.py

Python 3 with its standard library suffices. The deterministic output and
expected hashes are supplied there. The checker covers all 56 low-degree
monomials, all 66 vertex pairs, supporting facets/edges, and positive and
negative controls. Its README states the precise proof boundary: its target
moments do not replace their independent derivation in Lean.

Stricter independent verification

verification/README.txt describes the frozen-source replay, pinned dependency
identities, declaration-closure audit, and adversarial verification controls.
verification/frozen-sources.json binds all 14 Lean/configuration files. The
complete command receipts and audit data are preserved in the evidence archive;
human-readable local review records are provided beside it.

The independent review here was conducted in a separate AI review context.
It is local validation, not an upstream maintainer review or acceptance.

Rebuild the report

With Tectonic installed, from this submission directory:

  tectonic --keep-logs report.tex

The source is a standalone article using standard LaTeX packages. The submitted
PDF was also compiled with the desktop LaTeX editor and its five rendered pages
were visually inspected. No generated Lean binaries or dependency trees are
part of this submission.
