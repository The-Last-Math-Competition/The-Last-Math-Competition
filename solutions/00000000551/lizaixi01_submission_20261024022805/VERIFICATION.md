# Verification

The exact frozen source passed a new pinned Lean 4.33.0 root build. Mathlib commit db584cd6d46c92f209a44c0f1c829460d327499d and all dependency revisions are fixed in the manifest.

- Version check, new root build, warning-as-error all-namespace axiom audit, and full official fresh kernel replay: all exit 0.
- All 241 namespace declarations are audited: 101 explicit declarations (44 theorems, 28 definitions, 9 abbreviations, 18 instances and 2 structures), plus generated constructors, projections, recursors and auxiliaries. Imported namespace coverage is checked exactly. Only the auxiliary-name stability lint is disabled for this frozen exhaustive audit. Allowed axioms are propext, Classical.choice and Quot.sound.
- Full fresh kernel replay: 1688.3089 diagnostic WSL seconds. This uses the official checker; it is not a separate kernel implementation.
- Both PDF pages were rendered at 100 dpi and visually inspected by the worker and independently by the supervising AI, with no clipping, overlap or LaTeX overflow warnings.
- The supervising AI independently reviewed the complete mathematical source, report and scope.

Main SHA256: `b11c7c1e3627eb5308338ef354a47d1383dfbe6225eca2f1694580fc8992be5a`. Exact commands, exits and log hashes are bound in verification.json. The original full execution job, result, and every actual thread-affinity sample are included. All 3189 observed thread masks are [0,2]; no owned residual processes remained. This is selective production, not an additional controlled experiment or an efficiency claim.

The construction is the actual complex path algebra of the linearly oriented four-vertex quiver modulo every length-two path. The full path basis, concatenation law, exact relation ideal, quotient equivalence and special biserial conditions are checked. A finitely generated simple module has native Ext-based projective dimension 3 by explicit projective retracts, three short exact sequences and a nonsplitting obstruction. The genuine supremum defining little finitistic dimension therefore contains 3. This refutes the stated unrestricted universal bound 2; it does not assert a classification, a replacement universal upper bound or a result confined to cyclic string algebras. Full original bilingual source is preserved. No earlier same-ID submission was found; organizer acceptance remains pending.
