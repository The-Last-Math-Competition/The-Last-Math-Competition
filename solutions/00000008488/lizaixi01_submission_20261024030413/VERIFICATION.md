# Verification

The exact frozen source passed a new pinned Lean 4.33.0 root build. Mathlib commit db584cd6d46c92f209a44c0f1c829460d327499d and all dependency revisions are fixed in the manifest.

- Version check, new root build, warning-as-error all-namespace axiom audit, and full official fresh kernel replay: all exit 0.
- All 59 namespace declarations are audited: 40 explicit declarations (25 theorems, 8 definitions, 2 abbreviations and 5 instances), plus generated equations and auxiliaries. Imported namespace coverage is checked exactly. Only the auxiliary-name stability lint is disabled for this frozen exhaustive audit. Allowed axioms are propext, Classical.choice and Quot.sound.
- Full fresh kernel replay: 497.0275 diagnostic WSL seconds. This uses the official checker, not a separate kernel implementation.
- Both PDF pages were rendered at 100 dpi and visually inspected by the worker and independently by the supervising AI, with no clipping, overlap or LaTeX overflow warnings.
- The supervising AI independently reviewed the full source, report and exact mathematical scope.

Main SHA256: `5a5899064f5eb56c8ebb3eceedad69b23067546e2a9ce21212cb5542f3187c42`. Exact commands, exits and log hashes are bound in verification.json. The original full execution job, result and every actual thread-affinity sample are included. All 945 observed thread masks are [0,2]; no owned residual processes remained. This is selective production, not a controlled experiment or an efficiency claim.

The proof constructs the actual closed compact subshift of one-sided binary sequences with at most one1, the continuous left shift, and a cofinal family of metric entourages. Actual finite covers and separated sets prove the native coverMincard at the first-coordinate entourage is n+1, and uniform linear cover bounds at all prefix scales prove the full native coverEntropy is zero. The finite-time values therefore converge to zero but violate every eventual C/n bound, with all C and starting N quantified. No entropy or counting value is assigned by definition. Only the explicitly interpreted orbit-length harmonic-rate clause is refuted; classical equivalence of entropy definitions and the unspecified boundary/periodicity clauses are not disputed. Full original bilingual source is preserved. No earlier same-ID submission was found; organizer acceptance remains pending.
