# Verification

The exact frozen source passed a new pinned Lean 4.33.0 root build. Mathlib commit db584cd6d46c92f209a44c0f1c829460d327499d and all dependency revisions are fixed in the manifest.

- Version check, new root build, warning-as-error all-namespace axiom audit, and full official fresh kernel replay: all exit 0.
- All 34 namespace declarations are audited: 28 explicit declarations (20 theorems, 6 definitions, 1 abbreviation and 1 instance), plus generated equations and auxiliaries. Imported namespace coverage is checked exactly. Only the auxiliary-name stability lint is disabled for this frozen exhaustive audit. Allowed axioms are propext, Classical.choice and Quot.sound.
- Full fresh kernel replay: 503.2892 diagnostic WSL seconds. This uses the official checker, not a separate kernel implementation.
- Both PDF pages were rendered at 100 dpi and visually inspected by the worker and independently by the supervising AI, with no clipping, overlap or LaTeX overflow warnings.
- The supervising AI independently reviewed the full source, report and exact mathematical scope.

Main SHA256: `035981bce1cb0e9241be2cccd42d6aa996bb05f3d85e1592161e25dabbd517de`. Exact commands, exits and log hashes are bound in verification.json. The original full execution job, result and every actual thread-affinity sample are included. All 933 observed thread masks are [0,2]; no owned residual processes remained. This is selective production, not a controlled experiment or an efficiency claim.

The proof uses the actual field Q5 and the continuous linear maps f=g=-id. It proves both inverse identities and a genuine homeomorphism, the native inverse power-series representation with infinite radius, and the strict derivative -1 with nonzero value and norm1. Actual powers of5 give nonzero points in every positive-radius ball. Their full inverse-iteration orbits stay in that ball; actual cofinal even and odd subsequences are the distinct constants x and -x, so the full sequence has no limit in Q5. No numerical radius, norm or rate is assigned by definition. Only the unconditional inverse-iteration convergence clause is refuted; no claim is made against the inverse function theorem or a contraction theorem with its attracting hypotheses. Full original bilingual source is preserved. No earlier same-ID submission was found; organizer acceptance remains pending.
