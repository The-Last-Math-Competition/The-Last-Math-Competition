# Verification

The exact frozen source passed a new pinned Lean 4.33.0 root build. Mathlib commit db584cd6d46c92f209a44c0f1c829460d327499d and all dependency revisions are fixed in the manifest.

- Version check, new root build, warning-as-error all-namespace axiom audit, and full official fresh kernel replay: all exit 0.
- All 46 namespace declarations are audited: 34 explicit declarations (26 theorems and 8 definitions), plus generated equations and auxiliaries. Imported namespace coverage is checked exactly. Only the auxiliary-name stability lint is disabled for this frozen exhaustive audit. Allowed axioms are propext, Classical.choice and Quot.sound.
- Full fresh kernel replay: 619.9080 diagnostic WSL seconds. This uses the official checker, not a separate kernel implementation.
- Both PDF pages were rendered at 100 dpi and visually inspected by the worker and independently by the supervising AI, with no clipping, overlap or LaTeX overflow warnings.
- The supervising AI independently reviewed the full source, report and exact mathematical scope.

Main SHA256: `02a5bf92c0ab03d614aeb69a6b931dcfd48ddffa8ecf8de5271601f51882836b`. Exact commands, exits and log hashes are bound in verification.json. The original full execution job, result and every actual thread-affinity sample are included. All 1137 observed thread masks are [0,2]; no owned residual processes remained. This is selective production, not a controlled experiment or an efficiency claim.

The proof uses the actual rational polynomial X^2 of degree2 and the nonpreperiodic point2. It evaluates all true iterates and the native logarithmic and multiplicative Weil heights defined from all absolute values. The canonical height is obtained from its true degree-normalized limit, whose convergence and finite value are proved. Genuine finite sums show that the ordinary orbit means of both height conventions tend to infinity and cannot converge to any finite real number. The lower-bound argument uses positive indices and does not depend on a zero-denominator value. Only ordinary unnormalized mean-height convergence is refuted. No Fourier coefficients or orbit-frequency measure are assigned, and no claim is made against a differently normalized mean or canonical-height and equidistribution theorems under their hypotheses. Full original bilingual source is preserved. No earlier same-ID submission was found; organizer acceptance remains pending.
