# Verification

The exact frozen source passed a new pinned Lean 4.33.0 root build. Dependency commits are fixed by the manifest.

- Version check, fresh root build, warning-as-error all-named axiom audit, and full official fresh kernel replay: all exit 0.
- All 58 named declarations (43 theorems and 15 definitions), including every matrix and optimization definition, are audited. Only propext, Classical.choice, Quot.sound or no axioms.
- Full fresh kernel replay: 568.7175 diagnostic WSL seconds. Official kernel replay, not an independent kernel implementation.
- Both PDF pages rendered at 100 dpi and inspected by worker and supervising AI; no overflow or clipping.
- Exact source, full mathematical scope and report independently reviewed by the supervising AI.

Main SHA256: `217cef206cae3b7c752747db3a6199248fec32bb2dadf82a50d903060b6e2d8f`. Source, commands, exits, logs and cleanup are bound in the receipt. CPU affinity 0,2, one owned heavy process group, no owned residuals. Selective production, not an additional controlled experiment or an efficiency claim.

The actual input is X^3>=0,1-X^2>=0 with compact K=[0,1]. All finite legal orders have genuine PSD moment and localizing matrices with a negative first moment, from explicit positive atomic functionals. The exact quadratic-form/polynomial bridge and monomial matrix entries are proved. Actual evaluation functionals put all of K inside the projected relaxation, which strictly contains K. Real infimum and SOS supremum are nonempty, bounded and strictly below the true minimum0. The SOS lower certificate gamma=-1 and weak duality are formalized; no attainment or strong duality assumption. This only refutes finite exactness of the hierarchy built from the supplied generators, not existence of another SDP representation of [0,1]. Original bilingual source preserved; no earlier same-ID submission found. Organizer acceptance pending.
