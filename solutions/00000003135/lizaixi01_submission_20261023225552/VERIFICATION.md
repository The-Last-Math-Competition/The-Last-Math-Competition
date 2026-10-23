# Verification

The exact frozen source passed a new pinned Lean 4.33.0 root build. Mathlib commit db584cd6d46c92f209a44c0f1c829460d327499d and all dependency revisions are fixed in the manifest.

- Version check, new root build, warning-as-error all-named axiom audit, and full official fresh kernel replay: all exit 0.
- All 89 namespace declarations are audited: 51 explicit declarations (23 theorems, 11 definitions, 7 abbreviations, 9 instances and 1 structure), plus generated constructors, projections, recursors and auxiliaries. Imported namespace coverage is checked exactly. The frozen audit intentionally disables only the auxiliary-name stability lint; all proof warnings remain errors. Only propext, Classical.choice, Quot.sound or no axioms.
- Full fresh kernel replay: 422.4215 diagnostic WSL seconds. This is an official kernel replay, not a separate kernel implementation.
- Both PDF pages rendered at 100 dpi and visually inspected by the worker and separate supervising AI. No clipping, overlap or LaTeX overflow warnings.
- Exact source, full mathematical scope and report independently reviewed by the supervising AI.

Main SHA256: `0993b72ad88a5a3094c2f95807077549b1f0e2a2dd5b3d056f7d212653f53478`. Source, exact commands, exits and log hashes are bound in verification.json. The full execution job, result, and all actual thread-affinity samples are included. Every observed thread mask is [0,2]; no owned residuals remained. Selective production, not an additional controlled experiment or an efficiency claim.

The actual finite discreteC2 is a zero-dimensional smooth real Lie group. Its GroupLieAlgebra, standard LieAlgebra structure, genuine conjugation derivative and coadjoint action yield a nonempty subsingleton orbit quotient. The full quotient of continuous irreducible unitary representations on nonzero complex Hilbert spaces contains two distinct classes, trivial and sign, with every heterogeneous unitary intertwiner accounted for. This excludes a bijection under the literal unrestricted nilpotent Lie-group reading. The connected simply connected theorem, finite-field Lie-ring orbit method and undefined extra measure assertion are not claimed refuted. Full original bilingual source preserved. No earlier same-ID submission found; organizer acceptance remains pending.
