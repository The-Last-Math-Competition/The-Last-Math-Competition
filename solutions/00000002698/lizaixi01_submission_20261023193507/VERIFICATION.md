# Verification

The exact frozen source passed a new pinned Lean 4.33.0 root build. Mathlib commit db584cd6d46c92f209a44c0f1c829460d327499d and all dependency revisions are fixed in the manifest.

- Version check, new root build, warning-as-error all-named axiom audit, and full official fresh kernel replay: all exit 0.
- All 51 named declarations (38 theorems, 9 definitions, 3 abbreviations, 1 instance) are audited. Only propext, Classical.choice, Quot.sound or no axioms.
- Full fresh kernel replay: 281.5175 diagnostic WSL seconds. This is an official kernel replay, not a separate kernel implementation.
- Both PDF pages rendered at 100 dpi and visually inspected by the worker and separate supervising AI. No clipping, overlap or LaTeX overflow warnings.
- Exact source, full mathematical scope and report independently reviewed by the supervising AI.

Main SHA256: `c24fb2b2bd22583d512518012b9586f953ea77f56ae491b011d6b9a31517dec0`. Source, exact commands, exits and log hashes are bound in verification.json. The full execution job, result, and all actual thread-affinity samples are included. Every observed thread mask is [0,2]; no owned residuals remained. Selective production, not an additional controlled experiment or an efficiency claim.

The actual polynomial X+1 over Q5 has no classical positive-period points, and a generic characteristic-zero theorem covers classical extension points. Its coefficientwise tropicalization is built with the genuine extended additive valuation and evaluates to min(w,0). The value -1 is attained by 1/5 and is a tropical fixed point. Each positive composed polynomial X+n is proved to have the same discrepancy. Support, coefficients, derivative1, two-sided inverse and strict no-cancellation branch are proved. The scope is standard coefficientwise min-plus tropicalization and classical points; no Berkovich-point claim or definition of the source's unspecified ramification layer or log(p) height is supplied. Full original bilingual source preserved. No earlier same-ID submission found; organizer acceptance remains pending.
