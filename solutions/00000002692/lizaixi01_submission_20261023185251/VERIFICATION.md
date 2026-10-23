# Verification

The exact frozen source passed a new pinned Lean 4.33.0 root build. Mathlib commit db584cd6d46c92f209a44c0f1c829460d327499d and all dependency revisions are fixed in the manifest.

- Version check, new root build, warning-as-error all-named axiom audit, and full official fresh kernel replay: all exit 0.
- All 42 named declarations (32 theorems, 7 definitions, 2 abbreviations, 1 prime instance) are audited. Only propext, Classical.choice, Quot.sound or no axioms.
- Full fresh kernel replay: 573.1771 diagnostic WSL seconds. This is an official kernel replay, not a separate kernel implementation.
- Both PDF pages rendered at 100 dpi and visually inspected by the worker and separate supervising AI. No clipping, overlap or LaTeX overflow warnings.
- Exact source, full mathematical scope and report independently reviewed by the supervising AI.

Main SHA256: `a2c89b638cdaf8df257cfb3328f6d1999c6e991ebed00867fddf59d334d92355`. Source, exact commands, exits and log hashes are bound in verification.json. The full execution job, result, and all actual thread-affinity samples are included. Every observed thread mask is [0,2]; no owned residuals remained. Selective production, not an additional controlled experiment or an efficiency claim.

The actual polynomial f(x)=5*x on Q5 and Z5 has nonzero derivative and is a strict contraction. The inclusive convergence basin at0 is the entire phase space. The complete periodic set is {0}, while the true relative frontier is empty. The Z5 basin image in Q5 is the actual closed unit ball and has empty ambient frontier too. Only the necessary boundary clause is refuted. The arbitrary-measure lemma is the genuine equality mu(basin)=mu(univ), and no multiplicative order is assigned to0mod5. Full original bilingual source preserved. Prior closed PR276 and its actual rejecting review are included and fully explained; organizer acceptance remains pending.
