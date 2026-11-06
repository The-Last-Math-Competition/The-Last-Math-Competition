# Conjecture 00000002473: rank and crank disagree outside the exceptional classes

The English necessary clause says “the two statistics agree outside the exceptional classes.” At n=2, none of the Ramanujan size classes 5a+4, 7a+5 or 11a+6 applies. The two actual partitions have rank/crank values (1,2) for (2), and (-1,-2) for (1,1). Thus the statistics disagree pointwise, their full integer distributions differ, and their distributions modulo5,7,11 differ at residue1. The vague near-bijective refinement is unnecessary for refuting this necessary clause. The unclear Chinese wording is preserved in SOURCE.md; the counterexample concerns the clear English assertion.

Lean uses actual Mathlib Nat.Partition objects, defines the standard statistics from their parts, and proves that its two named objects exhaust Nat.Partition2. Distribution counts are filters of the full finite universe. They do not assume a test list is exhaustive. Both subtractions take place in Z, preserving negative ranks/cranks. Three final theorems negate the pointwise, full-distribution and modular-distribution universal agreement claims.

[Bringmann–Mahlburg–Rhoades, equations1.2–1.3](https://www.mi.uni-koeln.de/Bringmann/BMRFinalPublication.pdf) gives the standard definitions and the Ramanujan classes. The special n=1 generating-function convention does not affect this actual n=2 partition example. This does not refute Ramanujan's congruences or the established rank/crank theory.

## Reproduce

With elan installed, enter `lean/` and run:

```sh
lake exe cache get
bash verify.sh
```

Lean4.33.0, Mathlib db584cd6d46c92f209a44c0f1c829460d327499d and all dependencies are pinned. The source is newly built, sixteen key declarations are audited, and the official `leanchecker --fresh Main` replays the proof. Complete LaTeX source, visually checked two-page PDF, receipts/logs and exact hashes accompany the submission. No sorry, native_decide or added axiom. OpenAI Codex assisted; a separate supervising Codex agent reviewed the source and report. This is AI review, not human certification. Organizer acceptance is pending.
