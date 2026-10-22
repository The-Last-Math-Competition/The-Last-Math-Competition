# Conjecture 00000001294: inverse-tree growth

This submission refutes the claimed O((sqrt(4/3))^n) bound for the standard finite-depth unfolded Collatz inverse tree rooted at 1. Both the full odd step 3n+1 and the shortcut odd step (3n+1)/2 are formalized. Leaves mean frontier nodes at the specified depth; cyclic-root labels may recur at different levels, as explicitly permitted in Applegate and Lagarias, Section 2, pp. 4-5.

Every positive integer not divisible by 3 has three distinct genuine seven-step preimages of the same kind. An actual recursive injection from words of length m into the true finite fiber proves cardinality at least 3^m at depth 7m. Forward invariance of positive nonmultiples of 3 verifies the actual pruned path condition. The proof gives full negations of Mathlib's Asymptotics.IsBigO, for pruned and unpruned counts and both normalizations. It does not assume the Collatz conjecture or claim a result for a first-hit cycle-deleted convention.

- `report.tex`, `report.pdf`: complete proof and convention disclosure.
- `lean/`: pinned Lean 4.33.0 / Mathlib project, Main and 25 transitive theorem axiom audits.
- `SOURCE.md`: original problem at the recorded upstream commit.
- `evidence/`, `VERIFICATION.md`, `SHA256SUMS.json`: source-bound new build, axiom audit, full fresh kernel replay, eligibility and review records.

Primary definition: D. Applegate and J. C. Lagarias, *Density Bounds for the 3x+1 Problem I. Tree-Search Method* (December 15, 1993), equation (1.1), Section 2, pp. 4-5, and equation (2.1): https://websites.umich.edu/~lagarias/doc/applegateI.pdf . The worker and separate supervisor directly read these pages. The primary uses the shortcut map; this package also covers the full odd-step normalization.

OpenAI Codex assisted; a separate supervising Codex agent reviewed the source, report and rendered PDF. This is AI review, not human certification. Organizer acceptance is pending.
