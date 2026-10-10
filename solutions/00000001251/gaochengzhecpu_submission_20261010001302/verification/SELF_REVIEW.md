# Author self-review: conjecture 00000001251

Main.lean SHA-256: `b840c67d66d99a4ff6489febfdc556315391535e9041a187045acd3d874677e5`

main.tex SHA-256: `d3aa9914b7d062b6ae8754d37c496fb8a1410fc1687c7ff030d8699c30f94718`

SOURCE.md SHA-256: `cf780e6dd2045e341b12579327a45dee5f0fa239dd4d3b74c5cf9116a6bef5b4`

1. The state space has three sites and occupation values 0,1,2, so capacity two and the three-point scope are both genuine.
2. Moves is the actual decrease-one/increase-one rule with positive source, unfilled destination, and every unaffected site unchanged; it is not an arbitrary state permutation.
3. Both the partial-exclusion rates eta_i(2-eta_j) and the unit-rate legal-jump convention are defined on the same moves and verified separately.
4. The binomial and uniform laws assign positive mass to every one of the 27 states. At least one nontrivial particle jump is explicitly evaluated.
5. Both matrices have nonnegative off-diagonal entries and zero row sums, and the actual finite stationarity equations are checked. Detailed balance is not merely asserted in prose.
6. Actual Mathlib PMFs are constructed, and their toReal probabilities satisfy the corresponding generator equations. Product formulas and actual binomial marginals are verified.
7. The three-site raw factorization deficit is computed as zero. Full independence additionally implies vanishing mixed connected correlations.
8. The laws mix conserved particle-number sectors, as grand-canonical product laws do; no ergodicity or fixed-total hypothesis is in the source.

Formal and document verification: PASS. The final Lean sources passed fresh `lake build` and direct `lean -DwarningAsError=true Main.lean`. Only standard logical axioms occur. The final LaTeX source compiled successfully in the desktop compiler and Tectonic, and the final two-page PDF has zero TeX warnings. Both final rendered pages were visually inspected and passed. Exact source hashes and command evidence are in BUILD.json; PDF_REVIEW.json binds the page inspection to the final PDF and TeX hashes.
This is an author scope review, not an external review certificate.
