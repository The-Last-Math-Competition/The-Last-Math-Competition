# Conjecture 00000008331

For every integer-coefficient polynomial P, each exp(2*pi*i*P(n)) equals 1, so the frequency-one Weyl sum is exactly N. The concrete nonconstant cubic P(X)=X^3+X+1 consequently violates O(sqrt N).

## Scope and formal correspondence

Both source languages explicitly quantify over nonconstant integer-coefficient polynomials for P(n) modulo one. No irrational multiplier is present. The submission refutes that stated universal cancellation clause, with a concrete cubic and an eventual Big-O contradiction; it does not assess the separate assertions about quadratic irrational coefficients.

The Lean project uses Polynomial Z, its actual evaluation, Complex.exp, and the finite sum over Finset.range N. Complex exponential periodicity yields every summand and hence the exact complex sum and norm. Evaluations at 0 and 1 show the cubic is not any constant polynomial. The final theorem negates Mathlib Asymptotics.IsBigO at Filter.atTop, including every possible eventual constant and threshold.

## Files and reproduction

- `main.tex` and `main.pdf`: full disproof and Lean correspondence.
- `SOURCE.md`: unchanged bilingual conjecture, byte for byte.
- `lean/`: complete portable project pinned to Lean 4.19.0 and Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b.
- `verification/`: actual build logs, theorem axioms, hashes, native compiler result, source provenance and reviews.

Inside `lean/`, run `lake build`, then `lake env lean -DwarningAsError=true Main.lean`. A new machine can retrieve the official dependency artifacts with `lake exe cache get`. All transitive revisions are pinned in the manifest; there are no private dependencies or local paths. Run `tectonic main.tex` from the submission directory to export the PDF. No auxiliary numerical computation is needed.

The submission's own artifacts are freshly rebuilt without a reused `.lake` directory; only verified official dependency caches are reused. The native desktop LaTeX compiler succeeded on the recorded source. Tectonic produces the distributed PDF, and every rendered page is visually checked. Author self-review and parent-agent review are distinct records; no external independent review is claimed.
