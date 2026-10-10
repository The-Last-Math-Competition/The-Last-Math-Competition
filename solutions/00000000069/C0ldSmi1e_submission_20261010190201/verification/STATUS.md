# Author verification record

The complete mathematical source was first successfully built on 2026-10-10, then frozen for independent review. The author removed all generated outputs for the six authored proof modules, rebuilt them, replayed each source with `-DwarningAsError=true`, replayed `verification/Axioms.lean`, and ran the integrity utility. The complete successful output is `author-verification.log`.

The toolchain reported:

- Lean 4.19.0, arm64-apple-darwin23.6.0, commit `6caaee842e94`, Release.
- Lake 5.0.0-6caaee8.
- Stock Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

Every authored lemma/theorem's printed axiom dependency set is exactly `[propext, Classical.choice, Quot.sound]`. The final disproof theorem, genuine L¹ error identity, and degree-constrained infimum bound are included. No authored proof token `sorry`, `admit`, `native_decide`, or `axiom` was found. The exact-input hash inventory passed.

After the successful run, the root manifest's package name was normalized from the inherited `tlmc_neutral` to `tlmc69`; all package pins remained unchanged. The original manifest remains untouched under `source/`. The mathematical Lean sources were not changed. A final metadata build check is recorded in `final-metadata-build.log`.

The frozen theorem disproves the necessary L¹ rate clause as written, using unweighted Lebesgue measure, all real polynomials of degree at most n, and ordinary nonzero ratio asymptotic equivalence. It does not claim a sharp global rate, an optimal numerical constant, or a solution to the uniform-norm Bernstein-constant problem.

`report.tex` is the complete author LaTeX report. Parent is responsible for its native-editor compilation, PDF export, visual review, independent semantic/build audits, eligibility, and any publication. Those outcomes are not asserted by this author record. A successful formal proof is not competition acceptance.
