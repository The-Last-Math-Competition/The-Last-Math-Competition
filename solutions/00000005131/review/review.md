# Solution Review — Conjecture 00000005131 (PR 1080)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022101706`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000005131; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement says an eigenvalue of algebraic multiplicity m shifts by an ε^{1/m}-type power, with the exponent decided by the maximal Jordan block size, and the pseudospectral area scales as ε^{2/m} with a constant containing an explicit power of the condition number. The submission reads m in the displayed powers as the algebraic multiplicity and refutes the necessary sharp lower bounds for the response and area laws.

**Decisive results.** The 2×2 complex zero matrix has characteristic polynomial X² and hence algebraic multiplicity m=2, while its maximal Jordan block has size one. Lean proves the actual pseudospectrum is the closed disk of radius ε for the induced infinity norm, that the worst displacement is exactly ε, and that the area is πε². The sharp multiplicity-based response lower bound would require cε^{1/2}≤ε and the area lower bound cε≤πε² for small ε; both fail. Thus the literal algebraic-multiplicity reading of the filed powers is false. The source also says the exponent is decided by the maximal Jordan block size; the paper discloses that the corrected maximum-block version (and a big-O-only reading) is compatible with the example. The area clause is decisive because its displayed exponent is 2/m with m the algebraic multiplicity introduced in the source.

**Report correspondence.** The report and Lean agree on the exact disk pseudospectrum, the multiplicity two, the area πε², and the negations of the two multiplicity laws. The report explicitly notes that the corrected maximum-Jordan-block version is not refuted and that the condition-number/lattice clauses are not addressed. No stronger prose claim beyond that disclosed scope.

## Disposition

APPROVED — merged as PR 1080. The submission gives a complete, formalised disproof of conjecture 00000005131.
