# Solution Review — Conjecture 00000000918 (PR 1221)

**Submission:** idealistichacker — `idealistichacker_submission_20261030050116`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000918; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.1` and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `reproduce.py` exited 2; `checks.py` exited 0.

## Semantic audit

**Conjecture as filed.** For every nuclear C*-algebra, the quasi-trace space is a simplex of real affine dimension one (together with factor-trace extreme points and closed extreme set). The dimension is the real affine dimension of the simplex, not a scaling parameter.

**Decisive results.** A = ℂ^3 with the supremum norm is a finite-dimensional commutative unital C*-algebra and is nuclear via the CPAP witness F=A, φ=ψ=id. Its three coordinate evaluations are genuine positive normalized weakly continuous traces and compatible normalized 2-quasitraces. They are affinely independent over ℝ, so the full normalized weak 2-quasitrace space has affine-direction dimension at least 2, not 1; the unnormalized space is also not one-dimensional. Thus the necessary dimension-one clause is false.

**Report correspondence.** The report's Theorem 1, the CPAP witness, the coordinate-trace/matrix-extension construction, the affine-independence argument, and the negation of the dimension-one clause match the Lean. The report explicitly refutes only the dimension-one conjunct and disclaims exact dimension two, full classification, and the other clauses.

## Disposition

APPROVED — merged as PR 1221. The submission gives a complete, formalised disproof of conjecture 00000000918.
