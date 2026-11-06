# Solution Review — Conjecture 00000000644 (PR 1132)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023030741`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000644; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement requires that at real parameter points all eigenvalues of the Burau representation have real part ≥−1/2 (and calls this positivity). The submission reads this as the standard reduced and unreduced Burau representations of the three-strand braid group B3 over ℂ, at any legal nonzero real t, and refutes the universal spectral bound.

**Decisive results.** Lean constructs the genuine Artin presentation B3=⟨σ1,σ2 | σ1σ2σ1=σ2σ1σ2⟩, the standard reduced matrices A(t)=[[−t,1],[0,1]], B(t)=[[1,0],[t,−t]], and the standard unreduced blocks, proves the braid relations and determinants, and builds actual group homomorphisms to GL2(ℂ) and GL3(ℂ). At t=3/4 (real, nonzero, 0<t<1), σ1 has the eigenvalue −3/4 with real part −3/4<−1/2; `conjugate_eigenvalue` transports this to every invertible basis change. Hence the universal real-specialization spectral claim is false, in both reduced and unreduced versions. The hypotheses are satisfiable and the conclusion is the direct negation.

**Report correspondence.** The report/PDF state the same standard matrices, the same t=3/4 and eigenvalue −3/4, and the same all-bases and reduced/unreduced negations; the Lean theorems match. The report explicitly says it does not claim to refute mere trace positivity or the LKB/Floer/volume models.

## Disposition

APPROVED — merged as PR 1132. The submission gives a complete, formalised disproof of conjecture 00000000644.
