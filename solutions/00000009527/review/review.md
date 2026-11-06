# Solution Review — Conjecture 00000009527 (PR 1063)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261020023025`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000009527; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `verify.py` exited 0.

## Semantic audit

**Conjecture as filed.** The source defines φ ⪯_ln ψ by I(ensemble;φ)≤I(ensemble;ψ) for all ensembles and claims, among other things, that the less-noisy order is a closed partial order whose unique maximal element is the completely depolarizing channel. The submission reads 'unique maximal element' literally and tests the qubit channels D(A)=tr(A)I/2 and Z(A)=diag(A).

**Decisive results.** Lean proves D and Z are genuine CPTP maps via explicit normalized Kraus families. For every finite ensemble of actual complex density matrices, χ(E;D)=0 and χ(E;Z)≥0 (spectral diagonal entropy plus scalar Jensen), so D⪯Z. The orthogonal pure-state ensemble has χ(Z)=log2>0=χ(D), so Z⋠D. Thus D has a strict successor and is not maximal, let alone the unique maximal element. A second theorem exhibits two distinct reset channels equivalent in both directions, refuting antisymmetry on literal channel space. The capacity-formula conjunct is not needed once the maximal-element conjunct is false.

**Report correspondence.** The report proves the same D⪯Z and Z⋠D comparison and the same reset-channel antisymmetry example. The report's extra phrase 'even after quotienting by mutual less-noisy equivalence' is an immediate corollary of the strict comparison (if [D]=[Z] then Z⪯D), not an independently stronger claim.

## Disposition

APPROVED — merged as PR 1063. The submission gives a complete, formalised disproof of conjecture 00000009527.
