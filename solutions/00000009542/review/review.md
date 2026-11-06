# Solution Review — Conjecture 00000009542 (PR 1096)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022111228`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000009542; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `verify.py` exited 0.

## Semantic audit

**Conjecture as filed.** Literal: the entanglement-assisted capacity of a finite composite quantum set {φ_i} is the min-max formula min_i max_ρ I(ρ,φ_i). The submission reads capacity as the operational compound EA capacity and uses the standard coding theorem C_EA(W)=sup_ρ inf_i I(ρ,φ_i) (Boche–Janßen–Kaltenstadler, Theorem 3.1, eq. (7)).

**Decisive results.** The three qutrit-to-bit channels Φ_i(X)=diag(X_ii,tr X-X_ii) are genuine CPTP maps. The Lean proves the actual entropy-exchange mutual information, the pinching bound I(ρ,Φ_i)≤h(p_i), the exact individual optima max_ρ I(ρ,Φ_i)=log 2, and the common-input value sup_ρ min_i I(ρ,Φ_i)=h(1/3). Since h(1/3)<log 2, sup_ρ min_i I < min_i sup_ρ I. The cited compound EA coding theorem identifies the left side with the operational capacity, so the proposed min-max formula is false. The hypotheses (finite set of genuine channels) are satisfiable; the conclusion is the negation of the capacity formula.

**Report correspondence.** The report's channel construction, entropy-exchange formula, pinching/Jensen bound, exact h(1/3) and log 2 values and the strict gap match the Lean. The report explicitly says the operational coding theorem and the purification identification are cited mathematical background, not formalized in Lean; the Lean formalizes the single-letter gap. The supplementary verify.py ran and passed.

## Disposition

APPROVED — merged as PR 1096. The submission gives a complete, formalised disproof of conjecture 00000009542.
