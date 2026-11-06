# Solution Review — Conjecture 00000001785 (PR 1143)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023050733`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001785; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal: the optimal constant is an explicit step function of c with C(c)=max(1,2c)·π (with a transition at c=1/2). The submission reads 'step function' in the standard sense: a finite linear combination of indicators of intervals, and separately the more permissive countable disjoint-interval representation with constant pieces.

**Decisive results.** Lean defines positiveWindow=(1/2,1) and printedFormula c=max(1,2c)π. On this window max(1,2c)=2c, so printedFormula c=2cπ, which is injective; the window is uncountable, so the image is uncountable. A finite interval-step function has finite image (the membership pattern lies in the finite type {0,1}^n), and a countable interval-constant representation has countable image. Therefore no function C can be both a finite (or countable) interval step function on the window and equal the printed formula there. This is exactly the source's literal 'step function plus formula' conjunction, and it is false for every C. The hypothesis is satisfiable in the sense that the formula itself is a well-defined real function; the impossibility is the claimed incompatibility.

**Report correspondence.** The report matches Lean: finite and countable interval-step predicates, the finite/countable image bridges, formula_on_positive_window, formula_injective_on_window, formula_image_uncountable, and the two impossibility theorems. The report explicitly says it does not compute an Ohsawa–Takegoshi optimum, does not refute an independent extension theorem, and does not infer a jump from the word 'transition' alone. No stronger prose claim.

## Disposition

APPROVED — merged as PR 1143. The submission gives a complete, formalised disproof of conjecture 00000001785.
