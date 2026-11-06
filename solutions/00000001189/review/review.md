# Solution Review — Conjecture 00000001189 (PR 1141)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023044001`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001189; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal definition: the minimal support of a two-element-generated representation of SL_n(F_q) is the minimum, over generating pairs, of the dimension of the fixed-point space of the image in the natural n-dimensional representation. The conjecture asserts that a pair with common fixed space 0 and individual fixed spaces at most one line 'gives support n²−1'. The submission reads this literally at the legitimate parameters n=2, q=2, where n²−1=3.

**Decisive results.** Lean works with the actual group SL_2(F_2) and its genuine natural action on F_2^2. It defines fixed A = ker(A−I), commonFixed A B = fixed A ⊓ fixed B, and the generated subgroup closure. It proves commonFixed A B = imageFixed(⟨A,B⟩), so the source's 'fixed space of the image' is the common fixed space. The explicit transvections U and L are proved to generate the whole group; U fixes exactly {y=0}, L fixes exactly {x=0}, and their common fixed space is ⊥. Thus there is a genuine generating pair with common fixed dimension 0 and individual fixed dimensions ≤1, so 0 is in the actual support-value set and is its least element. The actual minimum is therefore 0, not 2²−1=3. The existence half of the source's conjunction is true, while the numerical 'giving support n²−1' half is false, so the literal conjunction is refuted at n=2,q=2. If the source is read universally over n,q, this is a counterexample; the report states that reading explicitly.

**Report correspondence.** The report matches Lean: actual SL_2(F_2), fixed subspaces, the U/L generating pair, common fixed space 0, least support 0, and support_formula_false. The report also treats the alternative reading over nonempty families of image subgroups via any_image_minimum_le_two. It explicitly says it does not reinterpret support as a codimension or adjoint invariant. No stronger prose claim than the formal statements.

## Disposition

APPROVED — merged as PR 1141. The submission gives a complete, formalised disproof of conjecture 00000001189.
