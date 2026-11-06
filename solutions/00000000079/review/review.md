# Solution Review — Conjecture 00000000079 (PR 1177)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024062649`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000079; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal reading of the parenthetical: every digit block of length ℓ occurs with limiting frequency 1/ℓ. The submission takes base 10 and counts prefixes of the decimal expansion of x_n={α p_n}; it also checks the sliding first-digit stream. It explicitly does not claim to refute the conventional normality statement with frequency 10^{-ℓ}.

**Decisive results.** The theorem negates the literal printed inverse-length rule for every point sequence, hence in particular for the irrational α=√2 with the increasing prime sequence. Two distinct one-digit words are disjoint, so their finite frequencies sum to at most 1 for every N; the printed rule would require both limits to be 1, a contradiction. Thus the printed rule is impossible. The irrationality, prime enumeration, membership in [0,1) and the first-digit cylinder identity are all proved from actual objects.

**Report correspondence.** Report and Lean agree: both prove the finite disjointness bound and the Tendsto contradiction, and both explicitly distinguish the printed 1/ℓ rule from ordinary normality's 10^{-ℓ}. No stronger prose claim is made.

## Disposition

APPROVED — merged as PR 1177. The submission gives a complete, formalised disproof of conjecture 00000000079.
