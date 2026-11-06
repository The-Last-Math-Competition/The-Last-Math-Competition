# Solution Review — Conjecture 00000000259 (PR 1076)

**Submission:** idealistichacker — `idealistichacker_submission_20261022085932`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000259; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.1` and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `reproduce.py` exited 2.

## Semantic audit

**Conjecture as filed.** For primes p ≡ 1 (mod 4), the density of those for which x^2 - p y^2 = -1 is solvable equals 1 - ∏_{k≥2}(1 - 2^{-k}); density is the relative counting density |A_N|/|B_N| with B_N the primes p<N with p≡1 mod 4.

**Decisive results.** The Lean proves the universal prime-radicand fact that every p ≡ 1 mod 4 is negative-Pell solvable, hence A_N = B_N for every N, the ratio is identically 1 for N ≥ 6, and its limit is 1. The claimed constant is proved to lie in [1/4, 7/16] and to be ≠ 1, so the relative-density sequence does not tend to it. This is the literal negation of the density clause under the stated relative-prime-class reading; the hypotheses are satisfiable (5 ∈ B_N).

**Report correspondence.** The report's Theorem 1, counting theorem, and constant-separation theorem match the Lean signatures. The report explicitly states the relative-density interpretation, discloses the denominator, and disclaims the composite-radicand literature version and the introductory wide-class-number clause.

## Disposition

APPROVED — merged as PR 1076. The submission gives a complete, formalised disproof of conjecture 00000000259.
