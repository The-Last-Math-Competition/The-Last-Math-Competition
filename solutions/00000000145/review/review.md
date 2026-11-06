# Solution Review — Conjecture 00000000145 (PR 1154)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023083235`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000145; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The printed LIL claim has no irrationality, Diophantine or almost-everywhere restriction on α; it asserts Ω± fluctuations at scale sqrt(x log log x / log x) for every admissible f with nonzero deviation from its mean. The submission takes the literal unrestricted-α reading and uses α=1.

**Decisive results.** Take α=1 and f(t)=sin(2πt). Lean proves f is smooth, 1-periodic, has interval mean 0, variance 1/2, and a point t=1/4 with f(t)≠0, so it has nonzero deviation. For every natural p (hence every prime), {1·p}=0 and f(0)=0; the actual filtered prime sum is identically 0. The scale is strictly positive for x≥e². `OmegaPlus` requires cofinally many x with c·scale(x)≤centeredSum(x); with centeredSum=0 this is impossible, and the same for Ω-. `literal_unrestricted_claim_false` negates the ∀α claim. The counterexample α=1 is a positive real in the literal parameter domain and satisfies every stated hypothesis on f.

**Report correspondence.** The report and Lean agree: the report states the prime set, mean, variance, actual sampled sum, exact scale, both Omega signs, the zero-sum computation, and the unrestricted-α negation. `mem_primesUpTo`, `sine_mean`, `sine_variance`, `centered_sine_zero`, `scale_pos`, `zero_not_omega_plus` and `literal_unrestricted_claim_false` formalize those claims. The report explicitly says it does not refute a corrected irrational-α or almost-everywhere version.

## Disposition

APPROVED — merged as PR 1154. The submission gives a complete, formalised disproof of conjecture 00000000145.
