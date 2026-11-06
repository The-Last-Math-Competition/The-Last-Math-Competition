# Solution Review — Conjecture 00000005501 (PR 1083)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022103119`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000005501; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement says that near the stability boundary the queue length of an open Markovian network with exponential service scales as the negative one-half power of the load deficit δ=1−ρ, with exponent given by the bottleneck branching structure and consistent with heavy-traffic diffusion, and the prefactor is the load redistribution coefficient. The submission uses a single stationary M/M/1 queue, which is an open Markovian network with exponential service.

**Decisive results.** Lean constructs the actual uniformized M/M/1 transition PMF, proves the geometric stationary law and its all-time stationarity, and proves the genuine mean E[N]=ρ/(1−ρ) against the actual measure. Along ρ_k=1−(k+2)^{-2}, the normalized mean √δ E[N]=a_k−1/a_k diverges, and for every fixed integer M the actual cutoff probability P(N≤M a_k) tends to zero; the waiting-only pushforward has the same obstruction. Thus the stationary queue length escapes to infinity on the proposed δ^{-1/2} scale and cannot have a finite half-power stationary scaling law. The single station is a valid instance of the source's broad 'open network' definition; the paper covers both queue-length conventions and explicitly does not claim a centered fluctuation law. The filed half-power claim is falsified for the actual stationary queue length.

**Report correspondence.** The report and Lean agree: the report proves the M/M/1 generator, stationarity, mean ρ/(1−ρ), the diverging normalized mean, and the vanishing cutoff probabilities for both total and waiting-only queue lengths. The report explicitly scopes itself to stationary queue lengths and not centered fluctuations or transient diffusions. The Lean does not formalize a holding-time path construction, but the paper says so; the uniformization construction and generator entries are formalized.

## Disposition

APPROVED — merged as PR 1083. The submission gives a complete, formalised disproof of conjecture 00000005501.
