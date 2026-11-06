# Solution Review — Conjecture 00000009634 (PR 1077)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022100550`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000009634; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `verify.py` exited 0.

## Semantic audit

**Conjecture as filed.** The source claims that the minimal hidden-state count of a sofic shift's output process equals the rank of its Hankel matrix (and is learnable in polynomial time from words of length 2n+1), with rank-deficit-one realizations forming an isolated family. The submission reads 'minimal hidden-state count' as the least number of states in a nonnegative HMM realizing the process, and 'Hankel rank' as the real rank of the all-finite-word probability matrix H_{u,v}=p(uv).

**Decisive results.** Lean defines a general finite nonnegative HMM (initial distribution and symbol-transition matrices) and the all-word Hankel matrix. For the explicit stationary four-state/four-symbol process P=1/2·(cycle with self-loops), it proves the full Hankel rank is exactly 3: a factorization through three columns gives rank≤3, and the 3×3 minor on words [0],[1],[2] has determinant 1/512, giving rank≥3. It also proves every nonnegative HMM realization needs at least four states: the length-two block has positive diagonal entries and H_{ij}H_{ji}=0 for i≠j, and a nonnegative factorization of that block forces an injection from the four symbols into the hidden states. The model itself is a four-state realization, so the minimal hidden-state count is exactly 4. Its positive-probability language has a finite labelled-graph presentation, so it is a sofic-shift output process. Thus 4≠3 refutes the filed equality.

**Report correspondence.** The report and Lean agree: the same process, the same full-rank-3 factorization and minor, the same nonnegative-factorization lower bound and the same four-state witness. The report's main theorem also calls the process stationary; stationarity is proved in the separate theorems `initial_stationary`, `stationary_left_consistency` and `stationary_right_consistency` rather than bundled into `counterexample`. The finite labelled presentation is formalized as `HasFiniteLabelledPresentation`; the report explains the bi-infinite sofic-shift extension via the self-loops.

## Disposition

APPROVED — merged as PR 1077. The submission gives a complete, formalised disproof of conjecture 00000009634.
