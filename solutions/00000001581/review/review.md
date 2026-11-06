# Solution Review — Conjecture 00000001581 (PR 1153)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023082026`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001581; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The source speaks of 'Q-points' of the PVI monodromy manifold but writes the finite-looking formula N_p=p²+ap+1 with a∈{-1,0,1}. The submission treats both readings for the standard zero-local-trace PVI character surface x²+y²+z²+xyz=4 (the Cayley member, θ_i=1/2), and states that no PVI parameters are specified in the source.

**Decisive results.** For the Cayley surface, Lean constructs actual SL2(Q) representations of the four-punctured-sphere presented group with trace coordinates (2,-s,s), s=u+1/u, u=n+2, and proves the points are distinct and lie in the Jacobian-regular locus (the x-partial derivative is 4-s²≠0). Hence the rational point type is infinite and its cardinality is not the finite number p²+ap+1 for any p,a; `literal_Q_formula_impossible` states exactly this. Separately, the same surface has exactly p²+1 points over F_p for every prime p, including p=2, so the intended finite-field pattern holds with a=0. The submission is therefore a disproof of the literal Q-point formula and a proof of the finite-field pattern for the standard member. The source does not specify other PVI parameters, and the report explicitly limits the claim to the Cayley member.

**Report correspondence.** The report and Lean agree: the report states the rational parametrization, the trace coordinates, the Jacobian-regular locus, the infinite cardinality, the all-prime count p²+1, and the finite-field pattern with a=0. `actual_trace_coordinates`, `rationalPoint_injective`, `smoothPoint_injective`, `literal_Q_formula_impossible`, `point_count_prime` and `dual_domain_conclusion` formalize those claims. The report explicitly says the full RH/GIT identification is cited, not reproved in Lean, and does not claim a formula for other PVI parameters; the prose is not stronger than the formalization.

## Disposition

APPROVED — merged as PR 1153. The submission gives a complete, formalised disproof of conjecture 00000001581.
