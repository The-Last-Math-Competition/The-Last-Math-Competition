# Solution Review — Conjecture 00000004105 (PR 1152)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023073819`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000004105; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The source asserts that motion-group growth is polynomial if and only if the graph is a tree, and separately that the star-graph motion group grows strictly super-polynomially (yet sub-exponentially). The submission takes the ordinary quantitative meanings of polynomial and super-polynomial growth for a candidate growth function, and the standard four-vertex star K_{1,3}.

**Decisive results.** `Star` is Mathlib's actual four-vertex star K_{1,3}, proved to be a tree with exactly three edges. The source's iff clause gives PolynomialGrowth (growth Star); the star clause gives SuperPolynomial (growth Star). `polynomial_incompatible` proves that no real function can satisfy both, using Mathlib's IsBigO and an explicit all-degrees/all-constants/all-cutoffs numerical super-polynomial predicate (not a syntactic negation). `no_graph_growth_assignment`, `no_necessary_upper_growth_assignment`, `no_all_finite_graph_assignment` and `no_natural_count_assignment` cover every assignment to actual four-vertex graphs, all finite labelled graphs, and natural-valued counts. Thus the two source clauses are incompatible for every candidate growth function, not merely for one chosen value; no value of the motion-group growth is assumed.

**Report correspondence.** The report and Lean agree: the report states the four-vertex star, the tree property, the three edges, the IsBigO-to-envelope equivalence, the quantitative super-polynomial predicate, and the contradiction. `actual_star_is_tree`, `actual_star_edges`, `polynomial_iff_envelope`, `polynomial_incompatible` and `no_graph_growth_assignment` match the report. The report explicitly does not claim a computation of the configuration-space fundamental group or any corrected classification.

## Disposition

APPROVED — merged as PR 1152. The submission gives a complete, formalised disproof of conjecture 00000004105.
