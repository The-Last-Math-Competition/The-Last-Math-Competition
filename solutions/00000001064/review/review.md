# Solution Review — Conjecture 00000001064 (PR 1217)

**Submission:** LibertychaserUS — `LibertychaserUS_submission_20261027165925`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001064; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.1` and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `check.py` exited 124.

## Semantic audit

**Conjecture as filed.** The filed statement says that for every odd q, the minimum size of a Kakeya set in F_q² (a set containing a full affine line in every direction) is q(q+1)/2 + floor((q-1)/2). For odd q the floor is (q-1)/2. The submission formalizes Kakeya sets as finsets of F×F containing a line y = m x + b for every slope m and a vertical line x = c, which is the standard planar definition.

**Decisive results.** The theorem is a proof of the exact minimum, not a disproof. `kakeya_min` gives both halves: every Kakeya set has at least q(q+1)/2+(q-1)/2 points, and the explicit extremal set E = {(x,y) : x²−y is a square} ∪ {x=0} is Kakeya with exactly that many points. The lower bound is proved from Faber's incidence identity, Jamison's 2q−1 blocking-set bound (proved by the polynomial method), the odd-multiplicity parity argument, and the product lemma excluding two non-vertical all-2 lines. The construction is checked directly: the lines y = m x − m²/4 lie in E, and the count q(q+1)/2+(q-1)/2 is derived from the (q+1)/2 squares. The hypothesis Odd |F| is satisfiable (all odd prime powers) and is exactly the filed regime. No step assumes the conclusion.

**Report correspondence.** The report's Theorem 1(a)-(b) is exactly the Lean conjunction `kakeya_min`, and the correspondence table maps each mathematical step to the Lean declarations. The report states the same construction and lower bound, and the Lean axioms are the standard three. The report compiles.

## Disposition

APPROVED — merged as PR 1217. The submission gives a complete, formalised proof of conjecture 00000001064.
