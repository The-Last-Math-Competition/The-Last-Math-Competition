# Solution Review — Conjecture 00000001004 (PR 1131)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023024334`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001004; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement says that for fixed n≥5, m₂(n,q)=c_n·q^{⌈n/2⌉}(1+O(q^{-1})) with c6=2. The submission reads the n=6 case literally as m₂(6,q)=2q³(1+O(q^{-1})) and refutes it on the unbounded subfamily of odd prime fields q=p.

**Decisive results.** For every odd prime p, Lean chooses a nonsquare d∈F_p and forms S={[1,u0,u1,u0²−d u1²,u2,u3,u2²−d u3²]:u∈F_p⁴} in PG(6,p). It proves S is a genuine cap (no three distinct collinear points, via the quadratic mixing identity and anisotropy), |S|=p⁴, and maxSize is the true maximum over all caps, so p⁴≤m₂(6,p). Since p⁴−2p³ is not O(p²), Lean proves no r=O(p^{-1}) can satisfy m₂(6,p)=2p³(1+r p) eventually. This directly negates the filed n=6 asymptotic on the unbounded prime subfamily; the hypotheses are satisfiable.

**Report correspondence.** The report/PDF state the same cap construction, the same cardinality and cap proof, the true maximum over all caps, and the same IsBigO/eventual expansion negations; the Lean theorems match. No stronger prose claim.

## Disposition

APPROVED — merged as PR 1131. The submission gives a complete, formalised disproof of conjecture 00000001004.
