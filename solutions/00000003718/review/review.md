# Solution Review — Conjecture 00000003718 (PR 1210)

**Submission:** LibertychaserUS — `LibertychaserUS_submission_20261027024349`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000003718; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.1` and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement says the roots of the matching polynomial of every tree are all real, and that their distribution is the transform of path counts. The submission reads the second clause as the moment identity: for every k, the k-th power sum of the roots (with multiplicity) equals the number of closed walks of length k in the tree. This is a natural reading because the power sums determine the root multiset and, in a tree, closed walks are back-and-forth traversals of paths.

**Decisive results.** The theorem is universal over all finite trees T and proves exactly the negation of 'some root is non-real' together with the moment identity. All three root conditions are present: Splits over ℝ, card roots = |V|, and every complex root has imaginary part 0. The moment identity is stated with multiplicity via Polynomial.roots.map and Mathlib closed walks. The hypotheses (T.IsTree) are satisfiable and are the filed domain. The proof goes through the independently formalized Godsil–Gutman identity μ(F)=charpoly(A(F)) for forests, then the spectral theorem for real symmetric matrices; it does not assume the conclusion.

**Report correspondence.** The report's Theorem 2(a)-(b) is exactly the Lean conjunction, and the report explicitly states the closed-walk moment interpretation of 'path counts'. The abstract's 'distribution is determined by walk counts' is the standard consequence of the moment identity plus Newton's identities. No stronger formal claim is made than what Lean proves. The report compiles.

## Disposition

APPROVED — merged as PR 1210. The submission gives a complete, formalised proof of conjecture 00000003718.
