# Solution Review — Conjecture 00000001734 (PR 1178)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024064225`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001734; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal reading: the full SL_2 character variety of a fibered hyperbolic 3-manifold group has only finitely many integral points (integer trace coordinates), with a bound depending on the number of boundary tori. The submission uses the figure-eight knot exterior, a fibered hyperbolic 3-manifold with one torus boundary, and counts the full character variety including the abelian component.

**Decisive results.** The theorem negates the finiteness claim. For each n, the representation ρ_n with ρ_n(a)=ρ_n(b)=I and ρ_n(t)=[[n+3,-1],[1,0]] is an actual SL_2(Z) representation of the presented figure-eight group; every word has integer trace, the full character is determined by χ(t)=n+3, and the characters are distinct. Hence there are infinitely many integral characters, and their trace coordinates (2,2,n+3) are infinite integer points of the published character-variety model, realized by actual representations. The hypotheses are satisfiable and the conclusion is a negation of finiteness.

**Report correspondence.** Report and Lean agree: both give the same representation family, the integral trace theorem, injectivity of the character family, and the infinite realized integer-point set in the trace curve. The report explicitly says the family lies on the abelian component and does not address irreducible/canonical or fixed-boundary variants; no stronger claim is made.

## Disposition

APPROVED — merged as PR 1178. The submission gives a complete, formalised disproof of conjecture 00000001734.
