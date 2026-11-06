# Solution Review — Conjecture 00000003135 (PR 1167)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023225552`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000003135; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** For a nilpotent Lie group (with no connectedness or simple-connectedness hypothesis stated), the unitary dual is in one-to-one correspondence with the coadjoint orbit space, with a KKS-type measure.

**Decisive results.** G=Z/2Z with the discrete 0-dimensional smooth real Lie structure is a genuine nilpotent (abelian) Lie group. Lean constructs its GroupLieAlgebra, proves the Lie algebra is zero-dimensional (finrank 0), so its dual is a singleton and the coadjoint orbit quotient is nonempty and a subsingleton. The full unitary dual is defined as the quotient of all strongly continuous irreducible unitary representations on nonzero complex Hilbert spaces; the trivial and sign representations on C are both irreducible and are proved not unitarily equivalent, giving two distinct classes. Hence no bijection exists, and the universal orbit-correspondence clause is false.

**Report correspondence.** report.tex Sections 1-5 match the Lean construction (discrete Lie structure, zero Lie algebra, coadjoint orbits, UnitaryRep/UnitaryDual, trivial/sign classes, no bijection). PDF text matches. No stronger prose claim.

## Disposition

APPROVED — merged as PR 1167. The submission gives a complete, formalised disproof of conjecture 00000003135.
