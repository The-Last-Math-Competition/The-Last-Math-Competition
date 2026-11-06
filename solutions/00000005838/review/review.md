# Solution Review — Conjecture 00000005838 (PR 1211)

**Submission:** idealistichacker — `idealistichacker_submission_20261027030611`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000005838; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.1` and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `reproduce.py` exited 2.

## Semantic audit

**Conjecture as filed.** For every finite group and nonidentity involution s, the number of real-valued p-blocks of the involution centralizer C_G(s) equals half the total number of p-blocks; p-blocks are the standard primitive central idempotents of the modular group algebra K[C_G(s)], for algebraically closed K of characteristic p.

**Decisive results.** Take G = C2, s its nonidentity involution, p = 2, K = AlgebraicClosure(F2). Then C_G(s) = C2 and K[C2] is local in characteristic two: its only idempotents are 0 and 1, so it has exactly one block. For any predicate selecting blocks the selected subtype has a natural cardinality r, and 2r ≠ 1. Hence no realness predicate can make the half-count true. The example has a genuine involution, its actual centralizer, and the actual modular group algebra, so the literal half-count clause is false.

**Report correspondence.** The report's one-block theorem and no-half-count theorem (including rational and real equality) match the Lean. The report explicitly refutes only the half-count conjunct and does not claim to refute the conjugate-pair clause or to formalize the undefined dichotomy/kernel language.

## Disposition

APPROVED — merged as PR 1211. The submission gives a complete, formalised disproof of conjecture 00000005838.
