# Solution Review — Conjecture 00000004277 (PR 1142)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023045803`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000004277; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal: the type lattice is the lattice of all types under joins and meets; every maximal chain of the type lattice has order type ω+ω*. The submission reads 'type lattice' as the standard height-type lattice of torsion-free abelian groups: characteristics P→(ℕ∪{∞}) modulo finite changes at finite coordinates preserving all infinite coordinates, with pointwise meet/join. PrintedOrder is ℕ ⊕ₗ OrderDual ℕ, i.e. ω followed by ω*.

**Decisive results.** Lean constructs the quotient HeightType as an Antisymmetrization of the characteristic preorder, proves the quotient order is exactly the standard order by pointwise-comparable representatives, and installs a genuine Lattice instance with pointwise meet and join. For each real x it defines the characteristic c(x) with value ∞ at primes whose assigned rational is < x and 0 otherwise. It proves x↦[c(x)] is monotone and injective (rational density supplies a prime where the infinity patterns differ), so the range is an uncountable chain. Zorn's lemma extends this chain to a maximal chain M; M is uncountable because it contains the uncountable cut chain. PrintedOrder is countable, so no order isomorphism M≃o PrintedOrder exists. This directly negates the universal order-type clause. The height-type lattice is the standard abelian-group 'type lattice'; the report states this interpretation.

**Report correspondence.** The report matches Lean: standard_order, quotient_inf/quotient_sup, cut_mono/cut_injective/cutChain_uncountable, maximal_chain_counterexample and not_every_maximal_chain_has_printed_order. The report explicitly refutes only the universal order-type clause and makes no claim about the separate continuum-many-chains clause. No stronger prose claim.

## Disposition

APPROVED — merged as PR 1142. The submission gives a complete, formalised disproof of conjecture 00000004277.
