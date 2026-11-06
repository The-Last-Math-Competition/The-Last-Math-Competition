# TLMC 00000009343: exchangeability alone is insufficient

A single fair bit repeated forever is exchangeable. The event that all coordinates are one is invariant under every coordinate permutation on the full sequence space, but has probability one half. This refutes the printed exchangeability-only zero-one assertion; it does not refute the genuine iid Hewitt–Savage theorem.

## Source and scope

[Official statement](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/main/conjectures/00000009343.md), checked 2026-10-26. The source says “exchangeable sequences” and does not include independence. If its intended meaning silently retains the iid hypothesis of the named classical theorem, this counterexample does not apply to that corrected problem. This qualification is substantive, not a claim that the classical theorem is false.

## Reproduction

Lean 4.31.0, no external packages. With that toolchain on PATH:

    lake build
    lake env lean -DwarningAsError=true -t0 Exchangeable.lean
    lake env lean -DwarningAsError=true -t0 Audit.lean
    lake env leanchecker Exchangeable
    pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error solution.tex
    pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error solution.tex

Do not install or execute any unrelated code. `verify.sh` contains only these project build/verification commands. `logs` records execution; an initial failed build is preserved separately as development history, not presented as passing.

## Exact formal coverage

- `probability` is the sum of two equal rational atom weights, on all subsets of Bool.
- `probability_empty`, `probability_universe`, `probability_bounds`, `probability_ext`, `probability_disjoint_add` verify the actual normalized finite probability model.
- `disjoint_family_eventually_empty` proves that any disjoint countable family has only finitely many nonempty events. `prefix_probability` and `countable_union_probability` formally prove that the probability of the countable union equals every sufficiently long finite probability sum, completing countable additivity for this space. The project does not import or claim a general infinite-series/measure-theory formalization.
- `X b n = b` is an actual infinite random sequence.
- `X_exchangeable` proves distributional invariance under arbitrary coordinate bijections for every event predicate, stronger than just finite-dimensional exchangeability.
- `allOnes_surjective_invariant` and `allOnes_symmetric` prove full-space event invariance, not merely invariance on the support.
- `allOnes_probability` derives one half by evaluating the finite measure of the pullback.
- `counterexample` and `conjecture_exchangeability_only_false` give the witness and formal negation of the restriction of the printed universal law to this space.
- `not_independent_first_two` verifies that joint probability is one half rather than the product one quarter, explicitly explaining why the iid theorem does not apply.

All event predicates on the finite source space are measurable. The all-ones event on sequence space is a countable intersection of measurable coordinate cylinders; that standard product-measurability argument is in the report, not a separately imported measure-theory framework. No simulation, approximation, empirical inference, or unverified oracle is used.

## Disclosure

Prepared and reviewed with AI assistance. Independent AI checks are not human review. No acceptance or scoring is claimed. There are no custom axioms, admitted proofs, native evaluation proofs, or kernel bypasses in this project. The axiom audit records the ordinary Lean foundational axioms actually used.
