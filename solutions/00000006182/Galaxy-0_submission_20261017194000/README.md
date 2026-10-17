# TLMC 00000006182: equal density does not give a constant expectation ratio

Status: disproof of the **unqualified exact/all-p constant-ratio clause**.

The triangle C3 and four-cycle C4 are both strictly balanced of density 1.
For ordinary unlabelled, non-induced copies in G(n,p), n >= 4,

- E[N(C3)] = binom(n,3) p^3
- E[N(C4)] = 3 binom(n,4) p^4
- E[N(C3)] / E[N(C4)] = 4 / [3(n-3)p]

At n=4 and the interior parameters p=1/4 and p=1/2, the ratios are 16/3
and 8/3. The exact cross products are 3/256 and 3/512. Thus no constant
works for all p, despite equal densities and strict balance.

## Semantic boundary

This does **not** dispute the standard common threshold p of order 1/n.
For a fixed c > 0 and p=c/n, the exact ratio is

4n/[3c(n-3)] = 4/(3c) + 4/[c(n-3)],

which does converge to 4/(3c). That narrower fixed-scale asymptotic claim
is correct and is not refuted. The source does not specify such a restriction;
this submission addresses its literal exact constancy assertion. The
arbitrary-n formula and asymptotic discussion have complete ordinary proofs
in the PDF, but are not claimed to be Lean theorems.

## Fully checked formal scope

`Main.lean` imports only `Std` and checks the entire finite disproof at n=4:

1. Actual four-vertex and six-edge subsets, the complete endpoint table,
   well-formed graphs, and vertex/edge-subset inclusion.
2. Strict balance against every proper nonempty-vertex subgraph of C3/C4.
3. Exhaustive cycle classification: exactly four triangle edge sets and
   three four-cycle edge sets. Connectivity is proved through an inductive
   graph-walk relation. Copy lists have no duplicates.
4. A complete, injective enumeration of all 64 simple graph outcomes.
5. Product Bernoulli outcome weights, total mass one, and nonnegative
   rational probabilities on 0 <= p <= 1.
6. Symbolic identities E[C3]=4p^3 and E[C4]=3p^4 from actual weighted
   graph-count sums. They hold over every field.
7. The two interior rational-parameter cross products differ. The final
   characteristic-zero-field theorem rules out **any** proportionality
   constant over that field, in particular a real one. It is not limited
   to rational candidate constants.

Main results:

- `TLMC6182.triangle_strictly_balanced`
- `TLMC6182.square_strictly_balanced`
- `TLMC6182.triangles_exact`
- `TLMC6182.squares_exact`
- `TLMC6182.probability_is_independent_edge_product`
- `TLMC6182.probability_mass_one`
- `TLMC6182.triangle_expectation_formula`
- `TLMC6182.square_expectation_formula`
- `TLMC6182.expectation_ratio_changes`
- `TLMC6182.conjecture_6182_constant_ratio_disproved`
- `TLMC6182.no_constant_in_any_characteristic_zero_field`

There are no external dependencies, custom axioms, assumed expectation
formulas, sorry/admit, native_decide, or kernel-bypassing evaluation. Closed
finite computations use ordinary proof-producing `decide`; symbolic
identities use `grind`. `Audit.lean` reports only standard logical axioms
`propext`, `Classical.choice`, and `Quot.sound`, as applicable.

## Reproduce

Lean 4.31.0, commit `68218e876d2a38b1985b8590fff244a83c321783`.
With the matching Lean/Lake binaries on PATH, from this directory:

```sh
./VERIFY.sh
```

This performs:

```sh
lean --version
lake build Main Audit
lake env lean -DwarningAsError=true Main.lean
lake env lean -DwarningAsError=true Audit.lean
lake env leanchecker Main
lake env leanchecker Audit
python3 verification/independent.py
```

A complete run is recorded in `verification/full-verification.log`.
The independent Python script uses only the standard library. It builds
cycles from vertex permutations as sets of unordered edges, enumerates all
host graphs on n=4,5, multiplies the Bernoulli factors edge by edge, and
checks exact `Fraction` expectations. It also verifies strict balance
against all proper subgraphs. Its output is `verification/independent.json`.
This independent computation is supplementary, not part of the trusted
Lean proof path.

## Report

`main.tex` and `main.pdf` give the complete mathematical proof and formal
scope. Rebuild with a usual TeX installation:

```sh
./build_pdf.sh
```

If TeX requires an explicit format directory, pass that directory as the
single argument. The provided PDF was built with pdfTeX 1.40.26, and all
three pages were rendered and visually inspected.

## Source and eligibility

- Original bilingual statement: `source.md`
- [Official source at checked upstream commit](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/cce2d90cb298de9595798eb674d2c80712100532/conjectures/00000006182.md)
- Source blob SHA: `920179a96b1058c56db58613db3647e61f614cd0`
- Metadata and combined historical-PR check: `eligibility.json`

At the 17 October 2026 check, metadata marked both `proven` and `disproven`
false, and no matching prior submission was present in the combined
1,024-item PR history. The original statement was retrieved through the
GitHub connector. This directory contains a prepared submission only;
publication is a separate step.
