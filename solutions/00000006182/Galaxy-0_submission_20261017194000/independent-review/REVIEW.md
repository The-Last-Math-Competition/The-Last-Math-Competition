# Independent review: TLMC 00000006182

Date: 17 October 2026.

## Verdict

PASS for the explicitly stated target: the unqualified exact/all-p expectation-ratio assertion. The mathematical argument, finite graph model, final Lean proofs, reproducibility checks and three-page PDF agree.

The interpretation boundary is important: at a fixed threshold multiplier p=c/n, the expected-count ratio converges to 4/(3c). That narrower asymptotic statement is true and is not refuted. The report and README disclose this prominently. This review does not claim to resolve an unstated threshold-only interpretation of the source.

## Source and mathematical verification

The bilingual conjecture was independently fetched from the official repository using the GitHub connector. Its source blob is 920179a96b1058c56db58613db3647e61f614cd0. The submitted source.md reproduces the statement and appends source-provenance information.

Both C3 and C4 are strictly balanced of density one: every nonempty proper subgraph is a forest and has fewer edges than vertices. Counting unlabelled, non-induced copies gives

- E[N(C3)] = binom(n,3) p^3.
- E[N(C4)] = 3 binom(n,4) p^4.
- Their ratio is 4/[3(n-3)p], for n >= 4 and 0 < p <= 1.

At n=4, the p=1/4 expectations are 1/16 and 3/256; at p=1/2 they are 1/2 and 3/16. The ratios are 16/3 and 8/3, respectively. The cross products are 3/256 and 3/512. All arithmetic was independently recomputed. In particular, the factor 3 in the arbitrary-n denominator is necessary.

For p=c/n the exact ratio is 4/(3c)+4/[c(n-3)], which tends to 4/(3c). The report's additional regimes p=n^(-1/2) and p=n^(-2) give limits zero and infinity, respectively. Its ordinary arbitrary-n argument is correct and is accurately distinguished from the finite Lean formalization.

## Formal semantic review

Read all final mathematical source definitions and proofs. The construction uses actual vertex and edge subsets, a complete endpoint table, incidence-based degrees, valid subgraphs, and all proper nonempty-vertex subgraphs in strict balance. The degree-two cycle classification at orders three and four is exhaustive, includes a walk-based connectivity proof, and yields duplicate-free lists of four triangles and three squares.

The probability model contains every one of the 64 edge assignments exactly once. The probability formula is connected to the product of the six independent Bernoulli factors, has total mass one, and is nonnegative for rational probabilities in [0,1]. Expected values are weighted sums of actual graph copy counts. The formulas 4p^3 and 3p^4 are proved from those sums, not assumed.

The final generic-field theorem uses these same field-valued sums and excludes any proportionality constant in every characteristic-zero field. It therefore avoids a rational-constants-only restriction. Positivity and the probability interpretation at the two rational witness parameters are supplied by the finite rational probability model; interpretation in real probabilities is the usual embedding of these rational values.

No desired cycle count, expectation formula or constancy contradiction is hidden in a definition or hypothesis.

## Independent reproduction and trust audit

Copied the final source into a separate clean directory and ran the supplied verification script with Lean 4.31.0, commit 68218e876d2a38b1985b8590fff244a83c321783.

- Clean Lake build of Main and Audit: PASS.
- Warning-as-error elaboration of Main and Audit: PASS.
- Independent leanchecker kernel replay of Main and Audit: PASS.
- Supplied standard-library Python enumeration of every graph on four and five vertices: PASS.
- Separate reviewer-written Python enumeration, generating cycles from permutations and verifying all proper subgraphs, all 64 hosts and exact expectation polynomials: PASS.
- Full environment audit of all 111 TLMC6182 namespace declarations, including definitions and generated declarations: PASS. Every transitive axiom closure contains only propext, Classical.choice and Quot.sound, as applicable.
- Declaration metadata: no unsafe declarations, custom axioms or opaque declarations.
- Source scan after removing comments: no axiom, unsafe, opaque, sorry, admit, native_decide, run_tac, run_elab, implemented_by or extern tokens.

The full audit is stronger than inspecting only the selected theorem statements in the supplied Audit.lean.

## PDF and package

Read the complete final paper and README. Independently rendered and visually inspected all three PDF pages. The final first two pages are pixel-identical to the inspected rendering before the small provenance-wording correction; the final third page was re-inspected. No clipped formulas, missing symbols, overlaps or illegible text were found. The report states the exact/asymptotic boundary and formal/nonformal boundary accurately.

Verified every entry in the frozen package's SHA256SUMS. The package excludes search probes and build caches. No mathematical source modification was requested during this review. Publication and eligibility are separate decisions; this is a mathematical and reproducibility review.

## Reviewed file identities (SHA-256)

- Main.lean: 16359593ff7f667d9607d2bcc05a720954f7cbb603408c17d82c3451bda64df1
- Audit.lean: d2fb729b38326fbcf9a7d6367f0589f9314a80c5fa04bc2135e71248200a3cb6
- main.tex: b93eca36f14fb88d06ee21d4fd099776fb0ca81bc937c1e4b6ddd2b732feb40c
- main.pdf: 1489268b935aa24fd69ce1a9fc89030593a8077e166749ec6f978f42276bf294
- README.md: 21fc566cee711585d2f93856848d8c1f8352e26514e59e1e6fa1226a86164f07
