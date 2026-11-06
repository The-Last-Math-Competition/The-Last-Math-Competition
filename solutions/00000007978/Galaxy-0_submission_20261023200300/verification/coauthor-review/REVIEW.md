# Review of the #7978 PIR counterexample

Date: 2026-10-23 UTC. This review covers the six Lean source files whose hashes are recorded in source-sha256.json. The reviewer also implemented Approx.lean and Coupling.lean, so verification of those two modules is a separate clean rebuild and semantic audit, not independent authorship. A further independent reader should inspect them before submission.

## Verdict and mathematical scope

The literal claim of a complete PIR capacity depending only on server count is false: the number K of independent stored messages matters. For N=1 and K=3, the standard information-theoretic capacity is 1/3, not the displayed 1/2. The submission should explicitly say that the displayed formula is correct for K=2; it is not disproving that correct special case. The original imposes neither K=2 nor N>=2. A nondegenerate N=2,K=3 instance has known capacity4/7 rather than2/3, but the Lean development does not claim the general multiserver theorem.

Primary source actually inspected: Sun and Jafar, The Capacity of Private Information Retrieval, author-hosted manuscript https://newport.eecs.uci.edu/~syed/papers/j75.pdf, Section II equations(3)-(9), Section III Theorem1. The model allows vanishing error and defines download D as an expectation over queries. Therefore a proof confined to fixed answer length or exact decoding would not establish the stated capacity counterexample. The added Approx/Capacity modules address these two issues in the finite uniform-random-tape model.

## Finite coupling, without shared-coin assumptions

Let every desired-index strategy use a uniform finite seed set S of cardinality R; different original finite seed sizes can be equalized by harmless repetitions. Perfect privacy says that the multiset of query values q_i(s), s in S, is the same for i=0,1,2. For each query value q, choose a bijection between the q-fiber for index0 and the q-fiber for index i. The union of these fiber bijections is a permutation pi_i of S with q_i(pi_i(s))=q_0(s). Reorder the ith decoder's seeds by pi_i. Every decoding-error count and the expected download cost is preserved, since a permutation preserves the sum of any function of the seed. This is a coupling of hypothetical executions for analysis, not a physical common-randomness resource provided to the user or server.

Coupling.lean proves this combinatorial construction at the list level; CouplingIndexed.lean supplies its indexed form. Its `coupling_from_equal_query_counts` derives a reordered seed list with the required common query sequence, permutation of the original seed list and preservation of every Nat-valued cost sum. The additional indexed_coupling theorem converts the reordered list into a Fin R -> Fin R relabeling, proves pointwise query alignment, and preserves every total R cost. Packaging the three relabeled decoders into CoupledScheme is a direct definitional identification rather than a single end-to-end exported construction theorem. The record's per-seed decoder may depend on both desired index and the entire coupled seed, which is exactly what reordering requires.

For arbitrary query distributions the same analytical coupling is obtained by first sampling Q from its common law, then sampling each private seed from its original conditional distribution given Q. Marginals and error probabilities are preserved. The full measure/probability machinery is not formalized here; it must be identified as a mathematical extension, not claimed as a Lean library result. The standard entropy/Fano argument gives D >= 3L(1-delta)-1 with delta the joint decoder error, delta <= epsilon0+epsilon1+epsilon2, hence asymptotic rate <=1/3. Download-all achieves1/3 with exact privacy and zero error. No exact capacity is assigned by definition.

## Formal object and proof audit

- PIR.lean constructs actual three-message databases as triples of finite alphabets, explicit base-B packing/unpacking, private query/answer/decoder schemes, the fixed-query injection from perfect zero-error correctness, a proved finite pigeonhole inequality and download-all achievability.
- Approx.lean uses a dependent answer type Fin(2^length(q)), so download length may vary with query. `goodAt` checks all three actual decoder outputs against the actual database fields. `good_count_bound` proves injection on the good database subset; `per_seed_union_bound` counts actual decoding failures.
- `expected_information_bound` sums a per-query counting bound and proves (3L)*totalGood <= 2^(3L)*(totalDownload+R). This bounds average, not worst-case, download. The `+R` term corresponds to one additive bit in the expected bound.
- Capacity.lean combines the actual union bound and expected-cost bound. Once L>=4 and the sum of the three actual error probabilities is at most1/6, it proves 9LR<=4*totalDownload. `rejects_half_neighborhood` excludes every rational rate a/b>4/9. This is a fixed gap below1/2, not merely nonattainment of rate1/2; it rules out a sequence approaching the claimed capacity.
- For vanishing per-message error, the small-error hypothesis eventually holds (e.g. each at most1/18). No Lean theorem about real limits, supremum capacities, arbitrary real-valued random laws, Shannon entropy or Fano's inequality is claimed.
- Answer length is determined by the query as in the source's usual download model. A model with a data-dependent, freely observable uncharged length side channel is not the same model. Prefix-free variable-length coding can be treated by the standard entropy bound, but is not represented by the finite answer type used here.

## Verification performed

All six source modules were copied into a new clean directory, compiled from scratch with Lean4.31.0 using `--trust=0 -DwarningAsError=true`, and replayed with `leanchecker -v`. All exited0. This is fresh replay by Lean's kernel, not a different independent implementation of its kernel. All42 named theorems were axiom-audited; only propext, Classical.choice and Quot.sound appeared. No custom conclusion axiom, sorry, native_decide or unsafe proof escape is used. See independent-verification.log and axiom-audit.log.

The initial helper count proof had an invalid fallback when the shrunken codomain was empty. It was repaired by a separate m=0 case proving all remaining marked elements absent, then the positive-codomain case. The final compiled source, not the discarded draft, was audited.

## Publication boundary

Do not describe the entire arbitrary-distribution Shannon theory as mechanically checked. The complete mathematical proof may use the explicit coupling/Fano argument and the primary theorem; the mechanized result is a genuine finite-model obstruction with variable expected download and a fixed vanishing-error rate gap, plus general list-level and indexed privacy coupling constructions. Source semantics, duplicated submissions, upstream status and final files still require the coordinator's publication gate.
