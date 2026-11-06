# Independent AI review of TLMC 9343

Date: 2026-10-26 UTC. Reviewer is an AI agent, not a human or competition organizer.

## Original statement and interpretation

Freshly read original bilingual conjecture at upstream commit b355e42906e6eaf52bc7e9d005e0ef02d8aa7400:
https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/b355e42906e6eaf52bc7e9d005e0ef02d8aa7400/conjectures/00000009343.md

English explicitly calls this a zero-one law of exchangeable sequences; no independence or ergodicity assumption appears. The candidate disproof addresses that literal exchangeability-only assertion. It must not be described as refuting the actual iid Hewitt-Savage theorem. The source is terse and invokes the theorem name, so intended restoration of iid hypotheses remains an interpretation caveat, not a mathematical failure of this witness. The report and README prominently preserve this distinction.

## Mathematical and semantic check

The underlying space is genuinely Bool with its full power set and two rational atom weights 1/2. The random sequence maps outcome b to the constant stream b. For every coordinate map, relabeling that stream is literally unchanged, hence its distribution is exchangeable. The chosen event is all coordinates equal true, not merely the event that coordinate zero is true. Surjectivity is exactly what proves event invariance on the entire sequence space. This handles the potential support-only invariance mistake. The pullback is precisely the singleton true, so its measure is 1/2, neither zero nor one.

The two coordinates are explicitly not independent: joint mass 1/2 versus product 1/4. No empirical simulation or arbitrary probability assumption is involved. A universal exchangeability zero-one law would apply to this particular finite probability space, so its restriction is a legitimate necessary consequence, not a strengthened surrogate.

The product-measurability of allOnes is also elementary: a countable intersection of measurable coordinate cylinders. It is proved in writing, not via a general Lean measure-theory library. The finite source measure is defined on every event predicate. Countable additivity reduces to finitely many nonempty events in a disjoint family.

## Independent execution

Initial source copied into a fresh clean directory with only Exchangeable.lean, lakefile.lean and lean-toolchain. Actual Lean 4.31.0 source-only Lake build, strict warning-as-error trust-zero elaboration, separate leanchecker replay, and an independently generated audit of all 19 initial named theorems passed. Only standard propext, Classical.choice and Quot.sound occur, with several elementary invariance proofs axiom-free. No custom axiom, admitted proof, native decision proof or kernel bypass was found.

Initial logs: build.log, strict.log, kernel.log and axioms.log. Final augmented-source and PDF checks are pending below.

## Final augmented source and PDF approval

The author added prefix_probability and countable_union_probability. Independently inspected the proofs: the former inducts over a genuine finite prefix of the event family and the latter proves exact eventual stabilization of every sufficiently long partial sum to the countable union's probability. This directly establishes finite-space countable additivity without needing a general infinite-series library.

A second entirely fresh source-only build of the final 21-theorem module passed, as did strict trust-zero elaboration, all-theorem axiom auditing and separate leanchecker replay. Logs are final-build.log, final-strict.log, final-kernel.log, final-axioms.log. Final source SHA is recorded in final-source-sha256.txt and reviewed-sha256.txt.

Read the complete updated LaTeX report and README. Independently rebuilt the final LaTeX source twice with installed pdflatex and explicit writable cache plus existing format, without installing or changing permissions. The resulting PDF has exactly two pages. Both rendered pages were visually inspected in full; no overflow, clipped text, missing symbols, or legibility defects were found. No overfull boxes occur in the final independent PDF log. Source and PDF hashes are in reviewed-sha256.txt; PDF byte differences due to build timestamps do not affect source equivalence.

Verdict: mathematically sound and semantically faithful as a counterexample to the printed exchangeability-only wording, with the explicit iid-interpretation caveat retained. No claim of a new counterexample to the standard iid theorem, generalized measure theory formalization, organizer acceptance, or human review is warranted. Final duplicate/eligibility/publication checks remain coordinator responsibilities.
