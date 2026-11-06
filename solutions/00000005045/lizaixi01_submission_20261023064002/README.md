# 00000005045: equal local Hanf data do not imply global graph isomorphism

The source explicitly defines its local-to-global conversion as conversion from Hanf local isomorphism to global isomorphism. This package disproves that necessary transfer for radius 2, already at degree 2 and at arbitrarily large equal graph orders. It does not invent numeric entries in the unspecified conversion table or refute the actual Hanf theorem about bounded-quantifier-rank first-order equivalence.

For every t >= 0, take t+1 disjoint copies of C12 and 2(t+1) copies of C6. Both actual finite SimpleGraphs have 12(t+1) vertices and degree 2. Every rooted induced closed radius-2 neighborhood is the actual five-vertex path. The proof constructs rooted GraphIsos, a genuine vertex Hanf matching, equivalences between every actual rooted-type fiber, and all threshold agreements. A global GraphIso would send a connected C12 into one C6, inducing an impossible injection Fin 12 -> Fin 6. Every size cutoff and threshold has such a counterexample.

The ball predicate is proved equivalent to an actual walk of length at most 2. No disconnected-distance fallback or assigned neighborhood/count is used. Nat.card is applied to actual finite ambient vertex subtypes. All named definitions, abbreviations, instances and theorems are explicitly audited in Check.lean, including proof-bearing equivalence constructions.

Primary definitions: Anuj Dawar, Simons Institute lectures (2016), [lecture II, PDF page 4](https://simons.berkeley.edu/sites/default/files/docs/5233/lecture22.pdf), and [lecture III, PDF pages 9-10](https://simons.berkeley.edu/sites/default/files/docs/5234/lecture31.pdf). Both were directly read by the worker and supervising AI. They distinguish actual Hanf locality from a global-isomorphism claim.

`SOURCE.md` preserves the exact bilingual source at the recorded upstream commit. `report.tex` and `report.pdf` give the complete mathematical argument and scope. `lean/` is the pinned Lean 4.33.0 project; run `bash verify.sh` there. `evidence/` binds original qualification, newly built source, actual axiom audits, full official fresh kernel replay and PDF/source semantic reviews. `SHA256SUMS.json` binds every other file.

OpenAI Codex assisted, with independent review by a separate supervising AI. This is not human certification; organizer acceptance is pending. Only the literal source's necessary global-isomorphism transfer is refuted. A different unstated meaning of the undefined numeric table lies outside the conclusion.
