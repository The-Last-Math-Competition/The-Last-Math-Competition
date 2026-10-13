# Independent internal review: TLMC 00000003980

Date: 2026-10-13 UTC. A separate coordinating AI reviewer performed these checks; this is not an official competition review or organizer acceptance.

## Result
PASS for disproof of the stated every-pair assertion, with the explicitly disclosed formalization boundary below. Final publication must use matching frozen files and refreshed eligibility.

## Mathematical and semantic review
The two systems are actual total tagged truth-table decoders, not arbitrary length functions. Propositional formulas are unbounded, use a functionally complete syntax, and are evaluated on every assignment to their occurring variable range. Acceptance requires equality with the complete generated assignment list as well as successful evaluation, preventing incomplete-table certificates. Soundness and completeness are proved in Lean. Rejected certificates map to a fixed tautology. A syntactically different tautology witnesses that the two tagged decoding functions are distinct.

Tag translation preserves every decoded formula and exact encoded length. Hence both systems have identical shortest-proof lengths on every tautology. This excludes even the very weak requirement of a single violation of each polynomial bound somewhere in a formula family, in both directions. It consequently excludes the usual eventual or infinitely-often superpolynomial separations, without assumptions about naturality or explicitness of the family. Shortest proofs are obtained by well-ordering over all finite proofs, not finite search.

Crucial domain bridge: the Lean ProofSystem record only includes semantic soundness/completeness, not a machine complexity field. Refuting a universal statement over that broader domain alone would not refute the original narrower Cook-Reckhow domain. The report does not use that invalid inference. It separately proves that the two concrete decoders are polynomial-time total surjections. Their finite token grammar is unambiguous, tokens fit in fixed four-bit words, invalid raw strings map to the common truth formula, and serialization length is proved in Lean. Unary indices ensure vars<=syntax size<=input size. The row-count guard runs before constructing the exhaustive table. If the guard succeeds, the table has at most N rows with at most N bits each; if it fails the verifier rejects without enumeration. The binary integer 2^vars has only vars+1 bits. This proves polynomial-time admissibility in proof-input length even though proof generation may be exponential in formula size.

Formalization boundary is acceptable and explicit: Lean verifies recursive value/cost meters and the assembled budget bound, not the exact execution time of compiled Lean or a Turing machine. Parsing correctness, encoding injectivity, raw-bitstring extension and bit-machine complexity are established by the elementary written argument. The 13(N+1)^2 theorem bounds the named budget only; allocation constants and bit-machine overhead are not claimed kernel-verified. There is no runtime axiom or hidden conclusion assumption. The elementary domain bridge was independently checked in full.

## Checks actually performed
- Read the complete Main.lean, Costs.lean and mathematical report.
- Isolated source-only strict Lean4.31.0 compilation of both modules: exit0.
- Separate leanchecker Main and leanchecker Costs invocations: both exit0.
- Transitive axiom audit of all34 authored theorems: standard propext/Classical.choice/Quot.sound only.
- A separate source-only Lake project build: exit0, 5jobs.
- Independent Python implementation of token parser/encoder, total decoders, explicit tag translation and semantic truth-table comparison: 404 formulas (177 tautologies), 4848 structured certificates including malformed tables, all16105 token strings of lengths0..4, 2000 corrupted strings, distinct-system witness and large-index rejecting guard all passed. These are regressions only, not a substitute for unbounded proofs.
- Compiled PDF rendered and all3 pages visually inspected. No clipping, unreadable equations or missing glyphs; text matches the report.

## Reviewed hashes
Main.lean SHA256 29eba93469872fba8d3aa267c9f85c1b7225d481cc594b3be6bffbe2f2ffc1eb
Costs.lean SHA256 69f24dee7fbd53bf108ad608dbff5a93ddf391a4202313cd01d51951923bd533
report.tex SHA256 c5e156f9308e849bc4705eb901579a6c848adc5ab53636e4c56636ccf7340bc5
report.pdf SHA256 80cb8a8738244df044cf2db2248b82f5ebd89cd393711eb13076af10074791e3

Final formatting delta: emergency line stretch added to eliminate an overflow. Pages1 and2 are pixel-identical to previously reviewed images; page3 was re-rendered and visually reviewed again. Mathematical text and Lean source unchanged. Final hashes above replace the earlier rendering.
