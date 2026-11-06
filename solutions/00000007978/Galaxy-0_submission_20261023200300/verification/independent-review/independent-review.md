# Independent nonauthor audit: TLMC 00000007978

Reviewed 23 October 2026. This reviewer did not author any of the six Lean modules or the mathematical report. The audit inspected the complete source, mathematical argument, original bilingual conjecture, and Sun–Jafar's primary author manuscript, Sections II–III, especially equations (5)–(10).

## Verdict

The mathematical disproof is valid for the unrestricted standard PIR statement as posted. The source does not fix the number K of independent messages to two. With one replica and three messages, the standard zero-error and vanishing-error capacities are 1/3, whereas the proposed formula is 1/2. The manuscript correctly identifies this as a missing parameter, not a new discovery, and does not claim to disprove a repaired K=2 statement. It makes no unsupported claims about the other conjuncts.

## Semantics and proof review

The database is a genuine triple of finite message values. The answer function depends on the query and database, not the hidden desired index. The zero-error proof uses support privacy only where it suffices: every possible query admits compatible private randomness for each index. Equality of answers then forces equality of all three messages. The explicit base-B packing/unpacking and pigeonhole proof justify the answer-alphabet lower bound. The download-all construction is actually defined and proved correct and private.

The approximate model does not silently replace expected cost with maximum cost. Its response length is query-dependent, and downloadTotal is the sum over equiprobable random tapes. Error predicates compare the actual decoders with the actual database coordinates. The jointly correct database subset injects into the answer alphabet. The union bound and the proved inequality n*g <= 2^n*(d+1) give an expected-download bound. For L>=4 and summed average errors <=1/6, the final theorem gives 9*L*R <= 4*downloadTotal. Positive tape count is explicitly required by the rate-exclusion theorem. This excludes a whole neighborhood of 1/2 and thus applies to vanishing-error families, not merely exact attainment or zero-error protocols.

The coupling theorem really constructs a reordered seed list from equal query multiplicities and proves preservation of every integer-valued cost sum. It does not assume that real clients share private coins across desired indices. The additional CouplingIndexed module proves actual Fin R relabellings with pointwise common queries and preservation of every integer-valued total cost. Relabelling the three original decoders produces the coupled normal form. No unsupported shared-randomness assumption remains.

For arbitrary randomization, the written entropy proof is correct. A client tape reconstructed conditional on the common query is independent of the database and its deterministic answer conditional on that query. Therefore the tape supplies no additional information about a message beyond query and answer. Fano's inequality and conditional subadditivity give the stated lower bound on expected download. The fixed response length for each query is the standard model used here; nonstandard data-dependent stopping conventions are explicitly not silently substituted. Sun–Jafar's manuscript defines expected cost over queries and allows vanishing error, consistent with this treatment.

## Mechanization boundary

The six Lean modules mechanize finite uniform random-tape counting, actual errors, query-dependent expected cost, coupling by permutations, and a quantitative capacity-separating gap. The arbitrary-probability entropy/Fano extension, real supremum/limit definitions, are mathematical arguments, not falsely claimed Lean theorems. The report states these boundaries. The formalization is materially stronger than an isolated deterministic example, fixed-length bound, or empirical check.

## Actual independent verification

All six source modules were copied to a fresh reviewer directory without compiled objects. Each passed Lean 4.31.0 compilation with --trust=0 and -DwarningAsError=true, followed by leanchecker replay. A separately generated audit enumerated all 42 named theorems. Only standard foundational axioms propext, Classical.choice, and Quot.sound occur. No sorry, custom axioms, native_decide, unsafe declarations, or implementation substitutions were found. Source hashes and complete logs accompany this review.

The complete LaTeX was read. All four rendered PDF pages were visually inspected: formulas, text, references and page boundaries are legible with no clipping or overlap. A separate reference page is stylistic, not a correctness defect.

Reviewed document SHA256:
- solution.tex: de7e9b5aeb93e7f48241adde5404edba2e8279e2c0e9177d0d016e4383547cb7
- solution.pdf: f99f4dd73473691bd96d3ebdbc8dcc5646a4dde1147b338e4542fe44917fba50

Primary source: https://newport.eecs.uci.edu/~syed/papers/j75.pdf
Original problem: https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/b355e42906e6eaf52bc7e9d005e0ef02d8aa7400/conjectures/00000007978.md

This is an independent technical audit, not organizer acceptance or scoring. Publication still requires the coordinator's fresh eligibility and duplicate checks.

Final sixth-module update: CouplingIndexed.lean (SHA256 edd7b15cfe832787bb2046eeb41adc80b482c114ccb59c7636e805d8840593a5) was independently read, strictly compiled and kernel-replayed. The revised coverage paragraph and PDF pages 3–4 were re-inspected; pages 1–2 remain unchanged. All final source hashes are in source-hashes.txt.
