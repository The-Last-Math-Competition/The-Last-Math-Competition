# Verification of conjecture 00000001569

Local validation passed. Maintainer acceptance is a separate decision.

## Mathematical scope

The endpoint negates the full uniform lower bound, with its constant and threshold chosen before the point set. The point domain is the standard real Euclidean plane. The finite angle set contains precisely the ordinary unsigned Euclidean angles at pairwise-distinct triples, with equal values counted once. The construction has exactly `n` points and at most two angles for every `n`. For every real `C` and every natural threshold `N`, an actual configuration at some `n ≥ N` satisfies the strict inequality `angleCount < n² - Cn`.

The source has no noncollinearity condition. Excluding the degenerate angle values would only reduce this counterexample's count. Refuting the necessary lower-bound clause refutes the conjunction; no particular meaning is invented for the ambiguous lattice-attainment phrase.

## Builds and proof dependencies

The author, independent semantic reviewer, verification engineer, and coordinating contributor each used separate fresh projects for validation. The coordinator's final public-runner records are in `verification/root-build/`; the independent source-first review and its original build/audit records are in `verification/semantic-review/`.

- Lean 4.19.0; Mathlib v4.19.0 at `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- All nine dependency revisions matched the manifest, with clean tracked sources before and after the final runs.
- Complete Lake build and direct replay of `Solution.lean`, `AuthorAudit.lean`, and `Audit.lean` passed with warnings treated as errors.
- All **26 compiled declarations owned by Solution** were inventoried by module ownership, including generated or private names. All are safe mathematical declarations; there are **zero compiler exceptions**.
- Full traversal of declaration types and values, including imported theorem proof values, covered **19,355 constants**. There were **zero unsafe proof dependencies**.
- Every proof dependency axiom is one of `propext`, `Classical.choice`, or `Quot.sound`. No admitted proof, custom axiom, or native evaluation shortcut supplies a mathematical conclusion.
- The author-frozen mathematical source is unchanged: SHA-256 `00be55d3ec046fa4a383ccc4d17e61b1b166e45b7c077e59e84e810ed7454e3e`.

`AuthorAudit.lean` is the author's original inspection source, preserved byte-for-byte under a distinct filename. The generic `Audit.lean` adds complete module ownership and transitive type/value coverage. The original author freeze record and original Lake configuration are preserved; the packaged configuration includes the additional verification modules. These engineering additions do not change the mathematics.

## Verification-tool controls

The engineer's and coordinator's separate runs agree. The coordinator's actual records are in `verification/root-controls/`.

- **25 unit tests ran: 24 passed and one was explicitly skipped.** The skipped test would attempt to disguise an axiom as an allowed compiler exception; this project has no such exception. Other tests reject custom axioms and compiler-shaped unsafe names.
- **Nine compiled negative controls passed.** Every fixture first compiled; the unmodified production audit then rejected it for the intended reason. Cases cover authored axioms, unsafe definitions, compiler-name spoofing, admitted proofs, and imported intermediary proofs/types hiding custom axioms, admissions, unsafe dependencies or the compiler-only `lcProof` axiom.
- The admitted-proof fixture was also rejected by direct replay with warnings treated as errors.
- A deliberately mismatched expected dependency revision was rejected.
- A real tracked-file mutation was rejected in an isolated synthetic Git dependency while its commit stayed unchanged; restoring the file restored a clean check. The actual shared standard-library checkouts were never mutated by this test.
- All verifier inputs remained byte-identical across execution. Failed subprocess/launch output preservation, omitted/extra declarations, altered types, altered sources and altered inventory records are tested.

The negative fixtures exist only in temporary test projects. Their deliberately invalid proof text is verification-test data, not part of `lean/Solution.lean`. This mathematical proof is entirely deductive and requires no auxiliary numerical computation.

## Independent semantic and document review

A fresh reviewer recorded a source-first checklist before reading the report or proof. The reviewer then read the complete LaTeX report, both rendered PDF pages, the complete frozen project, and the standard-library definitions used for the Euclidean geometry bridge. A separate complete build, strict direct replays, independently written module-owner audit, and expanded endpoint checks passed. No semantic correction was required.

The two-page PDF was regenerated from the supplied LaTeX source and visually inspected. The final export has no overfull or underfull layout warning. Source and PDF hashes are recorded in `verification/pdf-review.json`.

The mathematical author began from only the original bilingual statement, current rules, empty project and pinned standard libraries. Prior problem solutions and selector feasibility notes were not supplied. A fresh helper checked the current problem's semantics; its optional alternative remark was not used. The verifier engineer reused generic checking code; it accessed and applied that code to the new mathematical source only after the source was frozen. That work is distinguished from independent mathematical authorship in `verification/technical-provenance.json` and `verification/authorship/`.

## Submission eligibility and records

The current bilingual rules and original statement were checked, and public solved-status metadata and submission history were investigated. The external history result and coordinating contributor's independent replay are recorded separately from mathematical verification. A final current-state check is required before publication.

Packaged records retain actual command arguments, outputs, statuses and source identities. Duplicate scratch projects and generated dependency/build caches are omitted; their unchanged inputs are bound by the source hashes, and temporary negative fixture sources are present in `test_verify.py` and the control result records. Earlier development failures remain disclosed in the authorship record; they are not represented as successful final checks.
