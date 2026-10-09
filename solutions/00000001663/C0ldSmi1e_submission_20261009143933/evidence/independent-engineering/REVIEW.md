# Independent verification engineering review: 00000001663

The frozen mathematical and verification sources pass independent source replay and declaration auditing. No verification engineering defect was found in the checked proof. This result applies to the literal strengthened conjunction formalized in this project; it makes no claim to settle classical Kelly–Ulam reconstruction.

## Scope and isolation

I read the supplied bilingual original, both supplied rule files, the neutral Lean/Mathlib pin inputs, and the current author project for this conjecture. I did not read another conjecture, a solution folder, prior agent proof output, or an earlier project template. I edited no author file. All reviewer-created source, generated objects, controls, logs, and receipts are under `/private/tmp/tlmc1663-independent-engineering`.

The mathematical snapshot was taken after the author's revised freeze. Its four mathematical SHA-256 values match `snapshot/evidence/MATH_FROZEN.json`; the independent snapshot registry additionally binds `Verification.lean`, the copied author audit and finite check, the project configuration, and report. All exact input hashes were checked against the supplied input hash manifest. The neutral manifest originally names a different package; the working configuration consistently renames the current project to `tlmc1663` while preserving every dependency revision.

## Fresh replay

`replay_independent.py` created a new, initially empty `owned-build` and directly invoked the pinned Lean compiler on, in dependency order:

1. `Conjecture1663/Definitions.lean`
2. `Conjecture1663/Proof.lean`
3. `Conjecture1663/Challenges.lean`
4. `Conjecture1663.lean`
5. `Verification.lean`

Every command used `-DwarningAsError=true` and emitted new `.olean`, `.ilean`, and `.c` files. None of the author's owned compiled objects was copied or consulted. The initial empty build state, exact commands, exit codes, durations, and log hashes are recorded in `environment.json` and `commands.json`. The project configuration also compiled independently with warnings treated as errors. This direct source build does not purport to rebuild the entire dependency ecosystem.

The independent audit and the copied author audit were then executed against these fresh owned objects. The copied Python finite checker executed successfully and enumerated all 4, 64, and 4,096 ordered labelled-graph pairs at orders 2, 3, and 4 respectively. Its actual output is in `logs/finite-checks.log`; this finite computation is auxiliary, not a proof of any universal statement.

## Complete declaration audit

`IndependentAudit.lean` selects owned declarations by originating module, not declaration-name prefix. It inventories all 62 declarations from the five owned modules, including 41 explicitly written declarations and 21 generated declarations. The source-classified list is `classified-owned-inventory.tsv`. There is no generated-declaration exception, and all owned declaration bodies are available.

For every owned declaration the audit runs Lean's `collectAxioms`. Separately, it traverses every constant in each reachable declaration's type and available value, recording 4,575 distinct reachable constants and 69,771 type/value edges. It rejects missing declarations, unsafe declarations, non-safe definitions, traversal exhaustion, and every axiom except `propext`, `Classical.choice`, and `Quot.sound`. Those three are exactly the final closure's axiom set. The complete records are in `owned-declarations.tsv`, `reachable-declarations.tsv`, `dependency-edges.tsv`, and `logs/independent-audit.log`.

The author's audit independently returns the same 62/4,575 counts and three-axiom set on the reviewer's new objects. The reviewer additionally scans the mathematical and verification sources, with comments and strings erased, for admitted proofs, custom axioms, native evaluation tactics, unsafe/partial definitions, executable elaborator commands, and external implementation annotations. None occurs. The metaprogramming used by the two audit programs is separate from the mathematical imports and is not a proof dependency.

Explicit `noncomputable` annotations suppress unwanted executable compiler-stage declarations while retaining the ordinary mathematical definitions. The final all-declaration audit needs no allowance for `lcProof`, `Lean.ofReduceBool`, or compiler trust axioms.

## Negative controls actually executed

The isolated `controls` directory contains deliberate invalid examples. Their actual compiler/audit logs are preserved under `logs/attempt02-control-*`.

- An admitted `False` theorem is rejected with warnings as errors. Compiling the fixture permissively first also demonstrates that the declaration audit rejects its `sorryAx` dependency.
- A theorem depending transitively on a custom axiom in an external module is accepted by the ordinary compiler and rejected by the audit.
- An inductive declaration whose type mentions an external custom type axiom is rejected by the audit, including its generated declarations.
- An unsafe definition is rejected by the audit.
- A theorem proved using `native_decide` compiles, but the audit rejects the generated proof's `Lean.ofReduceBool` axiom.
- Changing the diagonal distance witness from zero to one fails compilation.
- Attempting to prove `False` with `decide` fails compilation.

These controls do not import into any mathematical or verification root.

## Pins, fingerprints, and trust limits

The runtime reports Lean 4.19.0, commit `6caaee842e94`, on arm64 macOS. All nine package Git revisions match the supplied manifest, including Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`; all nine package source trees report clean. Exact observations are in `package-pins.json`. The runtime executables and shared libraries are SHA-256 fingerprinted.

The audited import environment contains 4,065 compiled modules: five freshly built owned modules and 4,060 reused external modules. Every imported `.olean` has a unique resolved provider and an individual SHA-256 in `imported-module-fingerprints.json`. Sources are available and individually hashed for 2,793 modules: five owned and 2,788 external. The remaining 1,272 runtime module sources are unavailable and explicitly marked as such. The allowed neutral package directory resolves through symlinks to cached package trees; only that standard-library content was consulted.

The audit trusts the supplied Lean executable/kernel, its runtime, the permitted foundational axioms, the pinned cached dependency objects, and the local execution environment. Cached external objects were not rebuilt. Matching revisions and separately hashing available sources and compiled objects does not establish that those objects are a reproducible compilation of those source bytes. No PDF, publication, eligibility check, repository modification, comment, commit, or push forms part of this review.

## Preserved reviewer failures

`failed-attempts/attempt01` records an audit-utility API mistake: `Environment.find!` is unavailable in Lean 4.19.0. All five mathematical source builds had already passed; the utility was repaired to use checked `find?`, and the entire source replay was restarted into an empty owned build directory.

`failed-attempts/attempt02` records a negative-fixture syntax mistake: Lean rejects the redundant modifier in `noncomputable theorem`. Removing that modifier repaired the control fixture. Neither repair touched any author mathematical or verification source. No failed log was relabelled as a successful run.

## Final frozen author automation independently executed

After the author's final auxiliary freeze, I copied the exported author bundle into a separate reviewer-owned directory. The author manifest SHA-256 is `3dcf24191f6eff29298a1f5cc7ca5383845fb3d88271adc0af74719e81bbd315`. Every manifest-declared file hash matched. The final source/configuration/audit/finite-check files also exactly match the snapshot used by my independent compiler replay.

I executed `scripts/replay.py`, `scripts/negative_controls.py`, and `scripts/source_check.py` in that separate copy. All passed. The fingerprint helper and finite calculation were executed through the replay. I then set aside the two preexisting unlisted Python cache files and repeated all three commands with `PYTHONDONTWRITEBYTECODE=1`, so the final auxiliary run read the frozen Python sources directly. Those repeated commands all passed; the final fresh replay identifier is `ddf34db43d8540b5b7d3fc4e55d21669`. The exact commands, exit codes and output hashes are recorded in `author-automation-commands.json`.

The author negative-control driver executed eleven controls. It rejected mutations of original text, proof source, toolchain, dependency manifest, imported-object pin registry, runtime registry, protected registry, and audit program; forced a new replay despite planted old success files; and rejected changed audit evidence and a changed owned compiled object. Its receipts and actual logs are retained as historical evidence. Source-pin checking is explicitly labelled `SOURCE_PINS_ONLY`, not a build claim.

The two unlisted Python caches are recorded in `python-cache-observation.json`; they are not part of the final export. Their presence did not alter any of the author's 91 declared file hashes or its manifest. No author file was edited by this reviewer.

## Reviewer evidence export

The `delivery` directory is a selected, exact-inventory export. Its `FILES.json` binds every other exported file by relative path, byte size, and SHA-256. It contains actual logs, pinned source snapshots, complete inventories and dependency edges, reviewer audit/replay sources, and clearly labelled negative/failed fixtures preserved byte-for-byte with `.lean.txt` extensions outside build roots. `control-fixture-map.json` maps the executed source paths to their exported archival paths and source hashes.

No dependency cache, symlink, Python cache, or compiled object is exported. The copied author receipts are historical execution evidence; because their owned objects are intentionally omitted from this compact review export, the author's live receipt-object validator is not claimed to work on this reduced export. The exact-file manifest validates the exported evidence itself. Reproduce new source/build evidence with the delivered author project and its replay, or use the reviewer's snapshot and independent replay in a new evidence directory. All full working copies and objects remain separately in reviewer scratch.
