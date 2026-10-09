# Verification and engineering provenance

The frozen mathematical source is `Conjecture2187.lean`, not a renamed conventional solution file. The original author audit, explanation, exact source statement, configuration, manifest, toolchain, and logs are preserved. `verification/author-freeze.json` is the raw unchanged freeze, SHA256 `12e6c8ffd226ddd321d5fd2151df0f39b940dd3fe23e28ac160ebb4b77da97e5`.

The portable adapter reads the actual `conjecture_id` key. Its exact 13-file mapping preserves every raw freeze entry, including the six original log/verification records, and checks both hashes and byte lengths. The source/inventory/tool binding is `verification/source-manifest.json`. There are no mathematical source edits and no author-file renames.

## Audit coverage

The final engineering portable verifier and full control suite both returned **PASS**. The package includes their actual result/command records; the separate final package review is coordinated after this engineering stage.

The independently measured compiled inventory contains **33 safe declarations** owned by `Conjecture2187`: five definitions and 28 theorems, including generated/private declarations. Ownership comes from Lean's module index, not a namespace, author-supplied declaration count, or explicit theorem list. All 33 declarations are dependency roots.

The complete transitive dependency closure contains **12,296 constants**. Both declaration types and values are traversed, including imported theorem proof values and intermediate declarations. The only reachable axioms are `propext`, `Classical.choice`, and `Quot.sound`. There are zero owned axioms, unsafe/partial owned declarations, unsafe/partial proof dependencies, and compiler exceptions.

Every authored module is freshly built, and `Conjecture2187`, `AuthorAudit`, and `Audit` are individually replayed with warnings treated as errors. The input bytes are checked before/after execution. All nine real dependencies must match their pinned Git revisions and have clean tracked files both before and after. Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`; Lean is 4.19.0. The other exact revisions are preserved in both identical dependency manifests.

The frozen author audit already checks all owned mathematical declarations and their transitive axioms. The additional engineering audit independently emits the complete inventory and checks every type/value dependency, including imported proof values. The engineering agent contributes no mathematical lemma. Source interpretation, mathematical completeness, and report review belong to the separate independent semantic-review role and coordinating contributor; successful compilation is not a substitute for them.

## Meaningful controls

The retained Python suite has **25 discovered tests: 24 pass and one is skipped**. The skipped `test_compiler_artifact_axiom_rejected` is inapplicable because the production policy has no compiler exceptions. Ordinary custom axioms and compiler-shaped unsafe declarations are still rejected. The conditional compiled allowlisted-name spoof fixture is likewise not instantiated and is not counted as executed.

There are **10 compiled negative fixtures**: an owned custom axiom, an unsafe definition, a genuine `partial def`, an unsafe declaration with a compiler-shaped name, a `sorry` proof, a custom axiom hidden in an imported proof, a custom axiom hidden in an imported type, an imported `sorry` proof, a forged imported proof depending on an unsafe definition, and a forged imported proof using `lcProof`. Each must first compile and then fail the unmodified production audit with its intended diagnostic. The direct `sorry` fixture must also fail a separate warnings-as-errors source replay.

The compiled partial-definition fixture was specifically requested when the engineering audit made partial-definition rejection explicit. It compiles a genuine Lean `partial def`, not merely a token scan. This compiler exports its public constant as safe and its generated execution stages as unsafe; the audit rejects the first unsafe stage. The reporting-only metadata in `verification/partial-control-metadata.json` records this behavior. No claim is made that this fixture directly reaches the separate `.partial` safety-enumeration branch. All conventional fixture module names and input-tampering paths were mapped to the actual `Conjecture2187` filename/module.

Two further controls exercise wrong-revision rejection and tracked-file mutation at an unchanged revision in an isolated synthetic Git dependency. The same production pin checker detects the dirty tracked file, and the fixture is restored clean. Shared standard dependencies and user repositories are not mutated. Unit tests additionally cover missing/extra/generated declarations, missing modules, duplicate data, changed types/dependencies/inputs, frozen-source rebaselining, and actual subprocess failure/launch record preservation.

The last two forged-proof fixtures deliberately use low-level declaration insertion only in isolated negative-control projects. Those source strings are visible in `test_verify.py` and result records. Generated bad Lean modules remain in temporary test projects; no fixture is an imported submission module or mathematical premise.

## Provenance and limitations

The engineering scaffold was prepared before candidate selection and contained only reviewed generic runner, audit, and test tooling. No prior mathematical source, theorem strategy, report text, or mathematical evidence was carried forward. The engineering agent retains prior conversation context and is not presented as a fresh mathematical author. `verification/generic-scaffold-provenance.json` and `verification/generic-scaffold-ready.json` identify the exact generic inputs and preparation boundary.

Candidate source access and application occurred only after the explicit frozen release. Adaptation binds the actual owner module and all real paths, preserves the actual freeze schema, appends the independent Audit target, and adds explicit rejection of partial definitions in both owner and closure checks. The corresponding compiled partial control was requested by the coordinator. The strict no-exception policy was not relaxed. Exact adaptations and access provenance are in `verification/engineering-release-acceptance.json`.

The author's initial audit-checking-code build failure remains in `verification/author-logs/lake-build-initial.log`. It is distinguished from the final successful author build and strict replays, whose actual statuses are in `verification/author-logs/verification.json`. Preserving that historical failure does not imply that the final mathematical source fails.

The verifier relies on the standard Lean runtime and the pinned standard library sources with compatible compiled caches. It rebuilds the authored modules and traverses imported proof values; it does not bootstrap the entire compiler and dependency library from source. No numerical experiment or external computation supplies a mathematical premise. Verification here is local, and maintainer acceptance is a separate decision.

## Evidence layout

`verification/README.md` indexes final raw records, input and inventory bindings, the unchanged author logs, generic tooling provenance, and the supplied review receipts. The report source and PDF were copied byte-for-byte; their hashes and the coordinator's visual/compile checks are in `verification/root-report-qa.json`. The engineering task did not regenerate the PDF or independently review its mathematics/layout. The supplied `verification/independent-core-review.json` is bounded to the frozen mathematical core and explicitly predates final package/report review.

The later supplied `verification/independent-report-review.json` records independent complete report/PDF review with no blocking findings or requested edits. It remains distinct from the final assembled-package review. No reviewer scratch proof or auxiliary lemma is incorporated into the submission.
