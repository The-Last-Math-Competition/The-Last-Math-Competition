# Verification record

This package preserves author freeze revision 2 for conjecture `00000001478`. The raw author `FREEZE.json` is `verification/author-freeze.json`; its original schema and hashes are unchanged. `verification/source-manifest.json` binds the portable verifier's complete source/configuration/inventory input set. `verification/compiled-inventory.json` was measured from a separate fresh build, not inferred from the 54 explicit declarations.

## Measured coverage

The engineering public verifier and the coordinating contributor's independent fresh reproduction both returned **PASS**. The engineering control run also returned **PASS**. The coordinator separately rehashed and inspected the original build/control records; `verification/root-validation.json` records that check and distinguishes the still-pending final package/publication steps.

The engineering inventory contains **75 safe declarations**: 43 owned by `NuclearNorm`, 6 by `PolynomialCone`, and 26 by `Solution`. There are 47 theorems, 25 definitions, one inductive type, one constructor, and one recursor. This includes compiler-generated equation/proof and structure declarations. Ownership is determined from Lean's module index, not a namespace or naming pattern.

All 75 declarations are roots of the dependency traversal. Their full transitive closure contains **16,780 constants**, using edges from both declaration types and values, including theorem proof values and imported intermediate declarations. The only reachable axioms are `propext`, `Classical.choice`, and `Quot.sound`. There are **zero owned axioms, zero unsafe owned declarations, zero unsafe proof dependencies, and zero compiler exceptions**.

The fresh full build and warnings-as-errors replay cover `NuclearNorm`, `PolynomialCone`, `Solution`, `AuthorAudit`, and `Audit`. The verifier checks the exact input bytes before and after the run and checks all nine real dependency revisions and tracked-file cleanliness before and after. Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b` with Lean 4.19.0; the remaining eight exact revisions are in the manifest.

`AuthorAudit.lean` is the author's 54-explicit-declaration self-check. The complete compiled audit is separately authored engineering code. The engineering verifier contributed no mathematical lemma or proof repair. Independent mathematical/semantic review is a separate role, recorded by the coordinating contributor; build success alone is not that review.

## Controls and their scope

The Python suite discovers **25 tests: 24 pass and one is skipped**. The skipped test is `test_compiler_artifact_axiom_rejected`, because this candidate has no compiler execution exception. Ordinary authored axioms and compiler-shaped unsafe names remain explicitly rejected. The conditional compiled allowlisted-name spoof fixture is not instantiated for the same reason and is not counted as an executed control.

The **nine compiled Lean rejection fixtures** are:

1. An owned custom axiom.
2. An unsafe owned definition.
3. An unsafe definition with a compiler-shaped name.
4. A theorem containing `sorry`; the audit and a separate strict source replay must both reject it.
5. A custom axiom hidden through an imported theorem proof.
6. A custom axiom hidden in an imported type dependency.
7. A hidden imported theorem containing `sorry`.
8. An imported forged theorem whose proof value depends on an unsafe definition with no axiom dependency.
9. An imported forged theorem whose proof value uses `lcProof`.

Each fixture must first compile in an isolated project and then fail the unmodified production audit with the intended diagnostic. The last two fixtures deliberately use low-level declaration insertion only inside temporary negative-control projects to test traversal beyond ordinary elaboration. These strings appear in `test_verify.py` and captured fixture records; the generated Lean fixture modules are confined to temporary control projects and are not mathematical premises or submission modules.

Two further controls exercise dependency enforcement: an intentionally wrong expected revision, and a tracked-file mutation at an unchanged revision in an isolated synthetic Git dependency. The latter uses the same `check_pins` function as the real dependency checks, rejects the changed file, and restores the fixture to clean state. Neither control changes any shared standard dependency or user repository. Unit controls also cover missing modules/generated declarations, duplicate rows/JSON keys, changed types/dependencies/inputs, attempted rebaselining of frozen mathematical source, and preservation of actual failing-command output.

## Provenance and retained attempts

The author developed the mathematics from the exact original/rules and permitted standard Lean/Mathlib sources, with a fresh helper for `PolynomialCone.lean`; the full authored explanation and provenance are preserved unchanged in `verification/author-mathematics.md`. The author also read workspace README rule sections. The coordinator's receipt `verification/author-rule-equivalence.json` records that the operative English and Chinese rules match the current input copies, while the complete README bytes differ because of leaderboard content. This is not described as byte identity of the full READMEs.

The engineering agent retained prior task context. Reuse for this candidate was limited to three generic engineering files from the earlier verified tooling: the portable Python runner, its generic controls, and the Lean inventory/closure audit. No earlier mathematical Solution, report, author audit, or mathematical evidence was copied. Generic scaffolding was prepared before the freeze; candidate mathematical files were accessed and applied only after the explicit frozen release. `verification/engineering-provenance.json` records the exact reused hashes and this boundary.

The first frozen revision built its mathematical modules but was rejected by the broader production audit: it generated 35 unsafe execution artifacts, including nine unsafe specialization axiom placeholders. A diagnostic established that these were absent from the safe mathematical closure; that diagnostic was not production approval. The author then made exactly five `noncomputable` annotations and issued immutable revision 2. All definition bodies, theorem statements/proofs, imports, and original configuration remained unchanged. The engineering agent independently checked the exact five-line change and retained every failed/diagnostic attempt locally. A compact attempt receipt is included; duplicate failed projects are not packaged. The production policy was never relaxed.

The report source and PDF were copied byte-for-byte from the coordinator's reviewed artifacts. `verification/root-report-review.json` records the compiler/render checks and report hashes. This engineering task did not regenerate the PDF or independently perform the report's visual/semantic review.

## Included evidence and limitations

`verification/README.md` indexes the final raw build/control records, inventories, closure, source bindings, and provenance receipts. Command records contain the actual executable arguments, local working directories, timestamps, exit status, stdout, and stderr. Absolute paths in historical records identify where those runs took place; new runs may use different paths.

Source dependencies are standard pinned Git checkouts with tracked files checked clean; their compatible compiled caches are prerequisites. The runner rebuilds the authored modules and checks imported proof values but is not a from-source rebuild of the entire Lean compiler and dependency library. No numerical optimizer, external symbolic computation, or auxiliary mathematical calculation supplies a proof premise. Tool self-tests do not establish the interpretation of the original conjecture; that is covered by the separate mathematical review. Local verification is not maintainer acceptance.
