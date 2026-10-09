# Independent final engineering-package review — conjecture 00000000934

**Verdict: PASS_ENGINEERING_PACKAGE. No finding requiring a change.**

The exact reviewed package completed a fresh hardened verification run: all 11 subprocess stages exited zero, all 35 tests passed, the supplemental independent review sources executed, and all package bytes remained unchanged. The prior `PASS_CORE_MATHEMATICS` and `PASS_REPORT_CONTENT_AND_RENDERING` verdicts are preserved, with their original hash-specific scopes. This engineering receipt does not claim maintainer acceptance or authorize release.

## Exact snapshot and preservation

Input: `/private/tmp/tlmc934-submission/PACKAGE-REVIEW-SHA256SUMS.json`, SHA-256 `fc8f61957902b027ed471668485c34442eba4b108da1f7bb6afae6864d342fb2`.

Every one of its 196 inventoried files was checked before review and execution. Together with the inventory itself the package contains exactly 197 files; there were no extra, missing, or symlinked inventoried files. An exact private copy was made under `engineering-review-work/package`. After verification, every inventory entry, the manifest itself, and the complete file set were independently checked again in both the supplied package and the private copy. All remained unchanged. The additive `ENGINEERING-SHA256SUMS.json` also matched all its 94 entries.

Key engineering identities:

| File | SHA-256 |
|---|---|
| `verify.py` | `f4b504d6d27c8fc0e7f216a2c4e55f30508fe028680b8b73a63e23a29391bb04` |
| `test_verifier.py` | `160ed3bca9794d05e77f708460c6e502a044e392a511f2d20441f25ff77f5ff4` |
| `verification.json` | `be3b6ba614de503f5bfa25efcfdc87997c4d2f0d61f8acb72b7706683d4a0ec9` |
| `owned-declarations.json` | `798ae50b6758ac3a17c6a6d1a8f1fd315abaf592ecc4f11b003f10284710dbb2` |
| `VERIFICATION-PACKAGE.md` | `28b55701307f14ed386a0b1b93bd98d22c2405bba5f2dd600baa0414b02fea78` |

The proof still has SHA-256 `c519a1bba9351c813496d043ef8db4dd4ce3d287f4f5c69a715d84730d4e92e9`. The reviewed report/PDF hashes remain `49d6ed2bd6fc33a9772ddf0a4049a0d9dc9f0fe9db474e693c5f4e1a75aeada5` and `e8375c932ece31bce40396ee15cf6fdc971143025b28e2d47356761bf42a0c28` respectively.

## Source review and fail-closed behavior

The complete 476-line verifier, 268-line test file, configuration, 36-declaration inventory, and complete package guide were read. The generated Lean inspection source and final archived summary were also reviewed. The supplemental sources are byte-identical to the independently reviewed and frozen `IndependentAudit.lean` and `ReviewChecks.lean`.

The runtime path checks are consequential and do not merely search for a success phrase. The verifier binds the original core inventory to a fixed SHA-256, requires the configured core inventory to equal that frozen inventory plus its own manifest, checks every frozen file, and validates the exact toolchain text and all nine dependency revisions. Paths are restricted to existing nonsymlink files within the project. Source registration covers all active non-hidden Lean files; supplemental files are separately hash-bound. Auxiliary Python registration is also checked. The use of hidden directories to exclude dependency/build trees does not omit any active source in this exact inventoried package.

Python checks use explicit exceptions, and the entrypoint rejects optimization flags or `PYTHONOPTIMIZE` before doing verification. This also preserves assertions in the frozen author's auxiliary checker. Subprocess failures and timeouts cannot lead to a certification `PASS`; every successful stage is required before the final summary. Existing log destinations are rejected. Discovery mode is explicitly labeled noncertifying and was not used in this review. The CLI exposes no option to skip the test suite.

A new temporary project receives the exact frozen source bytes and registered supplemental bytes. The proof library output directory starts empty. `LEAN_PATH` is set to that directory followed by the checked upstream cache paths, and `LEAN_SRC_PATH` is removed. The Lake configuration is replayed, `Solution` is built to the fresh directory, and the source is independently replayed, all with warnings as errors. Existing submission proof artifacts are not reused as the proof result. The original `verify.sh` subsequently runs in the disposable project, so its output-writing behavior cannot overwrite archived evidence.

The principal generated audit identifies constants by their actual defining module. It emits declaration kind, safety, and the full `Lean.collectAxioms` result for every owned declaration, including helpers. A separate traversal follows all constant references in types and values, including opaque bodies, rejecting unsafe dependencies and axioms outside `propext`, `Classical.choice`, and `Quot.sound`. The parser requires the precise record structure and ordering, unique declarations and closure names, matching headers/footers/counts, correct module ownership, approved kinds and axioms, and exact equality to the reviewed name/module/kind inventory. Thus omitting a generated helper is not cured by merely altering the reported total.

The frozen author audit is actually executed and its names, summaries, and entire transitive-name file are compared with the principal audit. The two separately registered supplemental sources are then actually executed, and the supplemental audit's complete owned and transitive inventories are compared as well. The source-shaped `ReviewChecks` cannot pass by silently accepting an unrelated substitute theorem. Final source/hash checks occur after the complete test suite.

These checks support fail-closed certification for the exact reviewed package and stated trusted runtime/dependency boundary. They are not a claim that an arbitrary malicious replacement verifier, compiler, or upstream cache can certify its own integrity. The complete engineering/report snapshot is bound by the outer review manifest checked independently here; `verify.py` itself binds the core and supplemental sources, not a human/AI assessment of report text or rendering.

## Fresh independent execution

The recorded command used the private package copy, the pinned Lean 4.19.0 runtime at `/private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64/bin/lean`, and this reviewer's already independently built dependency cache at `/private/tmp/tlmc934-independent-math-review/core/.lake/packages`. It did not use the author's private working tree or private cache. Exact arguments, environment overrides, working directory, duration, and exit status appear in `verifier-command.json`.

The overall verifier exited **0** after approximately 81.2 seconds and printed its final certification `PASS`. The 11 recorded successful stages were:

1. Actual Lean runtime version.
2. Warnings-as-errors replay of `lakefile.lean`.
3. Fresh `Solution` build.
4. Fresh `Solution` source replay.
5. Generated defining-module/dependency audit.
6. Frozen `Audit.lean` execution.
7. Registered supplemental `IndependentAudit.lean` execution.
8. Registered supplemental `ReviewChecks.lean` execution.
9. Frozen input/pin Python checker.
10. Complete original `verify.sh`, including its own Lake build, fresh source replay, and audit.
11. All verifier adversarial tests.

The observed inventory exactly equals the 36 reviewed owned declarations. All three audits agree on the complete set of **30,946 transitive constants**; the independent closure file retains SHA-256 `84d1e821e1e21444ab03587e4805a455c422f09a79c77adf2e2b072e2dbd3503`. The observed axiom union is exactly the permitted three, with no unsafe owned declaration or owned axiom. A separate post-run check reconfirmed all nine dependency revisions and clean tracked source.

## Test coverage and results

All **35 tests** passed, with no skip, expected-failure substitution, or suppressed test failure. The suite contains 28 parser/policy checks and seven real Lean fixture checks. The real checks compile valid and deliberately invalid sources using the same Lean runtime. They exercise a valid proof, an incomplete `sorry` proof rejected under warnings as errors, a type-incorrect proof, a custom axiom, an unsafe definition, native certification through `Lean.ofReduceBool` and its generated helper, and omission of a real declaration even after repairing the audit count.

The parser/policy tests meaningfully cover absent/malformed audit output, extraneous success text, missing footer/closure/summaries, incorrect counts, duplicates, omitted owned helpers, unapproved axioms, unsafe constants, owned axioms, altered/missing dependency pins, modified frozen source, wrong runtime version, optimization attempts, unregistered supplemental source, and changed supplemental hashes. A positive audit fixture and nested-comment handling prevent the rejection-only tests from passing merely because the parser rejects everything. The test runner returns failure when the suite is not successful. No additional tests were added because no concrete unresolved concern remained.

## Documentation claims and preserved scope

`VERIFICATION-PACKAGE.md` correctly presents `verify.py` as the completed-package entrypoint while explicitly preserving `README.md`, `VERIFICATION.md`, and `verify.sh` as the earlier mathematical-core stage. It does not pretend those immutable earlier documents were rewritten to describe later artifacts.

The guide explicitly distinguishes trusted pinned dependency checkouts/compiled cache from newly rebuilt submission proofs. This fresh run respects that boundary. It does not claim a complete upstream-library rebuild. The fresh original-wrapper run and all supplemental replays support the expanded verification claims in the final guide. The report's earlier forward reference to this guide now names an existing reviewed document whose described workflow has actually passed.

The program does not claim to perform the separate semantic or rendered-report assessment. The independent reviews are AI-agent review evidence, not human reviewer signatures or repository-maintainer acceptance. The report expressly states that local compilation and independent review do not constitute maintainer acceptance. No archived receipt or engineering summary is interpreted as approval to merge, publish, or update competition records.

## Limitations and provenance

The review concerns this exact hash-bound package, not future edits. It trusts the supplied pinned Lean runtime and explicitly documented pinned upstream cache; it does not rebuild or manually reread every upstream library declaration. It is not a general-purpose hostile-runtime sandbox assessment. Previously frozen mathematical/report/provenance receipts were not amended. Full parsing and newly executed audit checks replace reliance on archived success logs; historical engineering files were hash-verified, with the definitive archived summary checked, rather than pretending every historical test run was independently repeated.

Authorized materials consisted of this conjecture's exact package, the existing independent review context, and the permitted neutral/runtime/private dependency cache. The authorized author's frozen mathematics and matching report were intentionally reviewed in the preceding phases. No unrelated/prior other-agent mathematics, other problem, prior submission, selector/operational note, app/thread/agent inventory, or external solution was consulted. No package source, proof, report, or test was edited, and no publication or maintainer action occurred.
