# Independent engineering verification

The author package passed a fresh build and direct Lean replays with warnings treated as errors. All four mathematical modules, the umbrella module and `CheckAxioms.lean` were replayed from their current sources. No compiled submission file was copied from the author's project. Only private copies of the explicitly supplied stock dependencies were used, leaving the submission and stock library untouched.

The supplied clean input manifest, exact English/Chinese statement and rules, embedded source copies, author SHA256 manifest, toolchain and all nine package revisions were checked. Every tracked package file matched its stock counterpart. Every external imported module was bound to a stock or runtime `.olean` identity: 2,994 imports in total. The full inventories and command receipts are in `engineering-evidence.tar.gz`.

The declaration collector selected declarations by originating module, including names outside the author's namespaces. It inventoried 91 declarations and 14,980 transitive dependency nodes. It followed types, values (including opaque bodies), recursor rules, and inductive/constructor links. All 60 safe roots passed: no unsafe dependencies or axioms beyond `propext`, `Classical.choice`, and `Quot.sound`. The 31 unsafe roots are compiler-generated runtime helpers; their full graphs are recorded separately, and they are unreachable from the safe roots. Active mathematical sources contain no authored unsafe declaration. All three capstones have exactly the three permitted axioms. Their complete elaborated types are retained; `disproof` has no assumptions, and `positive_arbitrarily_late` is universally quantified over the requested natural-number index.

Five mathematical/incompleteness controls failed as expected: a missing unboundedness premise, a missing affine-growth premise, reversal of the positive sign, omission of a growth hypothesis when applying the generic theorem, and an incomplete proof. A separate successful file proves the constant and linear countermodels cannot satisfy the removed premises. Three inspector controls first compiled bad fixtures successfully, then required the inspector to reject a custom axiom, an authored unsafe definition, and a `native_decide` proof. The latter exposed `Lean.ofReduceBool` and `Lean.trustCompiler`, both correctly rejected.

The first complete replay reached the successful main audit, then stopped on two linter warnings in the reviewer's countermodel fixture. Its exact receipts and runner version are retained. The fixture was repaired; the second full replay completed all 62 commands with their expected outcomes. No mathematical submission source needed a repair. The final shipped driver differs from the successful second-run version only in reading the audit template under its archival `.lean.txt` extension. This prevents infrastructure from being misclassified as an active mathematical module when checking the final package.

## Normal portable Lean reproduction

Use Lean 4.19.0 as selected by `lean-toolchain`, keep the committed dependency manifest, and run from the submission root:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true TLMC214/PartitionBounds.lean
lake env lean -DwarningAsError=true TLMC214/Sequence.lean
lake env lean -DwarningAsError=true TLMC214/Growth.lean
lake env lean -DwarningAsError=true TLMC214/Disproof.lean
lake env lean -DwarningAsError=true TLMC214.lean
lake env lean -DwarningAsError=true CheckAxioms.lean
```

Do not update the dependency manifest when reproducing these pinned results. The source configuration contains no machine-local dependency path.

## Full offline independent replay

The supplied Python scripts accept paths as arguments and contain no machine-specific input paths. This offline copying workflow requires Python 3, Git, a macOS clonefile-capable `cp -cR`, the Lean 4.19.0 binaries, and the already-populated immutable pinned Mathlib tree (with its `.lake/packages` and stock import cache). `OUTPUT` and `CONTROL_OUTPUT` must not exist. Point `VERIFIER` at this directory:

```sh
python3 "$VERIFIER/verify.py" "$SUBMISSION" "$STOCK_MATHLIB" "$LEAN_BIN" "$OUTPUT"
python3 "$VERIFIER/verify_audit_controls.py" "$OUTPUT/project" "$LEAN_BIN" "$CONTROL_OUTPUT"
```

Each verification command preserves its arguments, working directory, source hashes, exit status, stdout and stderr. Both scripts must print `PASS`. The first script verifies the `SHA256SUMS.json` in the supplied package, so it also accepts a final assembled package with a new comprehensive manifest. It never mutates that package. The audit template is materialized only inside the disposable replay project. Supplemental controls require the project produced by the first script.

## Evidence and scope

`SUMMARY.json` binds this review to the original author's source/configuration hashes. `engineering-evidence.tar.gz` includes both complete replay histories, dependency/source/cache identity inventories, full declaration graphs, negative-control fixtures and receipts, the exact driver versions, clean-input verification, auxiliary syntax checks and the source-token audit. It excludes private build/dependency copies. Deliberately bad Lean controls and historical snapshots are archived as text; they are not build inputs. The author's three auxiliary development wrappers were syntax-checked and inspected as historical receipt generators. The proof uses no separate numerical computation or computational oracle.

The report source hash in this evidence is the author's original layout. Parent preparation later changed only two alignment lines for PDF layout; final package hashing must bind that formatted report and PDF separately. Semantic review, visual PDF review, current submission eligibility and publication remain separate responsibilities.

The stock dependency `.olean` files were checked byte-for-byte against the supplied pinned stock cache; this review did not rebuild all of Mathlib from source or independently bootstrap the Lean binary. The compiler-generated runtime graphs include implementation internals that are not kernel proof dependencies. These limits are explicit; the result is not a claim of zero axioms or zero runtime helpers.

The only reused prior file was the parent-approved generic operational collector `ClosureAudit.lean`; no prior mathematical source was read. Its shipped SHA256 and the driver/evidence hashes are in `SHA256SUMS.json`.
