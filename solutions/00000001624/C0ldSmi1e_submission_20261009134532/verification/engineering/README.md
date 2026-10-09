# Independent engineering verification — conjecture00000001624

The hardened verifier passed a fresh real Lean replay, all 20 behavioral regression tests, and three real Lean negative controls. Three independently identified replay defects were reproduced on the earlier source and corrected by the author: incomplete checksum-key validation, unchecked manifest fields beyond package pins, and reuse of stale passing audit evidence.

## Exact reviewed sources

| File | SHA-256 |
|---|---|
| `scripts/replay.py` | `220a44d995b72dfc92ffc9806de6e4205c910e90f6f8d1a6f84bcbd4e382bd2d` |
| `Audit.lean` | `4bb5fe52a96a94ace859b75f0bbf7da91043c30a2f07063e65a77257dfb65fe2` |
| `Verification.lean` | `8b7bd1c71ca83fbfa82b723c1beff0582d2fd54bda12e46d5815f1e15add62bd` |
| `Conjecture1624.lean` | `f2135c4b339236755e8b6fd6dd23e7685d7831dbdbad3f2d9aaf924f5e4a7487` |
| `scripts/check_stale_audit_rejection.py` | `90624bf36cae3da9ab0d1407d4ee4f4fdc8df94935b076f77e8097403793020b` |

The six files in `source/`, including its checksum manifest, were independently compared byte-for-byte with the supplied input directory. All matched. Full source, test, runtime binary, command, log, and evidence hashes are recorded in the accompanying JSON records and deliverable manifest.

## Checks performed

`tests/test_replay.py` contains 20 focused tests. Three launch actual subprocesses to establish that success output, nonzero exit status, and zero-exit warnings are captured and classified correctly. Other tests replace only external Git/Lean operations while executing the real driver: changed/missing/self-consistently rewritten inputs, toolchain and package pin changes, redirected package directories, wrong and dirty checkouts, forbidden proof constructs, missing/stale/malformed/symlinked audit reports, each prohibited dependency category, and refusal to delete a symlinked build tree. Scanner tests cover nested comments, ordinary escaped strings, token separation, and unterminated input. They do not establish that the small scanner is a complete Lean lexer.

The historical 18-test reproducer intentionally exits 1 with exactly three failures on the initial source (`408c4a8855aaf577822fa6ed3e2cb82d397e1659750a9458bfab67c30e8cd9d9`). Its log preserves the demonstrated defects. The final 20-test run exits 0.

The real clean replay used Lean 4.19.0 and the nine supplied neutral standard-library packages. It rebuilt only owned modules and passed with 24 owned/generated declarations, 27,632 transitive declarations, and 3,430 fingerprinted imports. The only axioms were `Quot.sound`, `Classical.choice`, and `propext`; no unsafe or partial dependencies were accepted. Existing imported library artifacts were fingerprinted and their tracked source checkouts checked against pinned commits; this is not a claim of rebuilding the entire standard library from source.

`tests/run_lean_controls.py` injected three separate declarations into `Verification.lean` in an isolated copy. Each fixture compiled successfully, and the unchanged real `Audit.lean` then exited 1:

| Injection | Observed rejection |
|---|---|
| Unreferenced axiom `EngineeringControl.forbidden : True` | `collectAxioms` rejected the owned axiom. |
| Unreferenced unsafe definition of `True` | Audit reported `EngineeringControl.unsafeRoot` in `unsafe_dependencies`. |
| Recursive partial function `Nat → Nat` | Traversal failed closed on generated dependency `_obj`. This checks rejection, not the `partial_dependencies` classification. |

The original source was restored, recompiled, and audited successfully. Earlier control-fixture trials are retained as archival evidence: the first unsafe Nat-valued fixture also failed closed on `_obj`, and an attempted zero-argument partial declaration was rejected by Lean before auditing. Neither trial is counted as a successful final control.

The author's final package was then compared with the tested snapshot: all 13 existing source/input files matched exactly, and the 20-test suite passed against that final package directly. The newly added `scripts/check_stale_audit_rejection.py` was inspected and executed unchanged in an isolated copy. It passed its actual integration challenge: the no-op Lean audit exited 0, the replay exited 1 specifically because no fresh regular report existed, and the stale PASS report was gone. Its full nested replay records are included.

Inspection of `Audit.lean` confirmed ownership-based selection of all declarations from both proof modules, including generated declarations, followed by transitive traversal of types, bodies, opaque values, inductive constructors/families, and recursor rules. The independent `collectAxioms` pass uses an explicit three-axiom allowlist. `Verification.lean` contains eight kernel-checked boundary statements covering intervals, singleton measure, bounded gaps/components, nonmaximal subintervals, one reference energy, the role of closedness, and unrestricted extra predicates. These are formal checks rather than numerical experiments. This engineering review does not replace the separate mathematical interpretation review.

## Reproduction

The snapshots omit all `.lake` files and contain only this problem's source. No other problem, solution history, author private build, or external write was used. Substitute paths for the local Lean runtime and neutral package directory:

```sh
python3 tests/test_replay.py --project snapshots/hardened
python3 tests/initial_18_test_replay.py --project snapshots/initial
cd snapshots/hardened
python3 scripts/replay.py --lean-bin /path/to/lean-4.19.0/bin --stdlib-root /path/to/nine-pinned-packages
cd ../..
python3 tests/run_lean_controls.py --work-project snapshots/hardened --lean-bin /path/to/lean-4.19.0/bin --records records/new-lean-controls
cd snapshots/hardened
python3 scripts/check_stale_audit_rejection.py --lean-bin /path/to/lean-4.19.0/bin --stdlib-root /path/to/nine-pinned-packages
```

The second command is the intentional historical failure demonstration. The Lean-controls command mutates only its explicitly supplied isolated work project, restores its source, and checks the restored audit. Run it only on an expendable copied project beneath this verification directory. The final helper creates its own fixture within that copy and needs the positive replay's uncompressed audit report. Historical records retain original absolute paths for provenance; new runs write records at the supplied paths.

This approval binds only to the exact source hashes above. Documentation-only packaging changes can be checked by manifest comparison; changes to tested source require a new run.
