# Independent engineering review: conjecture 00000007788

**PASS.** The frozen Lean packet reproduced successfully without source correction. The unmodified verifier was run exactly once, from a separate exact copy, using Lean 4.19.0 and the specified pristine stock dependencies. All 24 subprocesses returned zero, including a clean authored build, all four warning-as-error replays, 40 type inspections, 40 axiom inspections, and the nine revision/cleanliness checks.

## Scope and identity

- Frozen input: `/private/tmp/tlmc7788-proof-v2`.
- Independent copy: `/private/tmp/tlmc7788-independent-engineering`.
- `SOURCE_HASHES.json` SHA256: `7c8b54c4e29f55719ad2def3b51fdbe11fe694be389ab9be65a288137973e221` (matches the supplied external digest).
- `verify.py` SHA256: `791ac285b52a0ddea5a1bd0fe384cc84fd30e19538e3780204031fd5eaa02cce`.
- Original/rules/pins manifest SHA256: `492540a5f2f6544e641ea4eabfd265a5064d89f93287908fc65faef70e7fe9a8`; all five input file hashes match.
- Read the original bilingual conjecture, both rules, exact pins, all four authored Lean files, the declaration inventory, complete verifier, build configuration, README, and mathematical notes. No prior solutions, roster/history/thread tools, network research, publication, or managed worktree edits were used.
- This is the engineering/reproducibility review. Mathematical semantic review is separate. No LaTeX/PDF is present in this staged research packet; later report correspondence and complete submission packaging are not certified here.

## Reproduction and commands

Copied all 63 frozen files byte-for-byte, checked the copy, then created a real `.lake/packages` directory. Its mathlib link targets `/private/tmp/tlmc-standard-library-419/mathlib`; the other eight links target the corresponding directories beneath that stock mathlib checkout’s `.lake/packages`. The original has no `.lake` directory, hidden build configuration, or symlinked source files.

The sole verifier invocation was equivalent to:

```sh
cd /private/tmp/tlmc7788-independent-engineering
PATH="/private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64/bin:$PATH" GIT_OPTIONAL_LOCKS=0 python3 verify.py
```

`GIT_OPTIONAL_LOCKS=0` prevents optional Git index writes during read-only status queries. There were no inherited LEAN_, LAKE_, or ELAN_ environment overrides. Both `lake` and `lean` resolved to the specified runtime directory. The actual reported version was `Lean (version 4.19.0, arm64-apple-darwin23.6.0, commit 6caaee842e94, Release)`.

Run interval: 2026-10-09T22:50:07.805743+00:00 through 2026-10-09T22:50:51.000032+00:00. Exact subprocess arguments, working directories, and return codes are preserved in `commands.json` and embedded in `result.json`. All commands used the independent copy as their working directory:

```sh
git -C /private/tmp/tlmc7788-independent-engineering/.lake/packages/mathlib rev-parse HEAD
git -C /private/tmp/tlmc7788-independent-engineering/.lake/packages/mathlib status --porcelain --untracked-files=all
git -C /private/tmp/tlmc7788-independent-engineering/.lake/packages/plausible rev-parse HEAD
git -C /private/tmp/tlmc7788-independent-engineering/.lake/packages/plausible status --porcelain --untracked-files=all
git -C /private/tmp/tlmc7788-independent-engineering/.lake/packages/LeanSearchClient rev-parse HEAD
git -C /private/tmp/tlmc7788-independent-engineering/.lake/packages/LeanSearchClient status --porcelain --untracked-files=all
git -C /private/tmp/tlmc7788-independent-engineering/.lake/packages/importGraph rev-parse HEAD
git -C /private/tmp/tlmc7788-independent-engineering/.lake/packages/importGraph status --porcelain --untracked-files=all
git -C /private/tmp/tlmc7788-independent-engineering/.lake/packages/proofwidgets rev-parse HEAD
git -C /private/tmp/tlmc7788-independent-engineering/.lake/packages/proofwidgets status --porcelain --untracked-files=all
git -C /private/tmp/tlmc7788-independent-engineering/.lake/packages/aesop rev-parse HEAD
git -C /private/tmp/tlmc7788-independent-engineering/.lake/packages/aesop status --porcelain --untracked-files=all
git -C /private/tmp/tlmc7788-independent-engineering/.lake/packages/Qq rev-parse HEAD
git -C /private/tmp/tlmc7788-independent-engineering/.lake/packages/Qq status --porcelain --untracked-files=all
git -C /private/tmp/tlmc7788-independent-engineering/.lake/packages/batteries rev-parse HEAD
git -C /private/tmp/tlmc7788-independent-engineering/.lake/packages/batteries status --porcelain --untracked-files=all
git -C /private/tmp/tlmc7788-independent-engineering/.lake/packages/Cli rev-parse HEAD
git -C /private/tmp/tlmc7788-independent-engineering/.lake/packages/Cli status --porcelain --untracked-files=all
lake env lean --version
lake build
lake env lean -DwarningAsError=true Conjecture7788/HullMeasurable.lean
lake env lean -DwarningAsError=true Conjecture7788/GenericRate.lean
lake env lean -DwarningAsError=true Conjecture7788.lean
lake env lean -DwarningAsError=true Audit.lean
```

## Build, inventory, and proof safety

The verifier deletes only the copy’s `.lake/build` after rejecting a symlink at that path. This directory was absent in the exact copy. The clean build newly compiled `Conjecture7788.GenericRate`, `Conjecture7788.HullMeasurable`, and `Conjecture7788`; no authored object files were inherited. Each of those three sources and `Audit.lean` then replayed with `-DwarningAsError=true`.

The full-source review found exactly 40 explicit authored declarations: 3 in HullMeasurable, 8 in GenericRate, and 29 in the main module. All appear in `DECLARATIONS.txt`, in the matching `#check` and `#print axioms` lists, and in the fresh raw audit output. This includes definitions, both probability instances, geometric and probability lemmas, measurability and integrability results, expected-volume correspondence, the lower bound, analytic divergence and inequivalence lemmas, source exponent, and final refutation. No meaningful authored result is omitted. Locally bound proof facts and compiler-generated proof auxiliaries are covered transitively by their containing declarations.

Every axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`. There is no authored `sorry`, `admit`, custom axiom, `native_decide`, `unsafe`, declaration injection, custom tactic/elaborator code, compiler override, or hidden bypass. Audit.lean contains only the intended import, pretty-print option, checks, and axiom prints. Normal Mathlib tactics construct proofs checked by Lean. The inventory regex is narrow, but the complete manual source review confirms it covers the actual frozen files; no reliance was placed on that regex as a universal Lean parser.

The verifier uses fixed argument-list subprocesses and no shell evaluation. Its only deletion is the checked local build directory; its writes are local validation records. The dependency manifest equals the original nine-pin manifest. Dependency sources and caches were reused as explicitly requested, not rebuilt from scratch. No executable auxiliary mathematical computation is needed: all mathematics is symbolic Lean proof; the Python program performs verification infrastructure only.

## Raw evidence and unchanged inputs

All 24 commands have fresh stdout/stderr logs. I inspected the build and all replay outputs, the 40 displayed declaration types and axiom records, and every dependency/version result. All stderr files are empty; no warning, error, failure, or `sorryAx` diagnostic appears. `validation/clean-build.log` is an inherited file that the verifier does not refresh; it is explicitly excluded from independent-run evidence. The authoritative clean-build evidence is the newly written `clean-build.stdout` and `clean-build.stderr`.

The external manifest digest and all source hashes matched before and after execution. All 63 original frozen files remain unchanged. A before/after metadata inventory of all 35,417 entries under the stock mathlib tree, including dependency trees and caches, shows zero added, removed, or changed entries. The nine dependency worktrees were clean at the exact pinned revisions. The stock snapshots and empty delta are retained beside this report.

`fresh-log-hashes.json` hashes all 48 fresh command streams, the fresh command list and verification summary, and the outer verifier streams. `result.json` embeds these hashes, all source hashes, all exact commands, and every declaration’s axiom list. `initial-package-hashes.json` also records the complete 63-file frozen copy.

## Frozen source hashes

| File | SHA256 |
| --- | --- |
| `Conjecture7788.lean` | `9484eda5d5694500f862c73fa5693b866ea62e489979e56b12cf164f2aba7ad1` |
| `Conjecture7788/HullMeasurable.lean` | `dc6d57508b9b0eec410fdf91111632868f9e19625ac5a664534ea61831ae97c3` |
| `Conjecture7788/GenericRate.lean` | `f27f2f5f69436481054b2a5062aa2da87675e8f1d1211807ec4224d3513f2f8a` |
| `Audit.lean` | `2c70056c334c02ba6da1a83fb75bbefc9d48957636eba67c785790d80d6b1ba5` |
| `DECLARATIONS.txt` | `4d4a658b3fa6937459df5a273cb969b110ed95124477534088ee92511c5cff65` |
| `lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| `lakefile.toml` | `3bfd67caefe58d07acb82f3987d24bd18b6875c1677474da78f782b6d83ea70b` |
| `lake-manifest.json` | `56f7aa9722d120b38ffe868179164054411be9398660939609cb8a0c55e48637` |
| `MATHEMATICAL_NOTES.md` | `2ba0221ae4956d22df8bb71d337af671b450ea77fdb6eacdf79928c5184a11c7` |
| `README.md` | `f7383f4b5f435ab4f71153f73673719fac0a42afc8f6f0e7071588c19e543d0d` |
| `verify.py` | `791ac285b52a0ddea5a1bd0fe384cc84fd30e19538e3780204031fd5eaa02cce` |

## Fresh evidence hashes

| Evidence file | SHA256 |
| --- | --- |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-mathlib-head.stdout` | `7c5e5dfacfc0943447dba5f5bd28c520d15249702af49b30e242982ee4fa03fb` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-mathlib-head.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-mathlib-status.stdout` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-mathlib-status.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-plausible-head.stdout` | `8c225aad5e3d382454f4b320bf788030dd981c0ed087f232f4eeda4b80b2211f` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-plausible-head.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-plausible-status.stdout` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-plausible-status.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-LeanSearchClient-head.stdout` | `fe5e2b291ee7c0ee2862e8c87ec70fc29e8599b3ff16a9b39cfe76f27fd30207` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-LeanSearchClient-head.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-LeanSearchClient-status.stdout` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-LeanSearchClient-status.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-importGraph-head.stdout` | `830441e9e75ac681a70b9f4ec6fbae725f97714ac30e20544b916b6ac5096a9c` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-importGraph-head.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-importGraph-status.stdout` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-importGraph-status.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-proofwidgets-head.stdout` | `a693832492e2787ecb1b1e1f9235c0945c3c17cd270cbf4dbabddce2c2334c71` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-proofwidgets-head.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-proofwidgets-status.stdout` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-proofwidgets-status.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-aesop-head.stdout` | `43887a17947e75ebec56372cb5b25c10ae389c69ac88c2627ffecfc0adfd8e08` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-aesop-head.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-aesop-status.stdout` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-aesop-status.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-Qq-head.stdout` | `3a113a4fee8a9c52c075c546887de0b28e78a8b8f8c69d4b8d6986bdc0e20545` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-Qq-head.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-Qq-status.stdout` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-Qq-status.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-batteries-head.stdout` | `d1dd9e03465309b43b034589c936326b14f616e7fb2f3f52c17f8b9094426f47` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-batteries-head.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-batteries-status.stdout` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-batteries-status.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-Cli-head.stdout` | `83775c0c37df4892edd11712ba9c0fc5657534af1f399ea6da534ec4b489df2e` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-Cli-head.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-Cli-status.stdout` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/dependency-Cli-status.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/lean-version.stdout` | `adae83ba7663543abb21a1527013239eb469a7dbff15bea8c52d90901b42cc65` |
| `/private/tmp/tlmc7788-independent-engineering/validation/lean-version.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/clean-build.stdout` | `79abcaf8b6a86bf3387c3b6b5616c1b0635625b5176a0ea0e51cddf4b27f5695` |
| `/private/tmp/tlmc7788-independent-engineering/validation/clean-build.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/warning-replay-1.stdout` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/warning-replay-1.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/warning-replay-2.stdout` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/warning-replay-2.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/warning-replay-3.stdout` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/warning-replay-3.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/warning-replay-4.stdout` | `ace7930ba451a9b873722a360c43dfc0bd3366e46d5f283b8aded45a3940cec4` |
| `/private/tmp/tlmc7788-independent-engineering/validation/warning-replay-4.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/private/tmp/tlmc7788-independent-engineering/validation/commands.json` | `d8e2d7969ab8ef31d1b0994c27498e9e9ba52056f1b89cf5578760a1e9962183` |
| `/private/tmp/tlmc7788-independent-engineering/validation/summary.json` | `33778d554811ed99f742b98b91c7b016652649cea84cc57972ed091f6f32f6ff` |
| `/private/tmp/tlmc7788-engineering-review/verifier.stdout` | `a0f5d596caded2c5e7c6d3f62fc4660288b86633e481cd2e0b835a1f7506a515` |
| `/private/tmp/tlmc7788-engineering-review/verifier.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |

**Needed corrections: none for this engineering audit.**
