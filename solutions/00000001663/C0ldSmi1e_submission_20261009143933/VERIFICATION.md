# Reproduce and interpret the verification

## Commands

From the project directory, with the supplied pinned dependencies and runtime available:

```sh
python3 scripts/replay.py
python3 scripts/negative_controls.py
```

The default dependency location is `/private/tmp/tlmc-standard-library-419`, and the default runtime binary directory is `/private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64/bin`. A reviewer can set `TLMC_PACKAGES` and `TLMC_LEAN_BIN` to relocated copies with **identical fingerprints**. The script does not fetch or update dependencies and rejects different pinned binaries, imported objects, available sources, revisions, or dirty package source trees.

`python3 scripts/replay.py --check-only` checks pins without building and is explicitly labelled `PREFLIGHT_ONLY`. `python3 scripts/replay.py --validate-receipt <receipt-path>` verifies existing receipt integrity and is explicitly labelled `EXISTING_RECEIPT_INTEGRITY_ONLY`; it never claims to be a fresh build. The default invocation always executes new builds and a new audit.

The dependency package names and exact revisions are in the working `lake-manifest.json`. Its package name is `tlmc1663`; its nine dependency entries are identical to the supplied archived input manifest. The archived input manifest's unrelated top-level project name is preserved verbatim in `source/lake-manifest.json` and is not used as the project's public identity.

## Review on another platform

The strict replay result is bound to the recorded macOS ARM64 runtime binaries and cached compiled objects. A different operating system, architecture, or independently compiled cache can legitimately have different hashes and fail strict replay. Relocation overrides do not waive any hash checks.

For an ordinary source review on another machine, install the official Lean **4.19.0** toolchain for that machine, make `lean` and `lake` available, and use a clean copy of this source project without an owned `.lake/build` directory. Keep the supplied working `lake-manifest.json`; Lake fetches the dependency commits recorded there when absent. Do not run `lake update` or regenerate the manifest as a substitute for its pinned revisions. Network access is needed only if the pinned dependency checkout or its required dependencies are absent.

```sh
lean --version
lake build Conjecture1663
lake build Verification
python3 scripts/source_check.py --packages .lake/packages
lake env lean -DwarningAsError=true scripts/Audit.lean > reviewer-audit.log
python3 scripts/finite_checks.py > reviewer-finite-checks.json
```

The project configuration treats warnings as errors for both roots. `source_check.py` verifies the source/lock registry and every dependency commit and clean source tree; its output is deliberately `SOURCE_PINS_ONLY`. The audit and finite checks execute on that reviewer's locally built objects. The author also executed the portable source-check script against the provided pinned packages, producing `evidence/source-check-portable.json`.

Record the local runtime version, platform, complete build logs, audit result, and object hashes separately. A successful cross-platform source build is independent evidence; it must not be labelled as the recorded strict binary replay unless all of its strict fingerprints also match. Do not edit or bypass a failed pin check to obtain a strict success label.

## Actual successful replay

The author executed the complete replay successfully. The current final run is identified by `evidence/FINAL_RUN.json`; its referenced receipt binds its logs by SHA-256. The first complete successful replay is also preserved at `evidence/runs/run-1605669832fa44e78a64272c17530798-g716lt2x/receipt.json`. Both mathematical and verification roots were built in a new workspace containing no owned `.olean` files. Warnings were errors throughout. The declaration audit and finite enumeration ran after those builds, using the resulting fresh objects.

The final declaration audit counts are:

- **62 owned/generated declarations**, identified by originating module, each independently checked by Lean's axiom collector.
- **4,575 reachable declarations** in the recursive closure through types and all available bodies.
- Exactly the allowed axioms: `propext`, `Classical.choice`, and `Quot.sound`.
- No unsafe or partial definition in that closure, no forbidden axiom, and no compiler-stage exception.

The complete imported module inventory comprises **4,065 modules**: five fresh owned modules and **4,060 external compiled modules**. The external compiled `.olean` objects total **2,869,927,664 bytes**. **2,788 corresponding source files are available** and individually hashed. **1,272 runtime module sources are unavailable** in this runtime installation and are explicitly marked unavailable, never represented as verified source builds. Lean/Lake executables and runtime shared libraries are pinned separately in `RUNTIME.lock.json`.

The exact tool reports Lean **4.19.0**, `arm64-apple-darwin23.6.0`, commit `6caaee842e94`, Release. The `lean-toolchain` requests `leanprover/lean4:v4.19.0`. The exact Python version and all nine clean dependency revisions are recorded in every receipt.

## Finite computation executed

All graphs and all ordered pairs at the stated finite orders were enumerated, with all vertex permutations considered when canonicalizing cards and minimizing edit cost:

| Order | Labelled graphs | Unlabelled graphs | Ordered pairs | Equal-deck ordered pairs | Nonisomorphic equal-deck pairs |
| --- | ---: | ---: | ---: | ---: | ---: |
| 2 | 2 | 2 | 4 | 4 | 2 |
| 3 | 8 | 4 | 64 | 20 | 0 |
| 4 | 64 | 11 | 4,096 | 556 | 0 |

Order two is a boundary test outside the conjecture's domain. The universal disproof and definition properties are proved in Lean; this finite computation does not claim any exhaustive verification above order four.

## Rejection controls

`evidence/negative-controls/results.json` records actual mutations in separate local copies. The controls change the original text, a mathematical source, toolchain, dependency manifest, imported-object pin file, runtime pin file, pin registry, and audit program; each is rejected. They also plant old success files and execute a complete new replay, proving those files cannot bypass compilation or the audit. Mutated audit evidence and a mutated owned compiled object are rejected by receipt validation. Mutations are restored afterward; frozen author sources and shared packages are not modified.

`PROTECTED.json` binds the mathematical roots, verification root, audit/fingerprint/finite-check programs, package metadata, input source copies, and import/runtime locks. Its SHA-256 is embedded literally in `scripts/replay.py`. The replay entry point and negative-control driver are externally bound by `evidence/DELIVERABLE_HASHES.json`, avoiding a circular self-hash. Reviewers should preserve the delivered top-level hash or independently inspect the verification code. No local manifest can establish its own provenance against an attacker who replaces the checker and all of its expected hashes.

## Cache and trust boundary

Shared pinned dependency caches are reused; all owned modules are compiled from source afresh. The entire runtime and Mathlib are not rebuilt. The kernel checks all newly elaborated owned proofs, while imported compiled objects remain pinned dependencies. Fingerprinting corresponding source files records their exact contents; it does not claim an independently verified source-to-binary derivation for each external object. Primitive constants such as inductive recursors have no ordinary expression body; the audit traverses their types and all available bodies, and logs body availability for every visited declaration.

The metaprogram audit and Python replay tools are verification infrastructure, not axioms or proof dependencies of the theorem. All mathematical declarations, including generated declarations in the mathematical/verification modules, are within the audit. `scripts/Audit.lean` is run separately after both roots and is not imported by either root. No `native_decide` is used.

## Archived development findings

The initial warning-as-error build rejected an unused binder. Early challenge builds exposed ordinary Lean elaboration issues that were corrected before the mathematical freeze. Their source snapshots are `.txt` files under `archive/`; logs are under `evidence/`.

The initial all-declaration audit rejected `lcProof` in automatically generated `_cstage` executable compiler intermediates. Those intermediates were not theorem dependencies, but the audit intentionally did not exempt them. Section-level `noncomputable` alone did not suppress them. Marking every mathematical definition/abbreviation explicitly `noncomputable` did suppress them, and the full audit then passed with the original three-axiom limit. The original mathematical expressions and proof arguments were unchanged. Both failed audit logs and source snapshots are retained for review.
