# Verification and reproduction

This submission is a mathematical counterexample under the interpretation stated
in the report and README. Compilation is one check; the independent source and
report reviews establish the correspondence between the actual walk, spectral
objects, mixing definitions, and the original numerical sufficient criterion.
These are local checks and agent reviews, not a maintainer review or acceptance.

## Frozen source and compilation

The source manifest in `evidence/frozen-review-manifest.json` identifies all
11 Lean/configuration files, including eight Lean modules totaling 1,395 lines.
It has SHA-256
`db3effdd39210ad094c0f16e0fba2f19819086aa9cee8a921208b3cf0eb055f0`.
No compiled author artifacts were used as submission inputs in the independent
build. The verifier copied the frozen source and created a private generic
dependency checkout/cache copy.

The independent run used Lean 4.19.0, commit `6caaee842e94`, and its bundled
Lake `5.0.0-6caaee8` (Lean 4.19.0), on macOS arm64. It checked the exact
committed toolchain and manifest, nine dependency revisions, and 7,507 tracked
dependency files. Mathlib is pinned to
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.

`lake --no-cache --wfail build` succeeded. Every owned Lean module was then
replayed directly with `-DwarningAsError=true`, including the separately
imported `Audit.lean`. The Lake build has one informational `ring_nf`
suggestion, with no warning or error. All eight strict replays passed. The
declarative TOML configuration was separately read in full; it has no executable
configuration hooks. The unchanged source, pins, runtime binaries, dependency
index, and imported artifact identities were checked through the run.

## Declaration and axiom audit

The audit selects declarations by originating module, including generated
declarations outside the submission namespace. It covers 342 owned declarations
and 31,861 nodes in their exported dependency graph. Its 292 safe owned roots,
including all five final theorems, have no unsafe dependency or unapproved
logical axiom. The five final theorems depend exactly on `propext`,
`Classical.choice`, and `Quot.sound`. There is no source `sorry`, `admit`,
`native_decide`, custom axiom, or kernel-trust bypass.

Lean also generated 50 unsafe runtime declarations: 42 definitions and eight
compiler placeholder axioms. They are inventoried separately, not silently
dropped or described as absent. None occurs in any safe owned root's proof
dependency closure. The raw driver deliberately records
`PASS_PENDING_RUNTIME_HELPER_CLASSIFICATION`; the separate engineering verdict
and explicit helper classification completed successfully and close that gate.
This raw record is preserved unchanged.

The graph consistency checker passed. A supplementary reviewer script checks
the fixed permitted-axiom policy, safe-root enforcement, duplicate root/graph
fields, complete unique owned module mapping, actual tool versions, exact
source hashes, every command receipt and stream hash, all imported artifact
hashes, and capstone types. It also checks that the reviewed source avoids the
generic driver's unsupported dotted-path collisions and multiple modules on
one import line. Python assertions must remain enabled for these checks.

The run preserves 62 command receipts; all stderr streams are empty. Six
intentional nonzero command results belong to negative trust controls. The
positive fixture succeeds. All five negative fixtures are detected: direct
custom axiom, transitive opaque assumption, admitted proof, native decision,
and unsafe runtime dependency. Seven independent Python hardening fixtures
also pass. Negative fixtures are verification-tool inputs, never imported by
the mathematical submission.

## Auxiliary exact computation

`auxiliary/exact_regression.py` uses only Python's standard library and exact
`Fraction` arithmetic. Two independent executions pass and produce identical
JSON. It constructs the actual support and transition matrix for
`N = 4, 5, 6, 7, 8, 11, 16`; checks generation, exact half holding, stochasticity,
symmetry, positive two-step transitions, a full-rank eigenbasis and its matrix
action; and compares 56,700 entries obtained by repeated matrix evolution with
the closed formula at times zero through 24 from every starting state. It also
checks exact TV distances, genuine first threshold times, and both spectral
ratios. Three negative controls detect wrong normalization, a wrong slow
eigenvalue, and an incorrect time-zero TV formula.

Run from the submission root:

```sh
python3 auxiliary/exact_regression.py
```

These finite tests are supplementary. All infinite-family assertions and
limits are proved in Lean and in the report; no finite sampling is used as an
asymptotic argument or formal assumption.

## Reproducing the stricter audit

The normal portable project build is given in `README.md`. To reproduce the
recorded stricter driver, prepare an unmodified generic Mathlib checkout with
the pinned dependencies and required imported cache, a Lean 4.19.0 runtime,
and a new output directory. The supplied driver uses macOS `cp -cR` for private
cache copies. From this submission root:

```sh
python3 verification-tools-v2/verify.py verify \
  lean evidence/frozen-review-manifest.json \
  /absolute/path/to/pinned-mathlib-stock \
  /absolute/path/to/lean-4.19.0/bin \
  /absolute/path/to/new-audit-output \
  evidence/expected-pins
python3 verification-tools-v2/check_audit_graph.py \
  /absolute/path/to/new-audit-output/declaration-audit.json
python3 verification-tools-v2/test_hardening.py \
  /absolute/path/to/new-hardening-output
```

Review and classify the generated runtime-helper inventory separately. The
retained supplementary reviewer script records this run's exact directory
layout and counts; adapt only its path bindings for another checkout, keeping
the frozen identities and fixed trust policy. Raw evidence archives preserve
the command arguments, source hashes, streams, audit graph, import identities,
positive/negative controls, supplementary checks, and explicit classifications.
They do not contain the private dependency checkout or compiled library cache.

## Trust and coverage limits

The Lean source compilation supplies kernel checking of this submission's
proofs. The dependency audit and graph checker inspect dependency structure;
they are not independent proof kernels. Cached dependency `.olean` files were
identified and matched to supplied generic stock, while pinned tracked source
bytes were checked separately. This does not establish a fresh source-to-cache
build for the whole library. Mathlib was not rebuilt in full and Lean was not
bootstrapped. Runtime/import hashes identify supplied artifacts rather than
authenticate their origin. Runtime library imports lack the pre-build cache
baseline used for external packages. PATH network wrappers are safeguards,
not operating-system network isolation. Full manual source/configuration review
supplements the token scan and audit.

The original statement's undefined conditional-gap, second-order, and comparison
phrases are not assigned new meanings. The proof refutes the explicit ordinary
gap/TV numerical sufficiency, under both actual minimum-eigenvalue readings.
The report and semantic reviews explain this boundary. Public eligibility was
checked separately through pinned source/rules, metadata, path history, public
PR/issue metadata, overlapping updates, and exact/topic searches. Those are
bounded, non-atomic public observations, not a claim about every fork, deleted
history, or every possible semantic paraphrase.
