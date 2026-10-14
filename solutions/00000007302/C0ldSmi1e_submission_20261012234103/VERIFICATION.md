# Verification of the 00000007302 submission

The independent engineering verdict is PASS. It covers frozen source identity,
fresh compilation of the owned source, package-source provenance, imported
artifact identity, declaration closure, operational controls and manual review
of configuration and auxiliary source. Mathematical interpretation was reviewed
separately. No numerical auxiliary calculation is needed.

| Check | Measured result |
| --- | --- |
| Frozen source/configuration files | 8, checked in 3 copies (24 SHA-256 matches) |
| Mathematical modules | 4 |
| Additional auxiliary module | AxiomAudit, replayed with warnings as errors |
| Lake configuration | Separately replayed with warnings as errors |
| Generic tool identities | 5 SHA-256 matches |
| Runtime binary/library identities | 8 |
| Pinned dependency packages | 9 |
| Pinned tracked package files | 7,507, checked against Git blob identities and private copies |
| Stable stock Git indexes | 9 |
| Unambiguously resolved imported modules | 4,063 |
| Retained command receipts | 60, with exit and stdout/stderr hashes checked |
| Owned declarations | 76 |
| Safe declaration roots | 61 |
| Generated unsafe runtime helpers | 15 (12 definitions and 3 compiler specialization axioms) |
| All reachable graph declarations | 18,364 |
| Declarations reachable from safe roots | 18,340 |
| Required safe capstones | 21 |
| Positive / rejection controls | 1 accepted / 5 rejected as intended |

The imported-module identities comprise 1,272 Lean-runtime modules, 2,540 Mathlib,
130 Aesop, 78 Batteries, 12 Qq, 11 ProofWidgets, 8 Plausible, 4 LeanSearchClient,
2 ImportGraph and 6 owned modules (the five source modules plus the inspector).

The independent stock was cloned from generic pinned stock, without author
compiled outputs. Three missing imports were built from pinned Mathlib source:
`Mathlib.LinearAlgebra.Multilinear.TensorProduct`,
`Mathlib.LinearAlgebra.PiTensorProduct`, and
`Mathlib.Analysis.NormedSpace.PiTensorProduct.ProjectiveSeminorm`.
The receipt is `evidence/stock-preparation/build-receipt.json`. Other imported
dependency artifacts were cached; this review did not rebuild all Mathlib or
bootstrap Lean.

The independent run built a fresh private project with `lake --no-cache --wfail
build`, producing the four mathematical modules. It directly replayed all five
owned Lean modules in dependency order with `-DwarningAsError=true`, including
the nondefault `AxiomAudit.lean`, and separately replayed `lakefile.lean` with
the same warning policy. The sources remained byte-identical to the freeze.
Manual review found declarative Lake configuration, ordinary mathematical
definitions/proofs and `#print axioms` only; no authored IO, initialization,
unsafe declarations, custom axioms or trust-bypass settings were present.

The declaration inspector selects every declaration by originating module,
including generated declarations. It follows constants from types, values
(including opaque values), recursor rules and inductive/constructor relations.
The independent Python checker recomputes all graph closures and trust summaries.
All 61 safe roots and all 21 selected capstones have only the foundational axioms
`propext`, `Classical.choice` and `Quot.sound`, with no unsafe or unavailable
dependency. Source compilation supplies kernel checking; the graph checker is
not another independent proof kernel.

The generated runtime inventory is retained in full. It has 15 unsafe helpers,
including three specialization axioms for `Function.update` and `List.mapTR.loop`.
Its 45 runtime-only findings also mention compiler proof erasure `lcProof` and
four unavailable erased-runtime names. These are explicitly classified in
`evidence/reviews/runtime-helper-classification.json`. None is in any safe-root
closure. The raw run's `PASS_PENDING_RUNTIME_HELPER_CLASSIFICATION` status is
resolved by this separate classification and the engineering verdict. There is
no claim that compiler runtime roots themselves satisfy the mathematical axiom
policy, and no runtime-only computation is used as proof evidence.

The freshly created operational controls checked: an ordinary safe fixture
(accepted), an unrelated custom axiom (rejected), an axiom hidden through an
opaque value (rejected), `sorry` (rejected both by warnings-as-errors and by the
dependency audit), `native_decide` (rejected for `Lean.ofReduceBool` and
`Lean.trustCompiler`), and an explicitly unsafe definition (rejected). All source,
graph, expected-exit and output checks passed. The generic v2 tools are copied
unchanged; their performance-only provenance records contain no prior problem
mathematical source.

The author receipts are separately retained in `evidence/author/verification/`.
They document development checks, not the independent review. The pre-development
`runtime-setup.json` records an earlier Lake-file hash; the later author freeze,
review snapshot and actual independently replayed final Lake file all match.
`evidence/frozen-review-manifest.json` is the authoritative eight-file freeze,
with the author manifest linked by hash. The auxiliary was additionally frozen
from the author's `AxiomAudit.lean`.

## Reproducing the complete independent verifier

The included verifier uses the macOS `/bin/cp -cR` clone workflow. It requires
a prepared stock Mathlib checkout and its eight pinned subdependencies/cached
imports, plus the Lean 4.19.0 `bin` directory. Supply those independently, check
them against the included pins, and use a NEW output directory which does not
exist. No cached dependencies or Lean binaries are distributed in this package.
The Python interpreter must run with assertions enabled (do not use `python -O`).

From this package directory, set the four paths in the shell and run:

```sh
package_dir="$PWD"
stock_dir="/absolute/path/to/pinned-stock"
lean_bin="/absolute/path/to/lean-4.19.0/bin"
new_output="/absolute/path/to/NEW-review-output"
python3 "$package_dir/verification-tools-v2/verify.py" verify \
  "$package_dir/lean" \
  "$package_dir/evidence/frozen-review-manifest.json" \
  "$stock_dir" "$lean_bin" "$new_output" \
  "$package_dir/evidence/expected-pins"
python3 "$package_dir/verification-tools-v2/check_audit_graph.py" \
  "$new_output/declaration-audit.json"
```

This full verifier performs its own strict build, source replay, import binding
and fresh controls. Manually review any generated unsafe helpers in the new
output, as was done for this run. It uses PATH safeguards against network tools
and Git writes; these are not operating-system network isolation. The stock,
Lean runtime and submission inputs are treated as read-only; the fresh output
contains private clones and products.

For the ordinary source check, `README.md` lists `lake build`, strict replay of
each of the five owned source modules and the Lake configuration, and the
axiom-printing command. Dependency acquisition may be needed if the pinned
dependencies are not already available. Preserve the supplied manifest; do not
update its package revisions.

## Inspecting the retained raw records

Extract into a new directory with Python's data extraction filter:

```sh
package_dir="$PWD"
records_dir="/absolute/path/to/NEW-records-directory"
python3 - "$package_dir/evidence/engineering-records.tar.gz" "$records_dir" <<'PY'
import pathlib, sys, tarfile
target = pathlib.Path(sys.argv[2])
target.mkdir(parents=True, exist_ok=False)
with tarfile.open(sys.argv[1], 'r:gz') as archive:
    archive.extractall(target, filter='data')
PY
python3 "$package_dir/verification-tools-v2/check_audit_graph.py" \
  "$records_dir/engineering/declaration-audit.json"
```

The tar members are ordinary files under `engineering/`, in sorted order with
normalized metadata and a zero gzip timestamp. Their hashes and sizes are in
`evidence/engineering-records-manifest.json`. The archive has all 60 receipt
triples, all 18 package source/cache-identity JSON inventories, six control
graphs, the complete declaration graph, frozen/pin/build-output identities,
the copied driver, and the offline safeguard scripts. Actual dependency caches,
the cloned project and compiled artifacts are omitted. Historical review scripts
and receipts retain original paths and are evidence of this run; use the generic
CLI above to reproduce in a different local layout.

## Report and remaining scope

The final report source hash is
`8961362dd0255d9a003ac505f1d5af1666ddce9645fe0c2ee88ec0f7d7023f7d`;
the PDF hash is
`db1a2c4b4ecc6f133cd8b0314e2e652a5d2ecbc0da0619c0ef1c19339f7ca2cb`.
The final native and Tectonic compilations succeeded. The report source's
mathematical content and exact typography-only amendment were independently
reviewed. Root visually inspected all four final PDF pages, including the
Chinese quotation; the checked page images and record are included.

This establishes the stated ordinary relative-nondensity result on the reviewed
source. It does not resolve the original's undefined parameter-space clause,
prove the implementation of Lean correct, rebuild all cached dependencies, or
constitute maintainer acceptance. The included initial eligibility summary and
final public-guard review are dated observations. The latter records 2,806
independently validated checks. Final package review and publication remain
separate decisions; later public changes require a new eligibility check.
