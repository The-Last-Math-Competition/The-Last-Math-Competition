# Disproof of conjecture 00000001473

Minimize `x` subject to `2x >= 1`, `y = 10x`, and `z = 10y`, with three integer coordinates. The unique integer optimum is `(1,10,100)` and the unique real-relaxation optimum is `(1/2,5,50)`. All finite input data have absolute value at most 10, but their infinity distance is 50, exceeding `n * Delta = 30`.

The proof also certifies inequality-only free, inequality-only nonnegative, and equality-only nonnegative forms. The equality form adds an actual slack coordinate, so its dimension is 4 and its bound is 40; the distance remains 50. Every form has unique attained optima and a relaxation vertex. Delta includes constraint coefficients, right-hand sides, costs, objective constant, and all finite domain bounds. The separate sharpness clause is not independently asserted false: falsifying the universal upper-bound conjunct disproves the stated conjunction.

## Materials

- `proof.tex` and `proof.pdf`: matching complete mathematical report.
- `ORIGINAL.md`: exact bilingual conjecture at the source revision used for this submission.
- `ARGUMENT.md`: the independent author's full mathematical argument.
- `AUTHOR_PROVENANCE.md`: the author's frozen input boundary, development history, verification scope, and limitations.
- `lean/`: frozen proof, exact rational audit, and canonical independent verification driver.
- `verification/`: semantic/report reviews, independent execution records, PDF records, source/eligibility checks, and preserved evidence archives.
- `SHA256SUMS.json`: final submission file hashes (excluding that hash manifest itself).

The source revision is `9b795e7a94a6076e49a65a6489e1caf9153abd23`; the exact conjecture SHA-256 is `bdceacf9b92330afb3ee49161d60a121e65ad4724d70bf332b76f7c843ba89d5`. The author's frozen proof SHA-256 is `940f2f162a82f7a58f36bb235482565328048bb4fe0baf7aa7fa304fb7921e2c`.

## Reproduce

Use Python 3.9 or later and Lean 4.19.0. Mathlib is pinned to v4.19.0, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`; all transitive revisions are in `lean/lake-manifest.json`.

From this submission directory:

```sh
python3 lean/verify.py --lean-bin /path/to/lean-4.19.0/bin
```

Without an offline stock library, the driver downloads the pinned dependencies and Mathlib cache. To reuse an existing pristine checkout and its stock compiled cache:

```sh
python3 lean/verify.py --lean-bin /path/to/lean-4.19.0/bin \
  --stock-mathlib /path/to/pinned/mathlib \
  --work-dir /path/to/new-verification-directory
```

The work directory must not already exist. The driver creates a separate project, copies no submitted compiled files, verifies all dependency source bytes against pinned Git blobs before execution and after verification, freshly builds the local proof, and explicitly replays all five authored Lean files with warnings as errors. It records raw command receipts, complete originating-module declaration inventories, type/body/opaque/recursor dependencies, imported artifact hashes, and exact theorem types.

The proof module has 274 compiled declarations: 128 safe kernel roots, including 71 theorems, and 146 compiler-generated runtime roots. The latter are recorded separately rather than treated as mathematical evidence. Every safe root is checked for a complete dependency closure with no unsafe or missing node and only `propext`, `Classical.choice`, and `Quot.sound`. The proof source contains no admissions, custom axioms, `native_decide`, or authored unsafe definitions. Verification/configuration infrastructure is separately inventoried; its runtime implementation is not a proof premise.

Seven negative controls confirm rejection of an omitted proof, custom axiom, unsafe root, unsafe proof dependency, native decision shortcut, changed frozen source, and unlisted Lean module. These intentionally invalid control sources are generated only in the separate verification directory and preserved as test evidence; they are not part of the mathematical proof.

The same driver executes the self-contained exact rational arithmetic audit. It can also be run directly:

```sh
python3 lean/exact_audit.py
```

This auxiliary audit checks all data, point feasibility, objectives, coordinate differences, the strict bound violations, and independent active systems. Full feasible-set descriptions, global optimality, uniqueness, and the vertex condition are proved in Lean, not inferred from finite point tests.

Compile `proof.tex` with a standard LaTeX installation (the supplied PDF was exported with Tectonic 0.17.0). The report also compiled with the desktop editor's compiler, and all three rendered pages were visually inspected.

## Evidence boundaries

Local proof modules were rebuilt. Pinned stock-library binary artifacts were reused and their hashes recorded; the records do not claim a fresh rebuild of every Mathlib module. Verification establishes the stated local checks, not maintainer acceptance.

`verification/author/frozen-development-and-validation.tar.gz` preserves all 80 files from the author's frozen delivery, with its `FREEZE.json` alongside. It includes failed development snapshots and the original author-only `validate.py` and README as historical evidence. Those historical files are not the combined package's entrypoint; use `lean/verify.py`. No development failure has been relabeled as a passing run.

The mathematical author developed the example in a fresh context using only the isolated original statement, rules, pins, and stock library. Independent semantic and engineering reviewers examined the frozen result. Publication/history checks and report assembly were performed separately by the root contributor, with no changes to the frozen mathematical source.
