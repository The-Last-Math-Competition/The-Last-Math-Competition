# Author provenance and verification

The mathematical author began with a clean context containing only the original problem and competition rules, the pinned toolchain and dependency manifest, and the supplied stock library/runtime. The author read all files in `/private/tmp/tlmc302-author-input`, including both language rule files and its hash manifest. No other conjecture, solution, prior submission, private feasibility or selection record, repository history, PR, sibling-agent work, or prior task state was inspected. No mathematical helper or external service was used. The argument and Lean proof were independently developed by this author after reading the statement.

The statement's omitted p,q domains and universal quantifiers were reported before formalization. The conventional interpretation of exponent-badly-approximable sets was explicitly accepted by the coordinating source gate and is recorded in the argument and Lean definition; this is not a silent repair.

The stock library was read at `/private/tmp/tlmc-standard-library-419/mathlib`, pinned to Mathlib v4.19.0, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Lean is version 4.19.0 from `/private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64/bin`. The project's manifest and toolchain file are byte-for-byte copies of the permitted inputs, including all eight stock transitive package pins.

The supplied compiled library cache did not contain the Liouville measure module. A private copy of the stock library and its eight packages was prepared in `/private/tmp/tlmc302-proof/.lake/packages/mathlib`. A first copy omitted Git metadata; Lake consequently discarded that incomplete dependency copy and attempted a network clone, which failed. The copy was then recreated with the stock Git metadata needed by Lake to validate the dependency URL and pin. Git history was not inspected. All successful compilation used the permitted stock source and existing runtime. The original shared library was not modified. The eight top-level package entries are symlinks into this private stock copy. This local dependency arrangement is a verification convenience and is not part of the portable submission source.

`dependency-build.log` records successful builds of the required missing stock modules. `project-build.log` records the initial full project build. The final rebuild, warnings-as-errors replays, theorem types, axiom audit, input hashes, and source hashes are saved separately beside this file.

The only axioms permitted in the final audit are Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. There are no custom axioms, admitted goals, or unsafe proof computations. Exact source hashes in `FROZEN_SHA256.json` identify the final immutable mathematical source and argument delivered to the coordinator. Build products and `.lake` dependencies are excluded from the source freeze.

Portable verification (with the pinned Lean toolchain available and dependency access enabled):

```sh
lake build
lake env lean -DwarningAsError=true Conjecture302.lean
lake env lean -DwarningAsError=true Audit.lean
lake env lean -DwarningAsError=true lakefile.lean
```

The checked-in `lake-manifest.json` pins Mathlib and all transitive packages; do not update it. On a fresh machine, Lake retrieves the pinned repositories. Cached stock oleans may be fetched using Mathlib's standard cache mechanism, or the necessary stock modules may be built from their pinned sources. No bespoke computation or generated mathematical data is required. Rebuilding the submission itself requires removing only the submission project's `.lake/build` directory and running the commands above again. These commands do not require this author's absolute scratch paths.

No LaTeX, PDF, PR, publication, or external message was produced by the mathematical author. The coordinator is responsible for report assembly, independent review, and any submission action.
