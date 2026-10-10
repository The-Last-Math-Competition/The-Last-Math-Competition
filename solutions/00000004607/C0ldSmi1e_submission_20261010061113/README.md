# Conjecture 00000004607: disproof

A convex nonnegative real function on `[0,V]` with zero endpoint values must be identically zero there. If `V > 0`, its midpoint is therefore another zero, contradicting the original assertion that only zero volume and total volume are zeros. Symmetry and an explicit formula cannot remove this contradiction.

The report treats both language versions, explains the ordinary finite positive volume domain, and does not invent a definition of “concavity correction.” It gives the flat unit torus as a familiar geometric realization of every volume in `[0,1]`; the obstruction itself applies to every positive finite total volume.

## Files and precise formal boundary

- `Disproof.lean`: all mathematical definitions and proofs. It uses stock `ConvexOn ℝ (Set.Icc 0 V) f`.
- `AxiomAudit.lean`: `#print axioms` for all three final theorems.
- `report.tex` and `report.pdf`: matching rigorous report. The parent compiled the final source and visually inspected all three PDF pages; `verification/pdf/QA.json` records the final identities and review. The author records predate PDF production.
- `lean-toolchain`, `lakefile.lean`, `lake-manifest.json`: pinned Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` with its dependency revisions.
- `verification/`: actual commands, exit codes, build and strict source-replay logs, and preserved failed attempts.
- `provenance/`: original authorized inputs, input hashes, stock-source record, development source snapshot, and author provenance.
- `SHA256SUMS.json`: SHA-256 hashes of the final submission, excluding itself.
- `provenance/AUTHOR-MANIFEST.json` and `provenance/author-package.tar.gz`: the original frozen author package and its exact manifest. The archive contains the original report and README; the final report changes only line and page layout. `verification/pdf/report-formatting.diff` records that change.

In namespace `IsoperimetricCorrection`:

1. `zero_on_volume_interval`: for real `V ≥ 0`, every convex nonnegative function on `[0,V]` with both endpoint values zero vanishes throughout the interval.
2. `no_nonnegative_convex_double_zero`: for real `V > 0`, no convex nonnegative function on `[0,V]` has zero set exactly `{0,V}`.
3. `no_shape_requirements`: for real `V > 0`, no function meets those three properties together with complementary-volume symmetry.

`ShapeRequirements` names the numerical property package explicitly asserted in the original. It does **not** define the unspecified concavity correction. Functions are represented as `ℝ → ℝ` and all relevant claims are restricted to `[0,V]`; extending an interval function outside this set imposes no extra constraint. The formalization does not define an isoperimetric profile, a geometric correction operator, or “explicit,” and does not formalize the illustrative torus geometry. The impossibility of the necessary scalar properties is fully formalized; no desired conclusion is assumed.

## Reproduction

Install the Lean toolchain specified by `lean-toolchain`. In a fresh checkout with network access, obtain the pinned dependencies and their standard cached artifacts:

```sh
lake exe cache get
```

The exact Mathlib revision is fixed in `lakefile.lean`; retain the supplied manifest to fix all dependency revisions. Lake materializes the dependency checkouts as needed. Alternatively, use already available stock dependency packages at these revisions. The author used local package symlinks to the supplied stock library and existing caches, without fetching or modifying stock sources.

Run the complete project build and then replay both source files with warnings as errors:

```sh
lake build
lake env lean -DwarningAsError=true -DautoImplicit=false Disproof.lean
lake env lean -DwarningAsError=true -DautoImplicit=false AxiomAudit.lean
```

Both libraries are default build targets. The replay of `Disproof.lean` elaborates the source again; the audit imports its built module and prints the axiom dependencies. Each theorem reports only `propext`, `Classical.choice`, and `Quot.sound`. The source uses no admitted proofs, custom axioms, or native evaluation proof mechanism.

The recorded local binary directory was `/private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64/bin`, with Lean reporting version 4.19.0 and commit `6caaee842e94`. These local paths are operational details, not project dependencies.

## Actual verification evidence

`verification/RESULTS.json` records successful exit codes for the final complete `lake build`, strict replay of `Disproof.lean`, and strict replay/axiom audit of `AxiomAudit.lean`. It also records the exact verified source hashes and a before/after inventory of dependency files (outside `.git`); the changed-path list is empty. The dependency artifacts were pre-existing stock caches. This is a complete build of this project, **not** a fresh build of all Mathlib.

Development attempts are retained without presenting them as successful checks:

- `build-attempt-01.log`: compilation failed because the first import list did not bring real numbers into scope. `provenance/failed-attempt-01.lean.txt` preserves that source. The small wrapper itself also failed afterward because it used a reserved zsh variable; `build-attempt-01-wrapper.txt` records this separately.
- `build-attempt-02.log` and `.json`: an optional nested operating-system sandbox could not start (`Operation not permitted`, exit 71); no Lean check occurred in this attempt. Its policy is preserved in `dependency-readonly.sb`. This is not a source failure or a successful sandbox enforcement claim.
- `build-attempt-03.log` and `.json`: after adding the stock real-number import, both project libraries built successfully and all three axiom reports passed. A dependency-file inventory recorded no changes.
- `full-build.log`, `strict-disproof.log`, and `strict-axiom-audit.log`: the final successful checks. An empty strict source log means the command completed without warnings or errors; its exit code is in `RESULTS.json`.

## Independent review and final packaging

`verification/independent-semantic/` contains a separate full mathematical review of both language versions, the report, definitions, and proofs. It passed with no required mathematical changes. Its final addendum checks that the report layout changes preserve the mathematics. The geometric illustration remains an ordinary mathematical explanation, while the necessary scalar impossibility is formalized.

`verification/independent-engineering/` contains a fresh offline project rebuild, strict compilation of all three authored Lean files including the project configuration, and a transitive declaration audit. It found four safe mathematical declarations, 5,253 reachable declarations, only standard axioms, and no unsafe dependencies. The evidence binds 2,413 imported module identities and all nine pinned package revisions. Fresh negative controls demonstrate rejection of admitted proofs, extra axioms (including transitive and unrelated-namespace cases), native evaluation axioms, and authored unsafe declarations. Full raw receipts and earlier operational failures are retained in its archive.

The final engineering run used fresh private dependency copies and disabled optional Git index refresh; the original stock index hashes were unchanged before and after. Earlier stock/private-clone index differences are inconclusive about an original-stock mutation and are disclosed in the engineering README. Cached stock imports and the supplied Lean runtime remain trust assumptions; the project was rebuilt, but Mathlib and Lean were not bootstrapped from source.

For the independent verifier, keep `verify.py` beside its `templates` directory and use a fresh output directory outside this submission:

```sh
python3 verification/independent-engineering/verify.py verify \
  "$PWD" "$PWD/SHA256SUMS.json" \
  /path/to/stock/mathlib /path/to/lean-4.19.0/bin /path/to/new-output
```

This recorded workflow uses macOS copy-on-write copying. The engineering README explains the ordinary recursive-copy substitution for other systems. The selected manifest is checked before and after the run; no submitted compiled artifacts are reused.

The original frozen author package is preserved unchanged in `provenance/author-package.tar.gz`. The final package adds the independent records, final PDF and report-layout corrections. `provenance/AUTHOR.md` discloses incidental exposure to unrelated agent summaries after this proof had already been independently derived and drafted; no prior solution to this conjecture was supplied or reused. Historical non-use cannot be certified solely from the files.

No auxiliary mathematical computation is needed. Local checks and independent agent reviews do not constitute maintainer acceptance. Public eligibility and publication checks are maintained separately from this mathematical submission.
