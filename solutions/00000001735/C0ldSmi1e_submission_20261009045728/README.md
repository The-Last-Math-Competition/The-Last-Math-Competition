# Disproof of conjecture 00000001735

For all ordered integer solutions of `X³ - 2Y³ = k`, the claims “the maximum solution count is 12” and “only finitely many integers attain that maximum” cannot both hold. Scaling a solution by a nonzero integer injects the solutions at `k` into those at its cube multiple. An attained global maximum at any nonzero `k` would therefore occur at infinitely many distinct parameters. The zero parameter has exactly one solution.

This submission refutes that conjunction, a necessary part of the original conjecture. It does **not** determine the actual maximum, assert that the maximum-12 clause alone is false, or supply an interpretation of the unspecified unit-group torsion condition. It also proves the contradiction when parameters are restricted to nonzero integers. No primitive-solution or cube-free-parameter restriction is present in the original or added here.

## Contents

- `ORIGINAL.md`: unchanged bilingual problem statement.
- `report.tex`, `report.pdf`: complete mathematical argument and formalization correspondence.
- `lean/Solution.lean`: proof using cardinalities of the actual integer solution subtypes.
- `lean/Inspect.lean`: displayed theorem types and axiom inspection for source-authored declarations.
- `lean/Audit.lean`: verification-only inventory and transitive proof-dependency audit.
- `verify.py`, `test_verify.py`: portable verification and adversarial controls.
- `VERIFICATION.md`, `verification/`: verification results and provenance.

The main endpoints are `Conjecture1735.conjecture_false` and `Conjecture1735.nonzero_conjecture_false`. The positive structural theorem is `Conjecture1735.maximum_twelve_implies_infinite_maximizers`.

## Reproduce

Use Lean **4.19.0**, Git, and Python 3. The checked-in Lake manifest pins Mathlib **v4.19.0** (`c44e0c8ee63ca166450922a373c7409c5d26b00b`) and all eight transitive packages. Python uses only its standard library.

Prepare those nine clean Git dependency checkouts and their Lean 4.19.0 build cache. With Lean's normal toolchain manager and network access, the usual initial setup from this submission folder is:

```sh
cd lean
lake exe cache get
cd ..
```

The verified runs used already prepared pinned checkouts. Dependency download/bootstrap was not part of those offline runs. Preserve the checked-in manifest; the verifier rejects wrong revisions or modified tracked dependency files.

Then run from this submission folder:

```sh
python3 verify.py
python3 test_verify.py --compiled-controls
```

Both commands print the directory containing their complete execution records and create fresh temporary projects. They perform no dependency download. To use an existing neutral dependency directory or a specific Lake executable:

```sh
python3 verify.py --lake /path/to/lean-4.19.0/bin/lake --dependency-root /path/to/packages
python3 test_verify.py --compiled-controls --lake /path/to/lean-4.19.0/bin/lake --dependency-root /path/to/packages
```

The dependency directory must contain `mathlib`, `plausible`, `LeanSearchClient`, `importGraph`, `proofwidgets`, `aesop`, `Qq`, `batteries`, and `Cli`. Optional `--output /new/directory` preserves records at a specified new path. The compiled negative tests intentionally print failed audit commands; the overall test command must exit successfully and its `result.json` must say `PASS`.

For direct Lean inspection after dependency preparation:

```sh
cd lean
mkdir -p logs
lake build
lake env lean -DwarningAsError=true Solution.lean
lake env lean -DwarningAsError=true Inspect.lean
lake env lean -DwarningAsError=true Audit.lean
```

`Audit.lean` writes its inventories into `logs/`, so create that directory for a direct build. The Python runners create it automatically. There is no finite numerical search supporting the mathematics: the scaling, zero-fiber, cardinality, and infinitude arguments are all proved in Lean.

The report is a standalone standard LaTeX document. Compile `report.tex` with a LaTeX engine to regenerate its PDF. The supplied PDF was compiled and every page was visually inspected. All reported checks are local contributor checks, not a claim of maintainer acceptance.
