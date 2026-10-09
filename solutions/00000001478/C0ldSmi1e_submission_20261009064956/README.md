# Conjecture 00000001478: disproof

The nuclear-norm unit ball of complex 2 × 2 × 2 tensors is not a polynomial image of a genuine cone. The proof uses a bounded real coordinate: a real polynomial bounded on a cone has its value at the origin everywhere on that cone, whereas the nuclear ball contains the zero tensor and a unit basis tensor with distinct coordinate values.

`ORIGINAL.md` preserves the exact bilingual conjecture. `report.pdf` and its editable source `report.tex` give the complete argument and its precise scope. The necessary cone-representation clause is disproved; this does not assert that every other SDP formulation of the nuclear norm is impossible. The formalization also treats the literal attained-minimum reading, without assuming global attainment.

## Formal sources

- `lean/NuclearNorm.lean`: the full complex tensor space, all finite decompositions, their scalar cost, the infimum definition, coordinate bounds, exact zero and basis tensors, removal of zero terms, and the attained-minimum variant.
- `lean/PolynomialCone.lean`: ray substitution, polynomial constancy on a cone, and representation of complex-coefficient polynomials by real and imaginary polynomials.
- `lean/Solution.lean`: arbitrary finite parameter dimensions, arbitrary polynomial degrees, the general cone obstruction, and the genuine 4 × 4 positive-semidefinite linear-pencil case. The principal theorem is `TLMC1478.conjecture00000001478_false`.
- `lean/AuthorAudit.lean`: the author's unchanged self-check of all 54 explicit declarations.
- `lean/Audit.lean`: the separate engineering audit of all 75 compiled declarations owned by the three mathematical modules, including generated declarations, and their complete type-and-value dependency closure.

The mathematical files and author self-check are byte-identical to author freeze revision 2. The original configuration is preserved in `verification/author-original-lakefile.toml`; the packaged configuration only appends a separate `Audit` library. The author's default targets are unchanged. The full verification explicitly builds all five libraries.

## Reproduce the verification

Requirements: Python 3 with its standard library, Git, Lean/Lake 4.19.0, and the nine standard Git dependencies at the exact revisions in `lean/lake-manifest.json`, with a compatible Lean 4.19.0 dependency build cache. `verification/pinned-dependencies.json` is the same manifest. The runner checks all nine revisions and tracked-file cleanliness before and after execution. It does not download or repair dependencies.

From this package directory, supply the absolute path to Lake and a directory containing the nine dependency checkouts. Use new output directories:

```sh
python3 -B verify.py --lake /absolute/path/to/lean-4.19.0/bin/lake --dependency-root /absolute/path/to/packages --output /absolute/path/to/new-proof-results
python3 -B test_verify.py --compiled-controls --lake /absolute/path/to/lean-4.19.0/bin/lake --dependency-root /absolute/path/to/packages --output /absolute/path/to/new-control-results
```

The dependency root has children named `mathlib`, `plausible`, `LeanSearchClient`, `importGraph`, `proofwidgets`, `aesop`, `Qq`, `batteries`, and `Cli`. If they are already available under `lean/.lake/packages`, omit `--dependency-root`. With a configured Lean 4.19.0 installation, `--lake` may also be omitted.

`verify.py` creates a fresh project, copies only the frozen source/configuration, links the verified standard dependencies, builds all five libraries, and replays each source with warnings treated as errors. It compares the newly measured declaration names, owning modules, safety, kinds, types, direct dependencies, and transitive axioms with the frozen complete inventory. It checks every safe root through both types and values, including imported theorem proof values. No authored compiled output is reused.

For a direct inspection in a prepared `lean` directory:

```sh
cd lean
mkdir -p logs
lake build NuclearNorm PolynomialCone Solution AuthorAudit Audit
lake env lean -DwarningAsError=true NuclearNorm.lean
lake env lean -DwarningAsError=true PolynomialCone.lean
lake env lean -DwarningAsError=true Solution.lean
lake env lean -DwarningAsError=true AuthorAudit.lean
lake env lean -DwarningAsError=true Audit.lean
```

The portable runner provides the additional frozen-input, dependency, and inventory checks and is the recorded reproduction path. `python3 -B test_verify.py` runs only the Python unit controls; use `--compiled-controls` for the compiled rejection fixtures and dependency controls.

`VERIFICATION.md` gives measured results, control counts and skips, provenance, and the included evidence layout. These are local verification results. Acceptance remains the competition maintainers' decision.
