# Conjecture 00000002187: disproof as written

The exact bilingual claim is preserved in `ORIGINAL.md`. The formalization follows its explicit minimum-edge containment definition. It proves that this attained minimum for the path on n vertices is n − 1, so the normalized minimum tends to 1 and the asserted `(3 + o(1))n` asymptotic is false. It makes no assertion about the differently defined conventional size-Ramsey number.

`lean/Conjecture2187.lean` is the unchanged frozen mathematical source. Its containment predicate is an injective graph homomorphism, its minimum is defined from all attainable finite host-edge counts, and the exact edge count and asymptotic negation are proved. The principal theorem is `Conjecture2187.conjecture_false`. `verification/author-mathematics.md` preserves the author's full correspondence, provenance, domain discussion, and exact treatment of the alternate path-indexing convention.

The author's `lean/AuthorAudit.lean` is preserved unchanged. It checks the entire mathematical owner-module inventory and prints the definitions, theorem types, and axiom dependencies. The additional `lean/Audit.lean` is separate engineering code: it independently inventories all compiled mathematical declarations and traverses their complete type-and-value dependencies, including imported theorem proof values. Mathematical/semantic review is a separate role from both checks.

`report.pdf` and its editable `report.tex` give the supplied complete written argument. Both were copied unchanged from the coordinator's reviewed output.

## Reproduce

Requirements are Python 3 with its standard library, Git, Lean/Lake 4.19.0, and the nine standard Git dependency checkouts at the exact revisions in `lean/lake-manifest.json`, with compatible Lean 4.19.0 build caches. The portable runner performs no dependency download or repair. It checks every exact revision and tracked-file cleanliness before and after execution.

From this package directory, use new output directories:

```sh
python3 -B verify.py --lake /absolute/path/to/lean-4.19.0/bin/lake --dependency-root /absolute/path/to/packages --output /absolute/path/to/new-proof-results
python3 -B test_verify.py --compiled-controls --lake /absolute/path/to/lean-4.19.0/bin/lake --dependency-root /absolute/path/to/packages --output /absolute/path/to/new-control-results
```

The dependency root must contain `mathlib`, `plausible`, `LeanSearchClient`, `importGraph`, `proofwidgets`, `aesop`, `Qq`, `batteries`, and `Cli`. If these are already prepared under `lean/.lake/packages`, omit `--dependency-root`. The default `--lake` is `lake` on the executable search path; use an explicit path to avoid selecting another installation.

The verifier copies the frozen sources/configuration into a new project and rebuilds `Conjecture2187`, `AuthorAudit`, and `Audit`. It replays all three sources with warnings as errors, measures the complete inventory, compares it to the frozen expected inventory, checks the full dependency closure, and verifies that the input bytes remain unchanged. It reuses only the verified standard dependency caches, not compiled candidate modules.

For direct inspection in an already prepared `lean` directory:

```sh
cd lean
mkdir -p logs
lake build Conjecture2187 AuthorAudit Audit
lake env lean -DwarningAsError=true Conjecture2187.lean
lake env lean -DwarningAsError=true AuthorAudit.lean
lake env lean -DwarningAsError=true Audit.lean
```

The portable runner supplies the additional input, dependency, and inventory comparisons. `python3 -B test_verify.py` runs only the Python unit controls; `--compiled-controls` also runs the compiled rejection and dependency controls.

The original author configuration is preserved at `verification/author-original-lakefile.toml`. The packaged configuration appends only a separate `Audit` library; its original default targets remain unchanged. The raw author freeze retains its actual `conjecture_id` key and all 13 original file records. Every mapped file, including the original author logs and failed initial audit-build log, is preserved byte-for-byte and checked by `verify.py`.

See `VERIFICATION.md` for precise measured coverage, control counts and skips, source bindings, and engineering provenance. These local checks do not constitute maintainer acceptance.
