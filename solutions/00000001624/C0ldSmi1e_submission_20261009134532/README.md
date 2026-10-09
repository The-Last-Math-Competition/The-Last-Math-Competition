# Conjecture 00000001624: verified author core

This project disproves the literal real-spectrum statement: a positive-measure Cantor
subset of the real line cannot have no internal spectral gaps. The exact bilingual source
and rules are in `source/`; `REPORT.md` gives the mathematical argument and
`SOURCE-MAPPING.md` makes the semantic bridge explicit.

## Contents

- `Conjecture1624.lean`: the frozen mathematical core (3 definitions, 10 named theorems).
- `Verification.lean`: 8 kernel-checked semantic and boundary challenge theorems.
- `Audit.lean`: executable audit tooling, never imported into either proof module.
- `scripts/replay.py`: complete local rebuild, source checks, audit, and fingerprint replay.
- `scripts/check_stale_audit_rejection.py`: a negative integration challenge that confirms
  a successful no-op audit cannot reuse an old PASS report.
- `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`: Lean 4.19.0 project with all nine
  exact dependency pins retained from the supplied manifest.
- `records/dependency-audit.json.gz`: complete owned/generated/transitive declaration
  graph, per-owned-declaration axiom results, and all imported module names.
- `records/import-fingerprints.json.gz`: SHA-256 of every imported `.olean` and every
  available corresponding source file. Missing bundled runtime source files are marked
  `null`; compiled artifacts are always fingerprinted.
- `records/replay-result.json` and `records/replay-*.log`: final successful clean replay.
- `attempts/*.lean.txt` and numbered historical logs: preserved development snapshots,
  including failures. These are plain archival text, are not imported, are not build roots,
  and are not claimed to compile. See `attempts/README.md` for the exact outcomes.
- `PROVENANCE.md` and `records/standard-library-reads.json`: input isolation and actual
  standard-library inspection record.
- `DELIVERY-MANIFEST.json`: explicit inclusion list and SHA-256 for every delivered file
  except that self-referential manifest itself. Local build products and plain copies of
  the two compressed JSON records are excluded from delivery.

## Build and replay

Use Lean **4.19.0** and the nine pinned standard-library packages. With those packages
installed at `.lake/packages`, the ordinary build is:

```sh
lake build
lake env lean -DwarningAsError=true Conjecture1624.lean
lake env lean -DwarningAsError=true Verification.lean
lake env lean -DwarningAsError=true Audit.lean
```

The Lake configuration treats warnings as errors for both proof roots. The explicit
Lean invocations additionally make that setting visible in the replay record. For a
complete replay, pass the directory containing the matching `lean` and `lake` binaries:

```sh
python3 scripts/replay.py --lean-bin /path/to/lean-4.19.0/bin
```

When the packages are already available in another directory, the optional
`--stdlib-root /path/to/pinned-packages` creates links only for missing package entries.
The replay requires exactly the five original input checksums and their original values,
and permits only package-name normalization in the working dependency manifest. It
validates every package revision and tracked-source cleanliness, and rejects
any mismatch with the exact supplied pins. It removes and rebuilds **only this project's**
`.lake/build`, rechecks both proof files and the audit, and records real command exit codes.
Before the audit runs, it deletes the prior generated plain report and then requires a
newly created regular nonsymlink report. It does not rebuild the pinned standard library
or download mathematical material.

The author ran:

```sh
python3 scripts/replay.py \
  --lean-bin /private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64/bin \
  --stdlib-root /private/tmp/tlmc-standard-library-419
```

The replay regenerates the two plain JSON audit records and deterministic gzip archives
with timestamp zero. The shipped compressed files decompress to the exact plain-content
SHA-256 recorded in `records/replay-result.json`. Paths in fingerprint and replay records
identify the author's environment; another environment will have different path strings
and timing values even when the proof sources, library pins, and dependency declarations
agree. Do not demand byte equality of path-bearing records across different machines.

After a successful replay has regenerated the plain audit seed, the negative integration
challenge can be rerun with the same `--lean-bin` and `--stdlib-root` arguments:

```sh
python3 scripts/check_stale_audit_rejection.py \
  --lean-bin /path/to/lean-4.19.0/bin \
  --stdlib-root /path/to/pinned-packages
```

No additional numerical computation is needed for this disproof. The development
archives are evidence, not auxiliary computations required by the theorem. The only
accepted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

This is the author's mathematical core package. The parent workflow supplies the final
LaTeX/PDF, independent review, publication eligibility checks, and repository packaging.
