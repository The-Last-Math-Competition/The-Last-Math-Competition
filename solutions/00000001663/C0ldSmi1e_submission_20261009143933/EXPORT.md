# Bundle boundary

This bundle contains the frozen sources, reports, supplied inputs, pins, verification programs, actual development and final logs, receipts, and archival failed source attempts. It excludes dependency checkout symlinks, dependency caches, Python caches, generated C/IR, and unrelated local artifacts.

Each archived successful run retains only its five small owned `.olean` objects, under the original relative workspace path, so receipt validation can also verify those recorded object hashes. A fresh replay reconstructs a complete new workspace. Dependency caches and runtime binaries must be supplied separately with the recorded pins for strict replay. Portable source review is described in VERIFICATION.md.

Some evidence records contain absolute paths from the original author workspace. They are provenance, not portable instructions. `evidence/ARCHIVED_RUNS.json` maps each original receipt to the bundle-relative path. `evidence/FINAL_RUN.json` uses a relative receipt locator.

`evidence/DELIVERABLE_HASHES.json` inventories all bundled files other than itself. Preserve its hash externally when transferring the bundle. It is a content inventory, not an independent attestation or substitute for fresh verification.
