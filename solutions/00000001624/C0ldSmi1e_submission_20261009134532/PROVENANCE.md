# Author provenance and independence

The author began with only the six files under `/private/tmp/tlmc1624-author-input`:
`ORIGINAL.md`, the English and Chinese rule files, `lean-toolchain`,
`lake-manifest.json`, and `SHA256SUMS.json`. The five manifest-listed file hashes were
verified before their mathematical content was used. Exact copies are in `source/`.
`records/input-verification.json` records this initial check and all nine package pins.
The final replay repeats these checks.

All author files were created in a new `/private/tmp/tlmc1624-author` directory. No
source-assessor notes, selector notes, other problems or submissions, repository solution
history, existing task chats, root operational files, or mathematical internet searches
were read. No other mathematical author was consulted. Parent messages communicated
workflow status and later reviewed the author's own frozen outputs; no external proof
or construction was supplied or used. The parent's subsequent LaTeX report was not read
by the author. Mathematical reasoning and the gap construction were developed from the
literal source and standard real-set definitions.

The only mathematical library was the permitted neutral standard library exposed under
`/private/tmp/tlmc-standard-library-419`. Its nine package HEAD revisions exactly match
the supplied manifest; tracked sources were clean at initial inspection and final replay.
The exposed directories are aliases into preexisting standard package checkouts. Only
those package directories were used; no sibling project files or solutions were read.
The Mathlib pin is `c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0).

The runtime was the permitted Lean 4.19.0 distribution under
`/private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64`. Final replay records the actual
version text and binary hashes. The package's final top-level manifest name is
`conjecture1624`; the original neutral manifest's name `tlmc934` is preserved in the
source copy. All nine package records are byte-for-byte equal as parsed JSON objects.
The Lake requirement uses the same `v4.19.0` input reference as the supplied Mathlib
record, and the manifest pins its exact commit.

`records/standard-library-reads.json` records source search scopes, the exact source
ranges explicitly displayed, and hashes of source files whose content was displayed.
The author additionally used Lean's `#check` and `#print` on ordinary library and runtime
APIs; the complete probe inputs and outputs are retained in the development archive.
A search for runtime source files found that this runtime installation does not include
the queried `.lean` files; API inspection therefore used the permitted runtime's compiled
declarations. No substitute external source was consulted.

The final audit lists the full imported module set and the full mathematical declaration
dependency closure. `records/import-fingerprints.json.gz` fingerprints every imported
compiled artifact and each available corresponding source. This records the exact
reused library artifacts and does not claim a fresh source rebuild of Mathlib or Lean.

The core was mathematically frozen after the warnings-as-errors check and successful
Lake build. Its SHA-256 remains
`f2135c4b339236755e8b6fd6dd23e7685d7831dbdbad3f2d9aaf924f5e4a7487`.
All later changes were separate challenge proofs, verification tooling, documentation,
and archive packaging. Historical failures were preserved rather than removed.
