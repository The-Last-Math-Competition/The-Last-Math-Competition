INDEPENDENT ENGINEERING REVIEW — CONJECTURE 00000000161

Result: PASS for the frozen Lean contribution.

This record certifies an actual independent clean build and engineering audit,
not a full competition submission approval. Statement interpretation, the
separately prepared mathematical report/PDF, eligibility, and publication are
separate reviews. The frozen author package itself contained no LaTeX/PDF.

Scope and provenance
--------------------
The reviewer read the original bilingual conjecture and both rules files before
the proof sources. The exact input manifest, frozen manifest, archive, and all
10 frozen payload files matched the supplied SHA256 values. Those files were
checked again after verification and remained unchanged. Only conjecture 161,
its authorized inputs, the frozen contribution, and pristine pinned Lean and
Mathlib dependencies were inspected. No public proof, other conjecture, solution
history, selector record, or chat/agent roster was consulted.

The author archive was extracted into a new independent project. No author's
compiled proof objects were copied. A separate copy-on-write mirror of stock
Mathlib and its eight transitive dependencies supplied pristine source and
existing stock cache objects. The missing stock module
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card was compiled in that mirror.
All nine exact Git revisions and 7,507 tracked file SHA256 hashes matched before
and after, and the shared stock module's missing object remained absent. This
review does not claim to rebuild every stock dependency from source.

Lean was 4.19.0, arm64-apple-darwin23.6.0, commit 6caaee842e94. Mathlib was
c44e0c8ee63ca166450922a373c7409c5d26b00b, with all dependency revisions taken from
the byte-identical neutral manifest. Exact pins and binary/source hashes appear
in engineering_summary.json and result.json.

Checks completed
----------------
The submitted verify.py was fully read and run successfully in the independent
project. Its clean build compiled both mathematical modules and the missing stock
cardinality module. A separate direct clean Lake build was also captured with
separate stdout/stderr and an explicit exit code. All four submitted Lean files,
including lakefile.lean and Audit.lean, passed warningAsError=true replay.

The full source inspection found no sorry, admit, native_decide, custom axiom,
unsafe source declaration, custom elaborator/tactic, or trust-setting bypass.
The cardinality bridge uses the stock general linear group, orderOf, Lagrange's
theorem, and Matrix.card_GL_field. The counting event and original-claim
definitions were printed and inspected. No auxiliary numerical result is claimed
or needed; the only submitted auxiliary executable is the verifier, which ran.

The submitted audit covers all 14 named theorems. IndependentAudit.lean prints
complete types and axioms for all 29 logical declarations: the 14 theorems,
5 definitions/abbreviations, 1 inhabited instance, and 9 generated logical
proof/equation helpers. No ellipsis occurs in the captured full-types output.

Discover.lean enumerates declarations by their originating mathematical module
and walks both type and value dependencies. The complete closure contains 19,737
constants. Its axiom set is exactly {propext, Classical.choice, Quot.sound}; no
unsafe or partial declaration occurs in this logical closure.

Two normal compiler runtime stages,
Conjecture161.primeIndexInhabited._cstage1 and ._cstage2, are inventoried separately
and excluded from logical roots. They are not authored proof declarations and do
not occur in the logical closure. They are not silently asserted to be safe
logical declarations. The initial broad inventory tried to traverse these runtime
stages and encountered the compiler-internal _obj. After classifying runtime
stages, the logical traversal completed. A separate first pretty-print helper
used the unavailable option pp.maxDepth; that option was removed and the helper
passed. Both failed helper attempts and all corrected runs remain in the complete
local evidence. Neither was a failure of a submitted Lean file.

Portable replay
---------------
Prerequisites: the frozen source project, its exact pinned dependencies already
provisioned in .lake/packages, and Lean/Lake 4.19.0 on PATH. Place this directory
anywhere and run, replacing PROJECT and OUTPUT with suitable local paths:

  python3 replay_extended.py --project-root PROJECT --output-dir OUTPUT

OUTPUT must be fresh. The script removes only PROJECT/.lake/build, then builds,
strictly replays all four submitted Lean files, compiles the two audit helpers,
checks every axiom and logical dependency, and checks all dependency revisions
and tracked source bytes again. It never downloads dependencies. It does not
modify source files. The audit helpers can also be run from the project directly:

  lake env lean -DwarningAsError=true /absolute/path/IndependentAudit.lean
  lake env lean -DwarningAsError=true /absolute/path/Discover.lean

The portable verifier itself was tested successfully using this exact invocation
with the pinned runtime directory prepended to PATH:

  python3 /private/tmp/tlmc161-engineering-review/public-verification/replay_extended.py --project-root /private/tmp/tlmc161-independent-engineering --output-dir /private/tmp/tlmc161-engineering-review/portable-replay

Evidence layout
---------------
commands.jsonl records the successful portable replay's exact argument vectors,
working directory, exit code, duration, and stdout/stderr SHA256 digests. Selected
build, strict-source, and full-type logs are included. supplemental_commands.jsonl
records the submitted verifier and import-resolution inspection. The author's
verifier combines its child streams; author_verifier_replayed.log preserves that
combined transcript, while its own process stdout/stderr are stored separately.

kernel_closure.stdout.gz is a lossless gzip of the entire successful closure
trace, not a summary. engineering_summary.json supplies both compressed and
uncompressed byte counts and hashes. The full trace is 9,594,057 bytes and the
gzip is 861,384 bytes. It decompresses exactly to the raw recorded stdout.

Repeated large dependency inventories and routine Git-output files are not
duplicated in this compact public subset. Their hashes are bound by
RAW_EVIDENCE_SHA256.json and the before/after inventory hashes in
engineering_summary.json; all raw local receipts remain under
/private/tmp/tlmc161-engineering-review. In particular, commands whose routine
dependency output is omitted here still have their actual stream hashes recorded.
The exact original inputs and frozen archive are retained in that local record.

PUBLIC_SHA256.json covers every other file in this public verification directory.
