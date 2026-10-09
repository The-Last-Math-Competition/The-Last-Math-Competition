# Reviewer entrypoint for the completed package

Use `verify.py` as the principal executable verification entrypoint. The immutable
`README.md`, `VERIFICATION.md`, and `verify.sh` describe the mathematical author's
earlier core stage. They remain accurate records of that stage; the completed
package adds this guide, independent hardened verification, adversarial tests,
and a report supplied by the package integrator.

The 43 files named in `CORE-SHA256SUMS.json`, and that manifest itself, are preserved
byte for byte. Its SHA-256 is
`41f401cdaea862da9247638deb6da15ded9ab350b13710ce7b71273ae8f6ff3e`.
The proof source SHA-256 is
`c519a1bba9351c813496d043ef8db4dd4ce3d287f4f5c69a715d84730d4e92e9`.
The report is an additional artifact and requires mathematical and visual review;
the program does not claim to perform that human review.

## Run the complete verification

Requirements: Python 3.11 or later, Git, and Lean **4.19.0** with the matching `lake`
executable beside `lean`. Supply the nine dependency checkouts pinned by the frozen
`lake-manifest.json`, with the compiled Mathlib dependency cache available. A normal
project's `.lake/packages` directory is suitable. Keep the lockfile unchanged when
preparing dependencies. The supplied proof's existing compiled artifacts are never
used as proof verification evidence.

From this submission directory, use a new log directory:

```sh
python3 verify.py \
  --lean /absolute/path/to/lean-4.19.0/bin/lean \
  --dependencies /absolute/path/to/the/nine/package/checkouts \
  --logs /absolute/path/to/new-review-logs
```

The dependency directory must contain `mathlib`, `plausible`, `LeanSearchClient`,
`importGraph`, `proofwidgets`, `aesop`, `Qq`, `batteries`, and `Cli`. The verifier
checks every exact revision and verifies that each checkout has no tracked source
changes. The checkouts and compiled standard-library cache are the upstream
dependency trust boundary; this tool rebuilds all submission proofs, not all of
Mathlib. Some pinned packages, such as an unused `Cli`, need no compiled library.

Do not enable `PYTHONOPTIMIZE` or run Python with `-O`: the principal entrypoint
rejects either condition. Its checks use explicit exceptions, and this guard also
keeps the immutable author's assertion-based auxiliary checks enabled.

Success requires exit status zero and the final `PASS` summary. Each subprocess
has a separate output log and a command/status JSON receipt. Any nonzero exit,
missing expected output, unknown axiom, unsafe declaration, changed frozen input,
incorrect dependency, or declaration inventory discrepancy fails verification.
The log destination must not exist, so previous evidence cannot be overwritten.

## What the entrypoint checks

1. It validates the frozen manifest and all 43 files against their SHA-256 values,
   enforces exactly nine dependency pins and clean tracked source, and verifies the
   actual Lean runtime version.
2. In a temporary project it replays `lakefile.lean` with warnings as errors,
   builds `Solution.lean` into a fresh output directory, then independently replays
   the mathematical source again with warnings as errors. It preserves the input
   source bytes throughout.
3. An independently generated Lean inspector identifies owned declarations by
   their actual defining module. It includes generated proof and equation helpers,
   checks declaration safety and kind, and uses `Lean.collectAxioms` on every
   declaration. It separately walks every referenced constant in declaration
   types and bodies, including opaque bodies, rejects unsafe constants, and permits
   only `propext`, `Classical.choice`, and `Quot.sound` as axioms.
4. The JSON output must have valid begin/end markers, unique complete records,
   a complete transitive-name inventory, and an exact match to the reviewed
   `owned-declarations.json`. Coverage is based on names and module ownership,
   not merely a hard-coded total of 36.
5. It compiles and executes the frozen `Audit.lean` with warnings as errors and
   checks that its owned names and complete transitive-name inventory agree with
   the independent audit. `Audit.lean` is inspection infrastructure; it adds no
   mathematical declarations to `Solution`.
6. It checks the exact registered hashes of `independent-review/IndependentAudit.lean`
   and `independent-review/ReviewChecks.lean`, copies their source bytes into the
   disposable project, and compiles/runs both with warnings as errors in the fresh
   proof environment. It checks the supplemental audit's complete owned and
   transitive inventories against the principal audit and retains the new logs.
   The archived independent review evidence is never overwritten. An additional
   active Lean source without registration, or a modified inspector, is rejected.
7. It runs the frozen `check_inputs_and_pins.py`, and then executes the complete
   frozen `verify.sh` in the disposable project. Thus the original Lake build,
   source replay, and audit also run. The original script's output-writing behavior
   never overwrites archived core logs. Its audit output is checked again.
8. It runs every adversarial test in `test_verifier.py`, then rechecks frozen file
   hashes, supplemental hashes, and the complete source inventory. There are no numerical mathematical experiments or additional
   mathematical computation programs required by this proof.

The `--discover` option exists solely to inspect a candidate's declaration
inventory. It does not print a certification `PASS`; reviewers should use the
normal command against the already reviewed inventory shipped here.

## Adversarial checks

The tests include real Lean compilation of valid and deliberately invalid small
fixtures. They reject a `sorry` warning, a false proof, a custom axiom, an unsafe
declaration, and native certification introducing `Lean.ofReduceBool` and generated
unsafe helpers. Parser and policy tests also reject malformed or missing JSON,
missing summaries, inconsistent counts, duplicate declarations, missing owned
helpers even after the reported count is repaired, incomplete transitive output,
altered dependency pins, a missing package, a changed frozen source, a wrong Lean
version, optimized Python execution, an unregistered supplemental Lean source,
and a changed registered inspector hash. A valid fixture passes, and nested
comments mentioning forbidden words are handled without false positives.

To run only the verifier's test suite:

```sh
python3 test_verifier.py --lean /absolute/path/to/lean-4.19.0/bin/lean
```

## Engineering evidence and development history

`engineering-logs/discovery-01` records the initial complete discovery run:
36 owned declarations and 30,946 transitive declarations, matching the author
audit. Its original 29-test suite passed. The reviewed inventory includes
`Conjecture934.L2._proof_1`, two `inclusionLinear` proof helpers,
`phase_L2_summable._proof_4`, and `term.eq_1`.

`engineering-logs/final-01` records a successful hardened run after adding explicit Lake
configuration replay, cross-checking the original audit's full output and names,
and additional adversarial cases; its 32 tests passed. `engineering-logs/final-02`
passed with a 33-test suite,
including actual native-certification rejection, and test bytecode generation
disabled. It finished with exit status zero: all nine subprocess stages passed,
all 33 tests passed, all 36 owned and 30,946 transitive declarations passed both
audits, and every frozen core hash remained unchanged.

The completed package additionally ships the independent review's two active
inspection sources. `engineering-logs/final-03` is the definitive run that includes
their registered, hash-bound source replays and the corresponding 35-test suite.
It finished with exit status zero: all 11 subprocess stages and all 35 tests passed;
all three audits agreed on 36 owned and 30,946 transitive declarations; the 43
frozen core files, the supplemental sources, and the integrator's report hashes
remained unchanged.
The generated principal inspection source is retained as
`generated-audit-source.txt` so it is reviewable without becoming another active
Lean module.

`engineering-logs/final-03/run-summary.json` records the final receipt, and
`ENGINEERING-SHA256SUMS.json` inventories the additive engineering files. That
inventory excludes itself and the separately managed report assets; it does not
replace the frozen mathematical core manifest.

During development, an initial ad hoc dependency-check command had an unmatched
parenthesis and did not run. After that invocation was corrected, the first
dependency probe rejected `Cli` because it has no compiled library in this cache.
The runner was corrected to enforce all nine pins and clean-source checks while
requiring compiled libraries only for actual imports; Lean source replay enforces
the import closure. No proof or audit requirement was weakened, and no frozen
mathematical source was edited. The initial 29 adversarial tests passed on their
first run. Expected failures from invalid fixtures are successful negative tests,
not proof failures. The author's earlier failed attempts remain in immutable
`logs/` with their original explanations in `VERIFICATION.md`.
