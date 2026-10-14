# Verification of conjecture 00000002899

The independent source build and declaration audit passed. Semantic review
checks the exact bilingual statement separately, retaining the report's
coefficient-one interpretation limit. This symbolic argument needs no auxiliary
numerical search or computation.

| Independent check | Result |
| --- | --- |
| Frozen source/configuration files | 11 |
| Owned Lean modules | 8, all reached by the default target |
| Pinned dependency packages | 9 |
| Pinned tracked package files | 7,507 |
| Stable stock Git indexes | 9 |
| Imported module identities | 2,942 |
| Retained command receipts | 63 |
| Owned declaration roots | 39, all safe |
| Named capstones and definitions | 25 |
| Reachable declaration graph nodes | 8,326 |
| Generated unsafe runtime helpers | 0 |
| Allowed axioms | `propext`, `Classical.choice`, `Quot.sound` only |
| Operational controls | 1 accepted and 5 rejected as intended |

The independent verifier starts with an empty owned-source output directory and
private clones of generic pinned dependencies. No author-produced compiled
artifact is copied. The default `lake --no-cache --wfail build` succeeds.
Each of the eight owned modules is then replayed directly in dependency order
with `-DwarningAsError=true`; `lakefile.lean` is separately replayed under the
same warning policy. Every frozen input remains unchanged. All generic imports
were already cached; no missing Mathlib source needed compilation for this run.

The inspector selects declarations by originating module, including the global
`finite_field_square_count` and generated proof declarations. It follows
constants in types, values, opaque values, recursor rules, and inductive and
constructor relations. All 39 safe roots and all 25 required declarations have
only the three permitted foundational axioms, with no missing or unsafe
dependency. There are no authored axioms, incomplete proofs, `native_decide`,
or trust bypasses. The independent graph checker recomputes the recorded
closures; source compilation supplies Lean kernel checking. The graph checker
is not a second independent proof kernel.

The six fresh controls are an ordinary safe theorem (accepted), an unrelated
custom axiom (rejected), an axiom reached through an opaque value (rejected),
`sorry` (rejected both by strict compilation and dependency inspection),
`native_decide` (rejected for compiler-trust axioms), and an explicitly unsafe
definition (rejected). Expected failures in these controls are successful
tests of the rejection policy, not failures in the submission.

The included generic hardening script also passed seven current-run fixtures:
unexpected owned output, an ambiguous import, untracked package source,
changed cached import, changed frozen source, changed exact pin, and multiline
forbidden-token/comment/string handling. Its receipt and results are in
`evidence/reviews/generic-hardening-*.json`. It uses synthetic files and does
not rebuild the mathematical proof. To repeat it, use another new directory:

```sh
python3 verification-tools-v2/test_hardening.py /absolute/path/to/NEW-fixtures
```

The source/configuration review checks every active file: ordinary mathematical
definitions and proofs, `#print axioms`/`#print`/`#check`, and declarative Lake
configuration only. It finds no authored file/network IO, initialization,
custom elaborator, unsafe declaration, or bypass setting. Author helper scripts
only invoke Lean and record development checks; their final mathematical work
is integrated into the independently replayed project. Earlier failed attempts
remain in the historical archive and are not active project modules.

The author's separate full build, source-only replay, dependency audit, and
`lean --trust=0 -DwarningAsError=true Conjecture2899/AxiomAudit.lean` replay all
exit successfully. They are retained as author evidence, not substituted for
the independent run. One root verifier invocation initially supplied CLI
arguments in the wrong order and stopped before writes or proof execution.
The corrected documented invocation produced the complete successful run;
the invocation correction is recorded separately.

## Reproduce the independent audit

The included generic tools use macOS `/bin/cp -cR`. Supply a stock Mathlib
v4.19.0 checkout, its eight locked generic subdependencies and cached imports,
and Lean 4.19.0. The stock source is verified against pinned Git objects and
private copies. Use a fresh output directory that does not already exist.
Python assertions must be enabled; do not use `python -O`.

```sh
package_dir="$PWD"
stock_dir="/absolute/path/to/pinned-stock"
lean_bin="/absolute/path/to/lean-4.19.0/bin"
new_output="/absolute/path/to/NEW-review-output"
python3 "$package_dir/verification-tools-v2/verify.py" verify \
  "$package_dir/lean" \
  "$package_dir/evidence/frozen-review-manifest.json" \
  "$stock_dir" "$lean_bin" "$new_output" \
  "$package_dir/evidence/expected-pins"
python3 "$package_dir/verification-tools-v2/check_audit_graph.py" \
  "$new_output/declaration-audit.json"
```

Review the new result and any generated runtime helpers explicitly. This run
had none. The supplied manifest and toolchain must remain unchanged. The simpler
portable `lake build` and per-module replay commands are in `README.md`.

## Evidence and trust limits

The engineering archive contains all retained non-project verification records:
63 command receipts and stdout/stderr files, complete declaration graph,
controls, stock-source/cache inventories, imported identities, runtime and
build-output identities, selected freeze, copied driver and PATH safeguards.
The author archive preserves inventoried development sources, scripts, plans,
freeze, results, and logs. Archive manifests record every member's size and
SHA-256; members have normalized metadata and contain no dependency cache or
compiled Lean artifact. Historical absolute paths record the actual execution
environment and are not portable build prerequisites.

Extract an evidence archive into a new directory using Python's safe data
filter, then run the graph checker on the extracted engineering graph:

```sh
python3 - evidence/engineering-records.tar.gz /absolute/path/to/NEW-records <<'PY'
from pathlib import Path
import sys, tarfile
target = Path(sys.argv[2])
target.mkdir(parents=True, exist_ok=False)
with tarfile.open(sys.argv[1], 'r:gz') as archive:
    archive.extractall(target, filter='data')
PY
python3 verification-tools-v2/check_audit_graph.py \
  /absolute/path/to/NEW-records/engineering/declaration-audit.json
```

Cached dependency imports are matched to the independently supplied pinned
stock; all Mathlib was not rebuilt. Runtime binaries and libraries are hashed
before and after the run; Lean was not bootstrapped. Runtime imported artifacts
are recorded, not authenticated by an independent compiler bootstrap. PATH
wrappers guard against unexpected network tools and Git writes but are not
operating-system network isolation. Source/configuration review, mathematical
semantic review, report comparison, and all-page PDF inspection are separate
checks; their final records are included in `evidence/reviews/` and
`evidence/report/`.

The public eligibility evidence is a dated metadata search with stated coverage
limits. It does not establish novelty against every mathematical publication,
private branch, deleted item, or alternate formulation. The result is a personal
submission of a verified disproof of the displayed bound; it makes no claim of
new mathematics or maintainer acceptance.
