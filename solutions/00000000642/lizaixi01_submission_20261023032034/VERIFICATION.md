# Verification

The frozen source passed a new root build in a separate Lean 4.33.0 project. Every dependency Git commit in the task-owned public bank matches the manifest pin. Main was newly compiled from this package source.

- `lake build +Main`: exit 0, 1781 jobs, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0, nineteen transitive axiom audits; only propext, Classical.choice, Quot.sound.
- `lake env leanchecker --fresh Main`: exit 0, 242.7968 diagnostic WSL seconds. Official kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at 100 dpi and visually checked by worker and supervising AI agent; no overfull boxes.
- Full formal chain, report and source scope independently reviewed by a separate supervising Codex agent.

Main SHA256: `c793f981efd3dfdf4424111d4d9f1c499c48f8a499ffd2ca1f9fe3a56e4b8ca4`. Structured receipts bind source, commands, exit codes and logs. The production runner uses the same bounded isolated process-group helper as the completed experiment; one heavy process at a time. This selective production case is not an additional experimental sample.

The source defines the actual Artin B2 and B3 groups, verifies the standard generic matrix model relations and nonzero determinants, and constructs their GL homomorphisms. A genuine positive stabilization changes determinant1 to tq3; these independent-variable rational functions are proved unequal, and arbitrary basis conjugacy preserves the obstruction. The standard generic Krammer/LKB identification is documented by the primary source, not re-proved as a configuration-space homology theorem in Lean. No sorry, native_decide or additional axiom is used. Organizer acceptance is pending.
