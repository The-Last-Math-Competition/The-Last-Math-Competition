# Verification

The frozen source passed a new root build in a separate Lean 4.33.0 project. Every dependency Git commit in the task-owned public bank matches the manifest pin. Main was newly compiled from this package source.

- `lake build +Main`: exit 0, 1801 jobs, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0, twenty-three transitive axiom audits; only propext, Classical.choice, Quot.sound.
- `lake env leanchecker --fresh Main`: exit 0, 246.2943 diagnostic WSL seconds. Official kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at 100 dpi and visually checked by worker and supervising AI agent; no overfull boxes.
- Full formal chain, report and source scope independently reviewed by a separate supervising Codex agent.

Main SHA256: `ac082adf54c808286e31f88f41458073320189889a44937f60a7d60a74a8457e`. Structured receipts bind source, commands, exit codes and logs. The production runner uses the same bounded isolated process-group helper as the completed experiment; one heavy process at a time. This selective production case is not an additional experimental sample.

The source defines the actual Artin B3 quotient and proves the braid relations and determinant-nonzero conditions before constructing both GL group homomorphisms. Actual nonzero vectors certify the complex eigenvalue -3/4 at the legal real parameter 3/4. An arbitrary-basis conjugacy theorem proves the obstruction persists in every basis. Standard reduced and unreduced matrices are attributed to the primary references in the report. No sorry, native_decide or additional axiom is used. Organizer acceptance is pending.
