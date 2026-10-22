# Verification

The frozen source passed a new root build in a separate Lean 4.33.0 project. Every dependency Git commit in the task-owned public bank matches the manifest pin. Main was newly compiled from this package source.

- `lake build +Main`: exit 0, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0, twenty-five transitive axiom audits; only propext, Classical.choice, Quot.sound.
- `lake env leanchecker --fresh Main`: exit 0, 265.1926 diagnostic WSL seconds. Official kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at 100 dpi and visually checked by worker and supervising AI agent; no overfull boxes.
- Full formal chain, report and source scope independently reviewed by a separate supervising Codex agent.

Main SHA256: `9679ca4219a6ab06384f1971808ef597b248d5a0d1c4fd6c6020c21cd91f8a97`. Structured receipts bind source, commands, exit codes and logs. The production runner uses the same bounded isolated process-group helper as the completed experiment; one heavy process at a time. This selective production case is not an additional experimental sample.

The proof uses actual positive Collatz inverse fibers rooted at1, for both full and shortcut maps. Each positive nonmultiple3 has three distinct genuine depth7 children of the same kind; an actual recursive injection into the true finite fibers proves cardinality at least3^m at7m. Forward invariance verifies every intermediate pruned-path node. The exact c=sqrt4/3 has c^7<3, and a genuine geometric limit refutes all eventual constants and cutoffs, giving true Mathlib IsBigO negations. Leaves mean frontier nodes of the standard finite-depth unfolded tree; repeated labels across different levels are permitted. No first-hit cycle-deleted convention or Collatz conjecture is asserted. No sorry, native_decide or additional axiom. Organizer acceptance is pending.
