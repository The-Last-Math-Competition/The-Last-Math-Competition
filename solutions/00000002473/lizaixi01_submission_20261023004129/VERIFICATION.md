# Verification

The frozen source passed a new root build in a separate Lean4.33.0 project with a task-owned public dependency bank whose Git commits match every manifest pin. Main was newly compiled from this package source.

- `lake build +Main`: exit0, 1026 jobs, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit0, sixteen audited declarations use only propext, Classical.choice, Quot.sound.
- `lake env leanchecker --fresh Main`: exit0, 154.2727 seconds. This is official-kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at100dpi and visually checked; final LaTeX log has no overfull boxes.
- A separate supervising Codex agent reviewed the entire formal chain and report.

Main SHA256: `209a6ac4f236e1aada465881f24e4297d7ae8526c04e613fa0a68fb5dd6250dc`. Structured receipts bind source, commands, exit codes and logs. The type of all partitions of two is exhaustively classified. Standard rank/crank values and full-universe integer and residue counts are proved from their definitions; numerical answers are not assigned as definitions. No sorry, native_decide or additional axiom is used. Organizer acceptance is pending.
