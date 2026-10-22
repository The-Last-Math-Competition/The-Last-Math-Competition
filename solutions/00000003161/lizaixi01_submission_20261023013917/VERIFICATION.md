# Verification

The frozen source passed a new root build in a separate Lean4.33.0 project with a task-owned public dependency bank whose Git commits match every manifest pin. Main was newly compiled from this package source.

- `lake build +Main`: exit0, 1946 jobs, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit0, eleven audited declarations use only propext, Classical.choice, Quot.sound.
- `lake env leanchecker --fresh Main`: exit0, 259.8055 seconds. This is official-kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at100dpi and visually checked; final LaTeX log has no overfull boxes.
- A separate supervising Codex agent reviewed the entire formal chain and report.

Main SHA256: `6eae316585cdf0487e971fe3c2fa617da7f792d4afbc611d3d276d3e409f2c58`. Structured receipts bind source, commands, exit codes and logs. The actual support, sensing matrix and all-signal recovery decoder are constructed; the genuine minimum measurement count is proved at most 2, rather than assigned a value. Its logarithmic-bound violation is proved for every positive dimension-independent constant in an underdetermined dimension. No sorry, native_decide or additional axiom is used. Organizer acceptance is pending.
