# Verification

The frozen source passed a new root build in a separate Lean4.33.0 project with a task-owned public dependency bank whose Git commits match every manifest pin. Main was newly compiled from this package source.

- `lake build +Main`: exit0, 2021 jobs, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit0, sixteen audited declarations use only propext, Classical.choice, Quot.sound.
- `lake env leanchecker --fresh Main`: exit0, 321.1659 seconds. This is official-kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at100dpi and visually checked; final LaTeX log has no overfull boxes.
- A separate supervising Codex agent reviewed the entire formal chain and report.

Main SHA256: `303ad5dc428f9bc6d5736dd3d9dda49f9d0ea0add02d6d47282380377e619ee7`. Structured receipts bind source, commands, exit codes and logs. Actual projective point/kernel incidence, coordinate set cardinality, blocking, tangents and nontriviality are proved from their definitions. The GF9 example has24 points and no Redei line; numerical answers are not assigned as definitions. No sorry, native_decide or additional axiom is used. Organizer acceptance is pending.
