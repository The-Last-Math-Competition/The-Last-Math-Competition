# Verification

The frozen source passed a new root build in a separate Lean4.33.0 project with a task-owned public dependency bank whose Git commits match every manifest pin. Main was newly compiled from this package source.

- `lake build +Main`: exit0, 1827 jobs, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit0, sixteen audited declarations use only propext, Classical.choice, Quot.sound.
- `lake env leanchecker --fresh Main`: exit0, 266.8694 seconds. This is official-kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at100dpi and visually checked; final LaTeX log has no overfull boxes.
- A separate supervising Codex agent reviewed the entire formal chain and report.

Main SHA256: `51b152edcc975f5a413d6e955cf111f61919c0ce7d00150198b2c697ea8d744c`. Structured receipts bind source, commands, exit codes and logs. Minimum complete arcs are selected from actual projective point sets and proved to be minima. The universal lower bound applies to all finite fields; the real-library fallback branch does not replace the geometric argument. No sorry, native_decide or additional axiom is used. Organizer acceptance is pending.
