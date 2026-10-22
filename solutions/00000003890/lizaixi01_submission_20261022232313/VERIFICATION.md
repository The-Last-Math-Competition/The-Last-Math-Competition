# Verification

The frozen source passed a new root build in a separate Lean 4.33.0 project using public dependency artifacts from a task-owned bank whose Git commits match every manifest pin. Main was newly compiled from this package's source.

- `lake build +Main`: exit 0; 1826 jobs; Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0; all fifteen audited declarations depend only on propext, Classical.choice and Quot.sound.
- `lake env leanchecker --fresh Main`: exit 0; 273.2555 seconds. This is official-kernel replay, not a separately implemented kernel.
- Both PDF pages were rendered at 100 dpi and visually checked. Text fits inside A4 page bounds; the final LaTeX log has no overfull boxes.
- A separate supervising Codex agent reviewed the mathematical definitions and complete formal chain.

Main SHA256: `23b364bfe593bb658321ed6af20c6ff7f16816951945934e7f16fdd24d8d8f90`. Structured receipts bind the source, commands, return codes and logs. The Frobenius root is proved least among all qualifying ideals. The test-ideal supremum is proved equal to the literal increasing union, and the infinite jump set is proved for one fixed nonzero proper ideal.
