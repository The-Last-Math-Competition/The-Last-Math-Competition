# Verification

The frozen source passed a new root build in a separate Lean 4.33.0 project using public dependency artifacts from a task-owned bank whose Git commits match every manifest pin. Main was newly compiled from this package's source.

- `lake build +Main`: exit 0; 2584 jobs; Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0; all fourteen audited declarations depend only on propext, Classical.choice and Quot.sound.
- `lake env leanchecker --fresh Main`: exit 0; 455.9917 seconds. This is official-kernel replay, not a separately implemented kernel.
- Both PDF pages were rendered at 100 dpi and visually checked. The final LaTeX log has no overfull boxes.
- A separate supervising Codex agent reviewed the mathematical definitions and complete formal chain.

Main SHA256: `5d1d472445346645f54041b70861a7f0c3dc3a6caed116dc047d44b5fe4a5f44`. Structured receipts bind the source, commands, return codes and logs. The proof covers ordinary ordered partial sums as well as HasSum, explicitly matches the original n>=1 indexing, and excludes a subset of cardinality 2^aleph0. It does not rely on a default sum for divergent series.
