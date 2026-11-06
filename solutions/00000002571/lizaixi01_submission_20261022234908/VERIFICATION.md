# Verification

The frozen source passed a new root build in a separate Lean 4.33.0 project using public dependency artifacts from a task-owned bank whose Git commits match every manifest pin. Main was newly compiled from this package's source.

- `lake build +Main`: exit 0; 2246 jobs; Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0; all seventeen audited declarations depend only on propext, Classical.choice and Quot.sound.
- `lake env leanchecker --fresh Main`: exit 0; 297.4739 seconds. This is official-kernel replay, not a separately implemented kernel.
- Both PDF pages were rendered at 100 dpi and visually checked. The final LaTeX log has no overfull boxes.
- A separate supervising Codex agent reviewed the mathematical definitions and complete formal chain.

Main SHA256: `a51b05a8064266920fc38294fa7f2fc66d23548807e9bee3858c0a9cfaca3ca7`. Structured receipts bind the source, commands, return codes and logs. The actual minimum protocol cost and real matrix ranks are proved, not assigned numerical values. Both common matrix encodings are covered. The Bob-output model has one-bit witnesses and no zero-bit protocol; the rank-one contradiction does not concern regularized or asymptotic bounds.
