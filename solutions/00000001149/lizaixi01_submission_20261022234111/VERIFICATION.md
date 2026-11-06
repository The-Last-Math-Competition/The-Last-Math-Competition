# Verification

The frozen source passed a new root build in a separate Lean 4.33.0 project using public dependency artifacts from a task-owned bank whose Git commits match every manifest pin. Main was newly compiled from this package's source.

- `lake build +Main`: exit 0; 2583 jobs; Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0; all nine audited declarations depend only on propext, Classical.choice and Quot.sound.
- `lake env leanchecker --fresh Main`: exit 0; 408.9244 seconds. This is official-kernel replay, not a separately implemented kernel.
- Both PDF pages were rendered at 100 dpi and visually checked. The final LaTeX log has no overfull boxes.
- A separate supervising Codex agent reviewed the mathematical definitions and complete formal chain.

Main SHA256: `0adbe38a8b5d41d35f30353ec407bc1fdf83b8f5ec1fc4decc527ce10db3872c`. Structured receipts bind the source, commands, return codes and logs. The standard Gaussian quotient is embedded into the actual p-adic fields; no arbitrary fractional-valuation element is assumed rational. The first-term norm contradiction refutes the necessary termwise law without assuming any value of a fusion coefficient.
