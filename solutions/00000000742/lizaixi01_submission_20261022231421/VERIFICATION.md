# Verification

The frozen proof passed a fresh Main build in a separate root Lean project, using task-owned public dependency artifacts checked against the manifest's exact Git commits.

- `lake build +Main`: exit 0; 1995 jobs; Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0; all eleven audited declarations depend only on propext, Classical.choice and Quot.sound.
- `lake env leanchecker --fresh Main`: exit 0; 290.3093 seconds. This is official-kernel replay, not a separately implemented kernel.
- Both PDF pages were rendered at 100 dpi and visually checked. The final LaTeX log has no overfull boxes; the text stays within A4 page bounds.
- A separate supervising Codex agent checked both counting interpretations and the full Lean source.

Main SHA256: `adf6996609afafaff98638466d53f70820b5943af673ea7b3f57d3291a1c002c`. Structured receipts bind that source to commands, return codes and log hashes. The proof concerns the actual 2-adic integers, actual distinct functions and actual closed minimal subsets, not merely finite quotient computations or conjugacy classes.
