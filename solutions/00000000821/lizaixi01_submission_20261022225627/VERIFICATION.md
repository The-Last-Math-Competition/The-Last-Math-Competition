# Verification

The frozen Main.lean passed a new root build in a separate Lean 4.33.0 project. Public dependency artifacts were reused from the task-owned bank, whose source Git commits were checked against every manifest pin. The new Main did not have a preexisting compiled artifact.

- lake build +Main: exit 0; 2172 jobs, Main newly built.
- lake env lean -DwarningAsError=true Check.lean: exit 0; all eleven audited declarations depend only on propext, Classical.choice and Quot.sound.
- lake env leanchecker --fresh Main: exit 0; 326.5069 seconds. This is official-kernel replay, not a separately implemented kernel.
- The two-page PDF was rendered at 110 dpi and both pages visually inspected. Text bounds are within the A4 page, and the final LaTeX log has no overfull boxes.
- A separate supervising Codex agent read the original and final source, including the nonzero condition, quotient functions, continuity, smooth coordinate pullback, derivatives and actual attained maxima. This is AI semantic review.

Structured evidence binds the Main source hash and log hashes to exact commands and exit codes. The mathematics is specifically the standard positive-Laplacian eigenvalue reading on the fixed flat circle; the report explicitly describes the coordinate formalization and the alternative frequency convention that is not claimed.
