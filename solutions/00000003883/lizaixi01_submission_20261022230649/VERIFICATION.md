# Verification

The frozen source passed a new root build in a separate Lean 4.33.0 project. Public dependency artifacts were reused from a task-owned bank, whose source Git commits were checked against every manifest pin. Main was built afresh from the source included in this package.

- `lake build +Main`: exit 0, 1918 jobs, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0. All eleven audited declarations depend only on propext, Classical.choice and Quot.sound.
- `lake env leanchecker --fresh Main`: exit 0, 273.6785 seconds. This is official-kernel replay, not a separately implemented kernel.
- The two-page PDF was rendered at 100 dpi and both pages visually inspected. Text bounds are inside the A4 page; the final LaTeX log has no overfull boxes.
- A separate supervising Codex agent reviewed the original, the standard-definition primary source, and the full formal chain. This is AI semantic review.

The main source SHA256 is `9cd485a99f91456123c666d9a2701b7079d9d9a46dc2f6ece8a758fbc720079c`. Structured records bind each command and log hash to this source. The formalized invariant is the standard F-pure threshold at the origin of F2[x,y], computed from actual Frobenius powers. The general equivalence with test-ideal definitions is cited, not claimed as newly formalized.
