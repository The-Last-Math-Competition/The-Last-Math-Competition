# Verification

The frozen source passed a new root build in a separate Lean 4.33.0 project. Every dependency Git commit in the task-owned public bank matches the manifest pin. Main was newly compiled from this package source.

- `lake build +Main`: exit 0, 1773 jobs, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0, twenty-four transitive axiom audits; only propext, Classical.choice, Quot.sound.
- `lake env leanchecker --fresh Main`: exit 0, 253.5555 diagnostic WSL seconds. Official kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at 100 dpi and visually checked by worker and supervising AI agent; no overfull boxes.
- Full formal chain, report and source scope independently reviewed by a separate supervising Codex agent.

Main SHA256: `765916d1f4fc45e5cfc9bcbb2bc821fdf6f8e36b384b80a12844e411e88bc7ed`. Structured receipts bind source, commands, exit codes and logs. The production runner uses the same bounded isolated process-group helper as the completed experiment; one heavy process at a time. This selective production case is not an additional experimental sample.

The source uses actual SL2(F2), its natural two-dimensional action, actual linear kernels and actual subgroup closures. Mathlib transvection induction and the F2 coefficient cases prove U/L generate the full group. Their common fixed space is zero and each individual fixed dimension is at most one. The genuine admissible dimension set contains zero, is nonempty and has least element zero before its infimum is evaluated. All fixed spaces of actual natural image subgroups have dimension at most two, so any nonempty image-family minimum is at most two. Thus the printed support value n²-1=3 cannot hold under the source definition. No sorry, native_decide or additional axiom is used. Organizer acceptance is pending.
