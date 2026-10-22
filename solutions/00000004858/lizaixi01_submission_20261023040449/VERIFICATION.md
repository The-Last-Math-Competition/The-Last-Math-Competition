# Verification

The frozen source passed a new root build in a separate Lean 4.33.0 project. Every dependency Git commit in the task-owned public bank matches the manifest pin. Main was newly compiled from this package source.

- `lake build +Main`: exit 0, 1280 jobs, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0, sixteen transitive axiom audits; only propext, Classical.choice, Quot.sound.
- `lake env leanchecker --fresh Main`: exit 0, 169.3230 diagnostic WSL seconds. Official kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at 100 dpi and visually checked by worker and supervising AI agent; no overfull boxes.
- Full formal chain, report and source scope independently reviewed by a separate supervising Codex agent.

Main SHA256: `c7dc0b8a94e5e1b598e25862b909958933e602a5d9491e7470111c101b4ba835`. Structured receipts bind source, commands, exit codes and logs. The production runner uses the same bounded isolated process-group helper as the completed experiment; one heavy process at a time. This selective production case is not an additional experimental sample.

The source uses actual signed integer words and an infimum of all valid word lengths, proving the lower bound and attainment before identifying word distance with the genuine integer metric. The standard four-point Gromov condition with delta zero and torsion freeness are proved for this same group. Actual reduced free-group words are noncommuting; no homomorphism into the integer group can be injective, and no actual subgroup can be isomorphic to the rank-two free group. No sorry, native_decide or additional axiom is used. Organizer acceptance is pending.
