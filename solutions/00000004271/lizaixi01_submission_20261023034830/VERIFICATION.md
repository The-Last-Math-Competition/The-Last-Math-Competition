# Verification

The frozen source passed a new root build in a separate Lean 4.33.0 project. Every dependency Git commit in the task-owned public bank matches the manifest pin. Main was newly compiled from this package source.

- `lake build +Main`: exit 0, 1390 jobs, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0, twenty-two transitive axiom audits; only propext, Classical.choice, Quot.sound.
- `lake env leanchecker --fresh Main`: exit 0, 176.4629 diagnostic WSL seconds. Official kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at 100 dpi and visually checked by worker and supervising AI agent; no overfull boxes.
- Full formal chain, report and source scope independently reviewed by a separate supervising Codex agent.

Main SHA256: `2a697aef654eba33ab2290cb5b65f110e6567cb29add1c995ec33e5720858616`. Structured receipts bind source, commands, exit codes and logs. The production runner uses the same bounded isolated process-group helper as the completed experiment; one heavy process at a time. This selective production case is not an additional experimental sample.

The source uses actual additive rational automorphisms and their defect homomorphism and fixed subgroup. Finite moved support implies finite defect image; the rational scalar classification forces identity. The finite-index proof uses actual subgroup index and nsmul_index_mem, not an assumed equivalence. The union of the three classes is the identity singleton, so doubling is outside its closure in every T1 automorphism topology and cannot be approximated in any genuine metric interpretation. No sorry, native_decide or additional axiom is used. Organizer acceptance is pending.
