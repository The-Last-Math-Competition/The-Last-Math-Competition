# Verification

The frozen source passed a new root build in a separate Lean 4.33.0 project. Every dependency Git commit in the task-owned public bank matches the manifest pin. Main was newly compiled from this package source.

- `lake build +Main`: exit 0, 2040 jobs, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0, fourteen transitive axiom audits; only propext, Classical.choice, Quot.sound.
- `lake env leanchecker --fresh Main`: exit 0, 265.8141 diagnostic WSL seconds. Official kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at 100 dpi and visually checked by worker and supervising AI agent; no overfull boxes.
- Full formal chain, report and source scope independently reviewed by a separate supervising Codex agent.

Main SHA256: `a3491d24bb72ee296f15a2c8915a73efb4358eac8d577ea4180f0fcc765fe722`. Structured receipts bind source, commands, exit codes and logs. The production runner uses the same bounded isolated process-group helper as the completed experiment; one heavy process at a time. This selective production case is not an additional experimental sample.

The source uses the actual complex unit circle and actual injective plane projection, proving the real crossing set and every underpoint choice empty. The complement is homeomorphic to Circle, so actual arc components are unique. The range of every possible crossing-relator rule on the actual empty crossing type is empty; the resulting actual PresentedGroup is isomorphic to the free group on this arc type and then to the integers. The actual spatial embedding has the prescribed projection and height zero. The infinite finitely generated group and sufficient classical realization contradict the necessary forward implication of the stated iff in the standard Kauffman model. No sorry, native_decide or additional axiom is used. Organizer acceptance is pending.
