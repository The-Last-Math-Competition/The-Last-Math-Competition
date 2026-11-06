# Verification

The frozen source passed a new root build in a separate Lean 4.33.0 project. Every dependency Git commit in the task-owned public bank matches the manifest pin. Main was newly compiled from this package source.

- `lake build +Main`: exit 0, 2008 jobs, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0, ten transitive axiom audits; only propext, Classical.choice, Quot.sound.
- `lake env leanchecker --fresh Main`: exit 0, 264.5142 diagnostic WSL seconds. Official kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at 100 dpi and visually checked by worker and supervising AI agent; no overfull boxes.
- Full formal chain, report and source scope independently reviewed by a separate supervising Codex agent.

Main SHA256: `1789d21e0d8fe1c022d5b496e2958a87edfa6eb5515b666210d0ee36c3149415`. Structured receipts bind source, commands, exit codes and logs. The production runner uses the same bounded isolated process-group helper as the completed experiment; one heavy process at a time. This selective production case is not an additional experimental sample.

The real analytic chain is fully formalized, unlike prior PR189's natural-number-only Lean file. Both exact decimal and inclusive three-decimal rounding interpretations are refuted for all real constants. No random-graph limit is assumed or claimed proved. No sorry, native_decide or additional axiom is used. Organizer acceptance is pending.
