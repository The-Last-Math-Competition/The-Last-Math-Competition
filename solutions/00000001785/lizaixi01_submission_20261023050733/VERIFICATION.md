# Verification

The frozen source passed a new root build in a separate Lean 4.33.0 project. Every dependency Git commit in the task-owned public bank matches the manifest pin. Main was newly compiled from this package source.

- `lake build +Main`: exit 0, 1966 jobs, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0, fifteen transitive axiom audits; only propext, Classical.choice, Quot.sound.
- `lake env leanchecker --fresh Main`: exit 0, 258.1754 diagnostic WSL seconds. Official kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at 100 dpi and visually checked by worker and supervising AI agent; no overfull boxes.
- Full formal chain, report and source scope independently reviewed by a separate supervising Codex agent.

Main SHA256: `fe66af311f3e6f1b1a58cfbf0798463d88d7da102c3ef046ff3a12a2982f28ae`. Structured receipts bind source, commands, exit codes and logs. The production runner uses the same bounded isolated process-group helper as the completed experiment; one heavy process at a time. This selective production case is not an additional experimental sample.

The proof uses actual finite sums of disjoint interval indicators, and actual countable interval covers with constant pieces, to derive finite/countable restricted images. The exact formula max(1,2c)*pi is injective and has uncountable image on the actual positive window (1/2,1). Formal restriction lemmas propagate this obstruction to all positive parameters. Every real function C fails the source necessary step-function and formula conjunction. No actual OT optimum is assigned or computed; no independent extension theorem or piecewise-linear replacement is claimed false. No sorry, native_decide or additional axiom is used. Organizer acceptance is pending.
