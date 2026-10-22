# Verification

The frozen source passed a new root build in a separate Lean 4.33.0 project. Every dependency Git commit in the task-owned public bank matches the manifest pin. Main was newly compiled from this package source.

- `lake build +Main`: exit 0, 2337 jobs, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0, seventeen transitive axiom audits; only propext, Classical.choice, Quot.sound.
- `lake env leanchecker --fresh Main`: exit 0, 339.8147 diagnostic WSL seconds. Official kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at 100 dpi and visually checked by worker and supervising AI agent; no overfull boxes.
- Full formal chain, report and source scope independently reviewed by a separate supervising Codex agent.

Main SHA256: `e9c0d6de88af6aa65a39fa22fd23415d9e9c0ea254d6ff59b8d63ea1a9dde7d6`. Structured receipts bind source, commands, exit codes and logs. The production runner uses the same bounded isolated process-group helper as the completed experiment; one heavy process at a time. This selective production case is not an additional experimental sample.

The actual maximum is defined over all caps in Mathlib Projectivization of K^7. The construction and its cardinality are proved before the maximum lower bound. Both an actual O(q^2) error and the stated relative O(q^-1) expansion are negated on unbounded odd prime fields, with all eventual/error-function quantifiers. No finite instance replaces an asymptotic argument, and no published cap bound is assumed. No sorry, native_decide or additional axiom is used. Organizer acceptance is pending.
