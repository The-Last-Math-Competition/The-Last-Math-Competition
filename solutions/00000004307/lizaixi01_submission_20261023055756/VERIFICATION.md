# Verification

The frozen source passed a new root build in a separate Lean 4.33.0 project. Every dependency Git commit in the task-owned public bank matches the manifest pin. Main was newly compiled from this package source.

- `lake build +Main`: exit 0, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0, nine transitive axiom audits; only propext, Classical.choice, Quot.sound.
- `lake env leanchecker --fresh Main`: exit 0, 149.8419 diagnostic WSL seconds. Official kernel replay, not an independently implemented kernel.
- The single PDF page rendered at 100 dpi and visually checked by worker and supervising AI agent; no overfull boxes.
- Full formal chain, report and source scope independently reviewed by a separate supervising Codex agent.

Main SHA256: `9dee5610734c6c3cc9df0446fc487e9328dba236e9a962b865547b0d9aa6c74a`. Structured receipts bind source, commands, exit codes and logs. The production runner uses the same bounded isolated process-group helper as the completed experiment; one heavy process at a time. This selective production case is not an additional experimental sample.

The proof refutes the literal same-rank necessary numerical conjunction at k3,p5, legalpositive andoddprime with gcd3,4=1, even under the optional additional index restriction1<=k<=p-2. Every candidate rank value and function is quantified, for arbitrary characteristic-zero semirings and explicit natural/integer/cardinal instances. No Euler system or higher-K group is artificially defined; no actual rank is assigned or computed. A different corrected piecewise formula is outside this refutation. Full original bilingual source preserved. No sorry, native_decide or additional axiom. Organizer acceptance is pending.
