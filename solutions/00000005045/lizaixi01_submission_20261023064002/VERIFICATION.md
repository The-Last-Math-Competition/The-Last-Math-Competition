# Verification

The frozen source passed a new root build in a separate Lean 4.33.0 project. Every dependency Git commit in the task-owned public bank matches the manifest pin. Main was newly compiled from this package source.

- `lake build +Main`: exit 0, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0, all46 named local declaration audits (28 theorems plus18 definitions/abbreviations/instances); only propext, Classical.choice, Quot.sound, or no axioms.
- `lake env leanchecker --fresh Main`: exit 0, 159.7238 diagnostic WSL seconds. Official kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at100 dpi and visually checked by worker and supervising AI; no overfull boxes.
- Full formal chain, exact original source scope and report independently reviewed by a separate supervising Codex agent.

Main SHA256: `5458874bef5b613fe52dd38b4c7c441fcc488ff74ca3b5ab66e60da58a749810`. Structured receipts bind source, commands, exit codes and logs. The production runner uses the same bounded isolated process-group helper as the completed experiment; one heavy process at a time. This selective production case is not an additional experimental sample.

The formal proof uses actual finite cycle-copy graphs, actual walk-length<=2 balls and induced rooted GraphIsos, a genuine Hanf vertex bijection and actual finite rooted-type fiber equivalences. Equal orders and all vertex degrees2 are proved. Every threshold and size cutoff admits such graphs but no global GraphIso; a connected C12 component cannot inject into one C6. All46 named declarations, including proof-bearing definitions and instances, receive explicit axiom audits. No finite/infinite cardinal fallback or assigned counts is used. Only the source-defined necessary radius2 Hanf-to-global-isomorphism transfer is refuted; no undefined table entries are invented and the actual Hanf bounded-rank FO theorem is not refuted. Full original bilingual source preserved. No sorry, native_decide or additional axiom. Organizer acceptance pending.
