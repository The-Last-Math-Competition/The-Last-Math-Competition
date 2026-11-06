# Verification

The frozen source passed a new root build in a separate Lean 4.33.0 project. Every dependency Git commit in the task-owned public bank matches the manifest pin. Main was newly compiled from this package source.

- `lake build +Main`: exit 0, 1685 jobs, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0, twenty-two transitive axiom audits; only propext, Classical.choice, Quot.sound.
- `lake env leanchecker --fresh Main`: exit 0, 247.1761 diagnostic WSL seconds. Official kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at 100 dpi and visually checked by worker and supervising AI agent; no overfull boxes.
- Full formal chain, report and source scope independently reviewed by a separate supervising Codex agent.

Main SHA256: `7c71432abdd105a9eb8b1a97a3d8cba3dcc876f4deed1f57d9541d6ce7d0b626`. Structured receipts bind source, commands, exit codes and logs. The production runner uses the same bounded isolated process-group helper as the completed experiment; one heavy process at a time. This selective production case is not an additional experimental sample.

The source uses the actual integer Away localizations at all primes. Module.rank over the integers is proved one for each summand and three for each triple, with rational embeddings ensuring torsion freeness. The finite product is explicitly equivalent to the actual finite DirectSum, whose full submodule is proved pure. Genuine residue homomorphisms separate p-divisibility from q-divisibility, excluding every additive-group isomorphism between different prime cases. The actual NonemptyAddEquiv quotient is infinite; every finite complete catalog is impossible. No sorry, native_decide or additional axiom is used. Organizer acceptance is pending.
