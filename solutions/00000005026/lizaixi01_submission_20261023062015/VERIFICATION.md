# Verification

The frozen source passed a new root build in a separate Lean 4.33.0 project. Every dependency Git commit in the task-owned public bank matches the manifest pin. Main was newly compiled from this package source.

- `lake build +Main`: exit 0, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0, fifteen transitive declaration axiom audits (13 theorems and two constructions); only propext, Classical.choice, Quot.sound.
- `lake env leanchecker --fresh Main`: exit 0, 144.6935 diagnostic WSL seconds. Official kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at 100 dpi and visually checked by worker and supervising AI agent; no overfull boxes.
- Full formal chain, report and source scope independently reviewed by a separate supervising Codex agent.

Main SHA256: `8b4b05c9510cf996914fb9c3f4c0c46fc8749b02f3d51ed24278e2ca70b1369e`. Structured receipts bind source, commands, exit codes and logs. The production runner uses the same bounded isolated process-group helper as the completed experiment; one heavy process at a time. This selective production case is not an additional experimental sample.

The proof uses actual FirstOrder empty-language syntax, Sentence.Realize and Language.Equiv. The genuine two-binder sentence existsxforally(y=x) characterizes singleton Unit even when empty structures are allowed. All actual language interpretations are quantified; uniqueness of interpretation data is proved. Exact Fin2 equality-body indices, binderCount2 and maximum allocated contextWidth2 certify this specific syntax uses at most two bound variables. A separate forallforall sentence covers the syntactically universal reading under explicit Nonempty-model convention. Only the unqualified globalfourvariablelowerbound under the source custom definition is refuted; no different rich target or restricted encoding optimum is claimed. Context width is not a general minimum reusable variable count, nor zero free-variable count. All13theorems and two constructions receive15 audits. Full original bilingual source preserved. No sorry, native_decide or additional axiom. Organizer acceptance is pending.
