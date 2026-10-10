# Disproof of conjecture 00000004110

Submitted by **@lizaixi01** with OpenAI Codex assistance for mathematical
reasoning, Lean formalization, reports, independent semantic review and packaging.
The separate semantic reviewer is an AI agent. Organizer acceptance is pending.

## Result and exact scope

Every ordinary subdivision of the actual four-claw K1,4 has continuous ordered and unordered configuration spaces homeomorphic, hence genuinely homotopy equivalent, to those of the original graph for every particle count. The proof constructs endpoint-gluing realizations, insertion maps with continuous inverses, arbitrary path replacements, incidence relabeling/reorientation and the actual permutation quotient. Thus the source's necessary assertion that the four-claw is its smallest n=2 separation example is false. This disproves the unchanged conjunction without imposing finiteness on the original unrestricted graph existential. That existential fragment and the all-n homology condition are not separately claimed decided. The standard continuous configuration and independent finite-path subdivision conventions are explicit and referenced in the report and source scope.

Final target: `P4110FourClaw.no_ordinary_four_claw_ordered_separation`. Both ordered and unordered negations and the
ordinary-subdivision coverage theorem are mechanically checked and included.
Read `subdivision_invariance.pdf`, its unchanged LaTeX source, `source-scope.md`
and `report.md` for the complete argument and original-source correspondence.
The named smallest example must itself be an example; excluding its necessary
inequivalence witness refutes the conjunction. This logical step does not rely
on assuming anything about the unrestricted infinite-graph existential.

## Reproduction

Install the toolchain in `lean/lean-toolchain` (Lean 4.33.0), enter `lean/`,
and run `lake build +FourClaw`. All seven local imported modules are included.
The Git manifest pins Mathlib and all dependencies. After building, a fresh
official replay is `lake env leanchecker --fresh --verbose FourClaw`.
Compile `subdivision_invariance.tex` with a compatible LaTeX installation.

The frozen package passed the actual Root Lake build, exact theorem-type and
transitive-axiom checks, LaTeX/PDF checks, separate original-first semantic
review, all-page PDF inspection and official fresh kernel replay before its
local promotion. The public files are exact byte copies of that package.
To preserve the user's concurrent experiment, this publication audit checks
those source/config/report hashes and prior receipts, and views the existing
rendered PDF pages. It runs no new local compilation, replay, rendering or
dependency download and writes no experiment files or caches. A cold build on
a separate machine was not tested here. Only standard Lean axioms are used;
no sorry, native_decide, unsafe proof mechanism or extra axioms are present.

## Frozen provenance and attribution

All 15 frozen materials are byte-identical, including seven Lean modules,
toolchain/config/lock, bilingual original, prose reports, LaTeX and PDF.
Added files are this publication note, LICENSE, copied evidence and SHA256.json.
Copied evidence replaces local machine paths with placeholders. Raw receipt
SHA256: `9de5bcde5f7407ace25d14bd952766de92a89caee2236dfe39639ebb9702d8be`; raw mechanical receipt SHA256:
`9292be4c9c4e4c302eca7b7543941b6273ae503519cdc0382a0846f838247fe7`; raw final semantic review SHA256:
`04fa8a59dfc38c80ffb71a41e25c45e533859d674de4c1d22caf520794e3c87b`. SHA256.json lists every other public file.

Historical reports describe local development and refer to external worker
receipts. The complete public proof compiles from the supplied Lean sources
and exact Git dependencies using the command above. No RuntimeGuard script,
private author .olean, worker environment or experiment directory is required.
Standard graph/configuration definitions are credited to the references in
the report, source scope and semantic review, including Diestel and Wawrykow.
No new mathematical discovery or worldwide priority is claimed.

## Submission eligibility

At official commit `9b795e7a94a6076e49a65a6489e1caf9153abd23`, both solved flags are false and there is no
solution folder or solution-folder commit history for 4110. All 944
historical PRs were checked in every state, including previous filenames.
The large PR #267 was covered by complete merge-base/head tree comparison
beyond the 3,000-file API cap, bound to its unchanged revisions. No matching
prior or pending submission was found. Eligibility is rechecked before upload.
