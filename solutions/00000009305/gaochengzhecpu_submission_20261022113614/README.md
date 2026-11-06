# Disproof of Conjecture 00000009305

Uniform rooting of growing disjoint unions of P3 has the actual constant local weak limit given by uniform rooting of P3. A measurable radius-two cylinder event has mass one in this limit and zero in every law concentrated on vertex-transitive graphs, excluding any such barycentric decomposition.

## Scope

Refutes the transitive-support restriction, even without requiring the component laws to be extreme. The exact source imposes no connectedness requirement on finite approximants or infinitude requirement on root components. No claim that the limiting law is extreme is needed or made.

## Formalization

Lean constructs actual countable connected locally finite SimpleGraphs modulo root-preserving isomorphism, walk-defined induced balls and the cylinder-generated sigma algebra. Actual finite disjoint unions grow without bound. Uniform PMFs on all vertices push forward through actual reachable components to the same law at every size; every cylinder probability therefore converges. The radius-two event reads complete degrees of the root and its neighbors, excluding vertex-transitive graphs without falsely identifying a whole component from a truncated ball. Actual measure-zero and nonnegative Lebesgue integral theorems exclude arbitrary measure-valued barycentric mixtures. An exact exhaustive auxiliary verifier checks all graphs on at most six vertices, the P4 boundary case and forty finite uniform-root laws.

## Reproduction

Inside lean/: `lake exe cache get`, `lake build`, and
`lake env lean -DwarningAsError=true Main.lean`.
Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned.
Compile `main.tex` with Tectonic. Any supplementary root-level Python
programs are run with Python 3; none is a computation oracle for Lean.
The exact bilingual source, provenance, actual fresh-build logs, axiom
audit, artifact hashes and all-page PDF review are included. The author
agent supplied a self-review; the parent reviewed the entire frozen proof
and final artifacts separately. No external independent review is claimed.
