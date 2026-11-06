# Disproof of Conjecture 00000009624

The actual bilateral three-symbol full shift is a surjective shift-commuting homeomorphism with minimal sliding-block radius one. Its genuine dynamical cylinder covering number is 3^n, so Mathlib topological entropy is at least log3>log2, violating the proposed universal radius bound.

## Scope

Refutes h<=r log2 under the exact source, which imposes no binary-alphabet restriction. Both inverse and forward rules have radius one and minimality is proved. Only a lower bound on total topological entropy is needed or claimed; the later extremal-family and spectrum clauses are not separately analyzed.

## Formalization

Lean uses the full compact product configuration space Z->Fin3 with actual discrete-product uniformity, a genuine shift homeomorphism and inverse, local-rule radius and minimality. A real uniform entourage observes coordinate zero, and actual iterates identify its dynamical balls with length-n word cylinders. Explicit read/extend maps prove every word occurs, every finite dynamical cover needs at least 3^n centers and an actual cover of exactly that size exists. Mathlib coverMincard, exponential-growth and coverEntropy definitions give the entourage entropy log3 and genuine total entropy lower bound. The final theorem directly negates the universally quantified radius-entropy law. No external symbolic-entropy bridge or proxy definition is used. An exact supplementary verifier checks finite words, orbit traces, inverses and both local rules.

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
