# Disproof of conjecture 00000000252

The counterexample is the simple graph K2: two vertices joined by one edge.
It is connected and both vertices have degree one. Any permitted labeling
assigns 1 to the only edge, so both vertex sums equal 1. Thus it is not antimagic.

This disproves the conjecture as written. No claim is made about a version
excluding K2. The source conjecture and organizer-maintained metadata are unchanged.

## Contents

- `proof.tex`: complete argument and explanation of the formalization.
- `proof.pdf`: compiled document.
- `lean/`: standalone Lean 4.19.0 project with no external dependencies.

## Reproduce

With Lean 4.19.0 installed, run:

```sh
cd lean
lake build
lake env lean Conjecture252.lean
```

The final theorem is `Conjecture252.conjecture_false`. Its statement negates
the universal claim for arbitrary finite simple graphs, using explicitly
defined connectivity, absence of isolated vertices, and antimagic labeling.
The file also prints its axiom dependencies. No `sorry`, custom axiom,
`native_decide`, or external theorem library is used.

Compile the PDF with `pdflatex -halt-on-error proof.tex` or `tectonic proof.tex`.

## Attribution and source

Proof and formalization prepared by Codex, an AI assistant, on behalf of the
submitting GitHub account. No human affiliation is asserted.
Source: `conjectures/00000000252.md`, upstream commit
`95acb520ec5607c826b8a997b1ef2fc82d6f7c57`.
