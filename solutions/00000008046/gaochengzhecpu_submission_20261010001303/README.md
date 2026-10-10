# Disproof of Conjecture 00000008046

The indicator of [0,1] has a graph given by finite polynomial conditions, hence is semialgebraic and subanalytic. Its actual Fourier integral at xi=n+1/2 has norm 1/(pi xi), and no eventual Ce^(-c xi) bound with c>0 is possible.

## Scope

Disproof of the implication subanalytic implies exponential Fourier decay in the stated class of definable compactly supported functions. The source imposes no continuity or smoothness hypothesis.

## Formal correspondence

Lean proves an explicit real-polynomial Boolean description of the function graph and actual compact support; it computes the genuine Mathlib Fourier integral by a Bochner interval integral, proves its exact values at half-integer frequencies, and rules out every eventual exponential bound for arbitrary C,R and c>0.

The LaTeX paper states the exact bridge between the mathematical terminology and
the formal objects, including any standard definitions used on paper.

## Reproduce

This submission is self-contained, with Lean 4.19.0 and commit-pinned Mathlib.
From `lean/` run:

```text
lake exe cache get
lake build
lake env lean -DwarningAsError=true Main.lean
```

`lake exe cache get` is needed only when the pinned dependencies are not cached.
The proof is checked in a fresh directory without reusing its own build outputs.
Only the standard axioms `propext`, `Classical.choice`, and `Quot.sound` are permitted.
There are no proof placeholders, added axioms, or numerical oracles.
Run `tectonic main.tex` to regenerate the PDF. No auxiliary numerical scripts are required.

The complete paper is `main.pdf`, its editable source is `main.tex`, and the
exact bilingual conjecture is `SOURCE.md`. Build logs and hashes are in
`verification/BUILD.json`; the native compiler record is `verification/NATIVE_LATEX.json`.
Source provenance and self-review are preserved in the same directory.
