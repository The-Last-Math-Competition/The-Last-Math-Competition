# Disproof of Conjecture 00000008356

A triangle with all three edge lengths 1/2 has integral cycle generator (1,1,1), length Gram determinant 3/2, and exactly three ordinary spanning trees. The covolume convention gives sqrt(3/2), also not 3.

## Scope

Disproof of the stated equality between the metric Jacobian lattice determinant and the ordinary unweighted spanning-tree count, without a unit-edge-length normalization. This does not dispute weighted matrix-tree formulas.

## Formal correspondence

The Lean code constructs the actual SimpleGraph K3 and counts its spanning-tree subtype, constructs the oriented edge-incidence linear map, proves its integral kernel has a one-element Basis, evaluates the positive length pairing on that actual basis, and computes the Gram determinant and covolume contradiction.

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
