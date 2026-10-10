# Disproof of Conjecture 00000007915

Every nonbacktracking row of a cubic graph has two possible successors. Therefore det(I-uB) is nonzero for |u|<1/2, whereas the conjectured radius 1/(2 sqrt(2)) is strictly below 1/2. A graph-independent positive separation rules out equidistribution there.

## Scope

Disproof of the unrescaled Ihara-pole equidistribution circle in the source, already for random finite cubic simple graphs. The theorem applies to every finite cubic graph and every subset of its poles, including the nontrivial poles.

## Formal correspondence

Lean constructs the nonbacktracking matrix on actual SimpleGraph.Dart objects, bounds successor cardinality from actual vertex degrees, proves the Hashimoto determinant has no zeros in |u|<1/2 using its actual kernel, and proves positive distance between every denominator root and every point of the claimed circle.

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
