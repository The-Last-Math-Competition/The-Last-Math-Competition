# Disproof of Conjecture 00000009278

On G=Z/4Z, the indicator of H={0,2} has Fourier transform twice itself. Both supports equal H and have size two. Its support product four is the global minimum over all nonzero complex functions. H is not a difference set: ordered difference 1 occurs zero times and difference 2 occurs twice.

## Scope

This refutes the stated classification of support-product extremals as difference sets for finite groups. The example is a proper nontrivial subgroup of a cyclic group, and neither the time nor the Fourier support is a difference set, even allowing degenerate parameters. The standard uncertainty lower bound itself is proved, not refuted. Multiplying the Fourier transform by a nonzero normalization constant leaves the example unchanged at the level of supports.

## Formalization

Lean uses actual complex functions on ZMod 4 and Mathlib ZMod.dft. Fourier inversion and a singleton-support argument prove the lower bound for every nonzero function. The actual standard character computes the witness transform; actual support cardinalities and ordered group differences are checked. The final theorem asserts nonzeroness, global minimality and failure of the difference-set property for both supports. All finite checks are kernel checked.

## Reproduction

In `lean/`, run `lake exe cache get`, `lake build`, and
`lake env lean -DwarningAsError=true Main.lean`.
Lean 4.19.0 and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`
are pinned in public-Git project metadata. Only verified official dependency
artifacts are reused; the submitted project is freshly rebuilt.
Run `tectonic main.tex` for the PDF. No auxiliary computation is required.

`SOURCE.md` preserves the exact bilingual source. `verification/` contains
provenance, actual build logs, hashes and review records. The author performed
a separate adversarial self-review; no independent reviewer or subagent was used.
