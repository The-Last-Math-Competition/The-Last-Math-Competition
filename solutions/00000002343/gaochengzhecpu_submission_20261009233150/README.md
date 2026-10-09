# Conjecture 00000002343: scalar matrix pencils have no eigenvalue crossings

For one-by-one matrices, the characteristic polynomial of A+tB is X-(a+tb), with derivative one. Every pencil therefore has an empty collision set and zero crossing count. Under every probability law the expectation is zero, contradicting the claimed pi/4 value at n=1.

## Scope

The original equality has no exclusion of n=1 and no asymptotic qualification. The counterexample addresses that admissible dimension for arbitrary complex matrices (hence also real ones) and every probability law, including nondegenerate laws. It does not claim a formula in dimensions n>=2. The absence of any repeated eigenvalue makes the count zero regardless of whether one counts collision parameters, pairs, or transverse crossings.

## Formalization

Lean computes the actual Matrix.charpoly for arbitrary Fin 1 matrices and a real pencil parameter, proves its unique root and separability, and proves that its simultaneous root/derivative-zero set is empty. It proves the Nat.card of this actual empty collision set is zero and evaluates the actual Bochner integral for any sample space, measure, and matrix-valued sample functions. The final theorem refutes the claimed expectation for every probability measure.

## Reproduction

In `lean/`, run `lake build` and `lake env lean -DwarningAsError=true Main.lean`.
Lean 4.19.0 and Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned.
The manifest pins transitive dependencies with public Git URLs and no local paths.
On a new machine, fetch official cached dependencies with `lake exe cache get`.
Run `tectonic main.tex` from the submission directory to rebuild the PDF.
No auxiliary numerical script is required. `SOURCE.md` preserves the exact bilingual source.

The project's own Lean artifacts are rebuilt from scratch; only verified official dependency
artifacts are reused. Actual build commands, source hashes, axiom checks, and PDF inspections
are recorded in `verification/`. Author self-review and parent-agent adversarial review are
separate; no external independent review is claimed.
