# Conjecture 00000004027: Zero mean does not imply a symmetric rough Levy-area sign law

A genuine planar pure-area rough path has first level zero and second-level increments A(t-s)J, where J is antisymmetric and A takes the values 2,-1,-1 on three equiprobable outcomes. Every entry of its second-level expectation is zero on every real-time interval, while the actual area sign law is constantly 1/3 at +1 and 2/3 at -1. Reflection preserves the entire mean tensor and reverses the sign bias.

## Scope and formal correspondence

The counterexample uses the standard weak geometric step-2 rough-path convention, with a Lipschitz second level and zero first level. The source states no mixing, independence, or nondegeneracy assumptions. All-time mean zero refutes the sufficient direction, including both long-time and small-time interpretations; a reflected pair also rules out an arbitrary functional of the full mean tensor determining signed asymmetry. Smooth-loop approximation at every weaker exponent between 1/3 and 1/2 is explained mathematically, not claimed as a formalized density theorem.

PureArea.IsWeakGeometricHalf explicitly states diagonal conditions, both Chen identities, the shuffle identity, and componentwise 1/2-Holder rough-path bounds. Every condition is proved for the actual two-level increments. The second-level expectation is a Mathlib measure integral with arbitrary real endpoints and both tensor indices. Levy area is extracted from that tensor, and its sign law is an actual measure pushforward of normalized counting measure on Fin 3. Lean proves the complete sign law is constant, its masses are 1/3 and 2/3, reflection symmetry fails, and those masses cannot converge to a common limit along any sequence of nondegenerate intervals. It also proves the mean-only functional impossibility. No existing Mathlib rough-path library or general weak-measure topology is claimed. Supplementary smooth polynomial loops are checked using actual derivatives, interval integrals, and concatenated signature definitions; their integer-endpoint mean calculation is not the primary all-time counterexample.

The main result is `Conjecture4027.PureArea.counterexample`. The defining rough-path
conditions and all-time mean theorem are in that namespace. The older repeated-loop
calculations earlier in the file are supplementary and make only integer-endpoint claims.

Standard terminology is cross-referenced to F. Caravenna, M. Gubinelli, and L. Zambotti,
[Lectures on rough paths](https://www.lpsm.paris/_media/users/zambotti/bookcgz.pdf),
version 14 May 2025, Section 11.4, Lemma 11.9. The identities and estimates required
for this example are proved directly in the submission.

## Files and reproduction

- `main.tex` and `main.pdf`: full counterexample, geometric interpretation, and exact formalization scope.
- `SOURCE.md`: exact bilingual source; its commit and SHA-256 are in `verification/SOURCE_PROVENANCE.json`.
- `lean/`: Lean 4.19.0 project with Mathlib pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- `verification/`: clean-build logs, theorem dependencies, native LaTeX and exported PDF records, and reviews.

Inside `lean/`, run `lake build` and `lake env lean -DwarningAsError=true Main.lean`.
On a new machine, `lake exe cache get` retrieves the pinned official dependency artifacts.
From the submission directory, `tectonic main.tex` reproduces the PDF. No auxiliary
numerical script is required.

Only official commit-pinned dependency artifacts are reused; the submission itself is
built in a fresh directory. The audit excludes proof gaps, added axioms, and native
computation shortcuts. Author self-review and parent review are recorded separately;
no external independent review is claimed.
