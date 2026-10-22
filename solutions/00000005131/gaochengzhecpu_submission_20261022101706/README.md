# Conjecture 00000005131 — Disproof

For the complex zero matrix of order two, algebraic multiplicity is two, but the exact worst eigenvalue displacement under induced infinity norm perturbations of radius epsilon is epsilon and the exact pseudospectral Lebesgue area is pi epsilon squared. Therefore the source's sharp powers based on algebraic multiplicity are false.

The source also mentions maximal Jordan block size. The paper openly acknowledges that the corrected version based consistently on maximal Jordan block size is compatible with the example; a big-O-only reading is likewise not refuted. The condition-number and lattice clauses are not addressed.

Lean proves actual characteristic-polynomial root multiplicity, the exact disk pseudospectrum over all admissible complex matrix perturbations, attained worst displacement, actual Lebesgue area, and negations of the universal lower bounds required by the two claimed sharp scaling laws. Main results: Conjecture5131.not_multiplicity_area_law and Conjecture5131.not_multiplicity_response_law.

From lean/: `lake build`, then `lake env lean -DwarningAsError=true Main.lean`. Lean 4.19.0 and the Mathlib revision are pinned in the project metadata. Only propext, Classical.choice and Quot.sound occur in the axiom reports.

Developed by a delegated AI agent with a self-review; the coordinating agent reviews it separately. No external independent review is claimed. The coordinating agent performs fresh build and PDF visual verification before publication. See verification/SELF_REVIEW.md and verification/SOURCE_PROVENANCE.md.
