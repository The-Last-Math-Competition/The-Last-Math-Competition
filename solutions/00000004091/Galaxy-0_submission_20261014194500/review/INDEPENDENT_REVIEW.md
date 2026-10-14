# Independent mathematical and source review

14 October 2026 UTC. This is a review performed during submission preparation, not an official competition review or organizer endorsement.

## Mathematical conclusion

The one-particle reduction is valid: no collision condition remains at n = 1, and S1 acts trivially. Evaluation identifies the product and quotient topology with the original graph realization. The two witnesses are finite, simple and connected. K2 is two-colorable and has an edge, hence chromatic minimum 2. C4 has its proper parity two-coloring and also an edge, hence the same minimum. With the listed coherent orientations, their rational incidence kernels are respectively zero and the constant four-coordinate vectors. Their dimensions are 0 and 1. The same input 2 cannot be sent to both values by one function, so no polynomial in chromatic number can supply the claimed invariant at n = 1.

No n >= 2 condition excludes this instance in the source. The conjunction is refuted by its polynomial clause; subdivision invariance itself remains true. The interpretation is the standard geometric realization of a graph, rather than a discrete vertex set. The claimed polynomial is read as one polynomial for each n across graphs; allowing arbitrary separate polynomials for separate graphs would not be a graph-invariant dependence claim.

## Lean source correspondence

The graph structure has real finite vertex/edge sets, endpoint functions, no loops, and no duplicated undirected edge. The incidence map uses the stored endpoint data and exact Rat arithmetic. Its cycle predicate requires vanishing at every stored vertex. The basis certificate quantifies actual edge vectors and requires spanning and unique coefficients, so it is a valid finite-dimensional basis specification, not a numerical Betti label.

The K2 zero-kernel and C4 constant-kernel proofs inspect every required vertex and edge. The coloring certificates give genuine proper maps and rule out every color count below 2. The final theorem applies the universally quantified chromatic-dependence hypothesis to these two graph certificates and derives the unequal values at input 2. No empirical output is trusted by this proof.

The independent `Audit.lean` also checks the graph endpoint data and proves that the C4 kernel cannot have a zero-element basis. A clean build, strict elaboration, nine public/audit theorem axiom prints, and separate kernel replays succeeded. The only reported axioms are Lean's standard logical axioms, as applicable. The Python checks independently confirm the numerical witness calculations.

## Topological bridge and limit

Section 4.1 explicitly builds the finite one-dimensional CW realization from vertices and unit edge intervals. The edge/vertex function spaces identify with cellular chains in their cell bases. The incidence map agrees with the cellular boundary because its vertex coefficient is incoming minus outgoing. With no 2-cells, first cellular homology is the cycle kernel. Hatcher's Theorem 2.35 (printed pp. 139–140), together with the coefficient extension on p. 153, identifies this with singular homology over Q. Section 2 supplies the Conf_1 homeomorphism.

This is a complete paper bridge for the stated witnesses. These topology constructions and comparison results are not formalized in the Std-only Lean project. The package discloses that boundary accurately and does not smuggle the bridge in as a Lean axiom. The mathematical disproof is sound; acceptance of the formalization boundary remains the competition reviewers' decision.

## Earlier rejected submission

PR 292 proposed the same correct path/even-cycle idea using P4/C4. Its only recorded organizer rejection concerns the absence of semantic objects linking the Lean arithmetic to the graph, chromatic number, configuration space, and Betti number. Inspection of the earlier source confirms its concluding theorem merely conjoins integer identities. The current source supplies actual graph/color/incidence-kernel/basis definitions and proofs, while documenting the remaining topological paper bridge. The earlier contribution is credited in the report, README, and comparison document. No claim of a newly discovered counterexample is justified or made.

## Review outcome

No mathematical error or hidden proof admission was found in the packaged graph-cellular disproof or in the stated paper topology bridge. The project is suitable for submission review with its scope explicitly disclosed. This assessment is not a claim that a complete singular-homology/configuration-space formalization has been checked by Lean.
