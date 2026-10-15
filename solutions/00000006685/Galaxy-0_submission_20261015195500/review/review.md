# Independent review: TLMC 00000006685

Status: PASS for the actual stated scope: mathematical counterexample with kernel-checked finite certificates and explicit prose geometric/topological bridges. Reviewed 2026-10-15. No claim of fully kernel-formalized real topology.

## Mathematical semantics
The explicit sites are the origin and the four vertices of a tetrahedron, with weights i/100. Strict own-site inequalities prove every cell has nonempty three-dimensional interior. Every pair has three exact rational, noncollinear strict bisector witnesses. These are genuine squared-Euclidean-power inequalities, not assigned adjacency data. The real bridge is valid: rational equalities/inequalities persist under Q → R; strictness gives a relatively open disk in the pair's bisector plane; that plane supports both full-dimensional polyhedral cells, making the intersection a shared facet. Alternatively the certified nondegenerate triangle proves dimension two.

Nondegeneracy is checked in conventional regular-triangulation terms: every four sites affinely independent, no five co-power-spherical, no hidden sites, and pairwise distinct weights. The universal characteristic-zero-field theorem actually excludes real sphere centers, not merely rational ones. The source's phrase “degenerate weights” is not formally defined, so this is necessarily the standard geometric interpretation rather than an exhaustive analysis of an unspecified alternative definition.

The rotation construction uses real K5 directed edges, endpoint-correct reversal, and all six cyclic orders of four incident ports. The independently generated successor permutations have 1, 3, or 5 facial cycles and never 7. The paper explicitly maps a sphere embedding to these cyclic orders and reverse-then-successor facial walks. For connected finite plane graphs, faces correspond to those cycles; Euler would force seven. This is a valid mathematical nonplanarity proof rather than a result-shaped definition. The paper also provides the shorter standard Euler face-length contradiction.

## Formal scope and limitations
Lean certifies finite rational facet witnesses, visibility, affine independence, distinct weights, the field-general no-common-power-sphere obstruction, and a genuine structural facial-decomposition obstruction. Real topology, dimension/facet semantics under Q → R, the identification of topological facial walks with the formal closed-walk partition, and the general embedding-to-rotation/Euler theorem are proved/explained in prose, not kernel formalized. Accordingly, this is a mathematical counterexample with substantial kernel-checked certificates, NOT a fully formalized theorem of real topological nonplanarity. It refutes only the conjecture's planarity conjunct and does not disprove the separate regular-triangulation assertion.

## Independent arithmetic and combinatorics
A separately written Python checker recomputes all 20 ordered-pair, three-point geometric certificates using Fraction arithmetic. Minimum strict margin across all points: 1011/1000. Increasing-order four-site determinants: 4, -4, 4, -4, -16. It independently generates the 6^5 = 7776 cyclic order systems from permutations and directly traverses their facial cycles, rather than copying the Lean lookup table or orbit-minimum implementation. Histogram: 2340 systems with 1 face, 4974 with 3, 462 with 5.

## Final structural proof audit
The final implementation replaces exhaustive global enumeration with a stronger symbolic proof. `FacialBound.ClosedWalk` requires a nonempty walk following the actual successor at every step and closing back to its start. `Decomposition.partition` is a permutation of `List.finRange 20`, forcing every directed edge to occur exactly once. It does not assume a face bound or assigned invariants. `faceStep_ne` and `faceStep_twice_ne` follow from actual dart endpoints and genuine local four-cycles. Hence all facial walks have length at least three, and the total twenty darts give at most six faces. `all_rotation_systems_represented` ensures every family of local cyclic orders is included. A sphere embedding of K5 induces exactly such a partition and would require seven faces. There is no vacuous “planarity” predicate in the formalization.

The independent Python enumeration remains an additional cross-check; the final Lean proof does not depend on enumeration.

## Reproducibility
Final source snapshot and clean compilation products are under `final/`. A clean `verify.sh` build with Lean 4.31.0 succeeds for PowerCells, NoSphere, FacialBound, K5Rotation, and Conjecture6685. Each compiled module is replayed through leanchecker. The axiom audit of main theorems reports only propext, Classical.choice, and Quot.sound; no sorryAx or additional axiom. See final/logs and final/review-build.log.

Additional strict `lean -DwarningAsError=true` compilation PASS for all five modules plus Audit. The final source scan finds no sorry, native_decide, axiom declaration, or unsafe code. The earlier memory-intensive enumeration draft was replaced; it is not the reviewed deliverable.

## PDF visual review
Final PDF has four pages. All pages were rendered and visually inspected. Pages 1–3 are byte-identical PNG renders to previously inspected pages, and changed page 4 was reinspected after bibliography tightening. No clipping, overlap, missing glyphs, broken equations/tables, or orphaned bibliography remain. The explicit formalization scope statement remains present and accurate.

## Hashes and verdict
The exact reviewed files are listed in `final/SHA256SUMS.txt`. Key SHA-256 values:

- K5Rotation.lean: d955b8525a82a7dbd6df0222c67c34942c1fbcae6db530af2d4f2a023ecdcb09
- paper.tex: 6948fee2166bb70bae1380a5cc0745ec437b7d0c67fd9ced1b6bc10239ca19bb
- paper.pdf: faed4fc0d129fbbea5b47bc7e89552261a5b3d177d2b12b3d113864145e78139

PASS applies to the precise scope and limitations above. Competition eligibility/live submission state is not independently reverified by this mathematical audit. No external write or submission was performed.
