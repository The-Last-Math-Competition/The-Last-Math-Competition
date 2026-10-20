# Author-agent self-review: 00000005609

Verdict: PASS

Main.lean SHA-256: `8efd0b733bba0ff7a74b400721b4351ea01c013ccf3c92db960e3dc758f3e194`

Author self-review, followed by parent review; no external independent review.

# 5609: three-dimensional packing-covering ratios are unbounded

## Exact source claim being refuted
The conjecture says that the spectrum of the covering-radius/packing-radius ratio over three-dimensional lattices is a closed interval whose endpoints are attained by the cubic lattice. In particular it asserts an attained finite upper endpoint. That assertion is false. We make no claim against its separate statement concerning a minimum at the body-centered cubic lattice.

## Mathematical proof
For every real t>=1 use the full-rank rectangular Euclidean lattice

  Lambda_t = {(t*m,n,p):m,n,p integers}.

It is an additive subgroup. Its displayed three axis generators span R^3. Distinct lattice points have distance at least 1, so it is discrete. A unit vector in the second coordinate is a lattice vector; every nonzero lattice vector has norm at least 1. Thus its packing radius is exactly 1/2.

For any x=(x_0,x_1,x_2), rounding x_0/t, x_1 and x_2 to the nearest integers produces a lattice point z with coordinate errors at most t/2, 1/2, 1/2. Hence

  dist(x,Lambda_t) <= sqrt(t^2+2)/2.

At c_t=(t/2,1/2,1/2), every lattice point differs in those coordinates by absolute amounts at least t/2, 1/2, 1/2. The lower bound matches. Consequently

  r_pack(Lambda_t)=1/2,
  r_cover(Lambda_t)=sqrt(t^2+2)/2,
  gap(Lambda_t)=sqrt(t^2+2).

For every real B, t=max(1,B+1) has gap>B. So no finite upper endpoint exists. More concretely the simple cubic lattice Lambda_1 has ratio sqrt(3), whereas Lambda_4 has ratio sqrt(18)>sqrt(3).

## Actual objects formalized in Lean
- E is Mathlib EuclideanSpace R (Fin 3), not a proxy metric.
- point t z is exactly (t*z_0,z_1,z_2).
- lattice is the actual range in E; latticeGroup supplies its AddSubgroup structure.
- point_injective and the explicit three basis vectors verify the integer coordinate representation.
- separation proves distance>=1 for distinct lattice points.
- lattice_discrete proves the actual subtype carries DiscreteTopology.
- lattice_full_rank proves Submodule.span R (lattice t)=top, through an explicit real decomposition of every vector.
- packingRadii is the set of nonnegative radii with 2r<=every nonzero lattice norm. packing_geometric proves equivalence to 2r<=distance of every pair of distinct lattice points, the usual nonoverlapping-open-ball condition.
- coveringRadii is the set of nonnegative r such that every x lies in some radius-r closed ball about a lattice point.
- packingRadius is actual sSup of packingRadii and coveringRadius is actual sInf of coveringRadii.
- packing_exact and covering_exact identify their extrema (not merely upper/lower estimates).
- gap_exact proves their actual quotient equals sqrt(t^2+2).
- valid_lattice_unbounded includes the discrete/full-rank certificates for every witness.
- no_upper_endpoint negates the universal finite-upper-bound statement.

The argument is valid without any determinant normalization: both radii scale by the same positive factor. Thus determinant-one normalization would preserve the ratios. The source imposes no restriction to well-rounded or bounded-aspect-ratio lattices. Adding one would be a different problem.

## Solo adversarial review
PASS, subject to parent review of the final artifacts. No independent reviewer was used.
1. No change from Euclidean metric to l-infinity metric: actual EuclideanSpace norm_sq is used.
2. No radius formula is assumed: both exact extrema are proved using universal radius sets.
3. Covering upper bound uses rounding all three coordinates; lower bound checks every lattice point, not just corners of one cell.
4. The selected family is proved additive, discrete, and full rank for every t>=1.
5. We refute only the upper-endpoint assertion. The BCC minimum is not claimed false.
6. No floating-point or numerical search enters the proof.
7. No sorry/admit/native_decide/custom axioms; all proof terms checked by Lean 4.19.0 with warnings treated as errors.

Primary terminology reference located: Daniele Micciancio, CSE206A Lattice Algorithms and Applications, Lecture 2, section 5, University of California San Diego (2019). Packing radius equals half the shortest nonzero vector norm; covering is by closed balls.
https://cseweb.ucsd.edu/classes/fa19/cse206A-a/lec2.pdf
The web search supplied its section text; direct PDF open returned an internal error. Use another successfully opened primary source in the final paper if full-source verification is required.

Artifacts: round5/drafts/00000005609/lean/Main.lean and round12/other/5609-strict.log. Parent will prepare LaTeX/PDF, provenance, fresh build, final review and single-problem PR.

Additional primary source successfully opened in full: Pulkit Grover, Se Yong Park and Anant Sahai, The finite-dimensional Witsenhausen counterexample, section III, Definitions 2--4 (PDF page 9; packing radius, covering radius and their ratio).
https://people.eecs.berkeley.edu/~sahai/Papers/WitsenhausenFiniteLength.pdf
Only terminology is used; every radius formula and counterexample is proved above independently. No novelty claim is made for the elementary rectangular-lattice calculation.


Reviewed artifact hashes:

- Main.lean: `8efd0b733bba0ff7a74b400721b4351ea01c013ccf3c92db960e3dc758f3e194`
- main.tex: `076ee5bb59e39a10f5867e67b35f94c8827ff5f0d96f9d04c35d84a8bab0ae20`
- main.pdf: `18924c4f4ca77cfe84968b33f16bf30e2758f097b4761e29a07fb75a4ea30ee0`
