# Mathematical correspondence (author handoff, not the submission report)

## Exact source and scope

Original file: `/private/tmp/tlmc1569-author-input/ORIGINAL.md`, 552 bytes, SHA256 `b625b615f8944e7f0d0b0b754e89786d0377a17159113dd05a0c05e8836ac751`. Both language versions were read completely before deriving the construction. Both state an unrestricted n-point distinct-angle lower bound n² - O(n), followed by a lattice-attainment assertion. Neither specifies general position, noncollinearity, a restricted class of point sets, or an exceptional family to omit.

I use the ordinary Euclidean plane and ordinary unoriented angles in radians, determined at the middle point of a triple of pairwise distinct points. Collinear triples determine angles 0 or pi. These are Mathlib's canonical EuclideanGeometry.angle on EuclideanSpace R (Fin 2), not a custom surrogate for angle size. Radians vs degrees does not affect distinct-value cardinality. The source does not explicitly settle treatment of degenerate angles; excluding 0 and pi would only reduce this counterexample's angle count to zero, so that convention does not rescue the lower bound. The Lean endpoint uses the convention that includes them. No unstated noncollinearity condition is added. If the intended claim had a restricted admissible family, that would be a different statement needing specification.

The source's lattice-attainment clause is not precise enough to identify a unique formal proposition. We do not invent a family or equidistribution assertion. Instead we refute its necessary first conjunct, and formally prove the conjunction false for every possible proposition representing the second clause.

## Uniform asymptotic statement

The claimed bound entails constants C >= 0 and N in N such that for every n >= N and every finite planar S of cardinality n,

    n² - C*n <= number of distinct angles of S.

`UniformQuadraticLowerBound` is exactly this quantifier order. A uniform O(n) remainder is bounded above by C*n for sufficiently large n. The disproof is stronger: `arbitrarily_large_counterexamples` allows every real C, including negative ones, and every natural threshold N. This also defeats a claimed bound specialized only to our single entire configuration family. It is not a finite check or an isolated small-n violation.

## Construction and proof

`axisPoint x = (x,0)` in the standard Euclidean plane. Its first coordinate proves injectivity. `configuration n` is the finite image of {0,...,n-1} under j -> axisPoint(j). Injectivity of natural-number casting and of axisPoint prove its cardinality is exactly n, with no surrogate cardinality.

All axisPoint values lie on the line with base point 0 and direction (1,0). The formal proof supplies this affine-line representation to Mathlib's collinearity criterion. For three distinct points a,b,c of a configuration, the canonical theorem for three collinear points gives a=b or c=b or angle(a,b,c)=0 or angle(a,b,c)=pi. Distinctness eliminates the equalities. Therefore the actual angle set is a subset of {0,pi} and has cardinality at most two.

For arbitrary C and N, choose a natural m > max(C,2), put k=max(N,m), and use the configuration with n=k+1 points. Then n>=N, n>3 and n-C>1; consequently n²-C*n=n(n-C)>n>2. Its at-most-two angle values violate the lower bound. The implementation uses the Archimedean theorem `exists_nat_gt`, natural/real order conversions and kernel-checked polynomial arithmetic (`nlinarith`) to prove this inequality for all C and N.

## Source declarations and endpoint mapping

All names are in namespace `Conjecture1569`.

- `Plane`: the canonical two-dimensional real Euclidean space.
- `angleSet`: finite image of the genuine Euclidean angle over the filtered Cartesian cube of S; the filter enforces pairwise distinct vertices.
- `mem_angleSet_iff`: proves both directions of the exact correspondence between membership in this represented angle set and a genuine angle determined by three pairwise distinct points of S.
- `axisPoint`, `axisPoint_injective`: actual geometric placement and injectivity.
- `configuration`, `configuration_card`, `configuration_mem_axis`: actual n-point configuration, exact cardinality n, and membership on the geometric line.
- `axis_collinear`: canonical affine collinearity of the x-axis.
- `configuration_angle_zero_or_pi`: the geometry bridge from canonical angles to the two possible values.
- `configuration_angleSet_subset`, `configuration_angleSet_card_le`: actual angle-set inclusion and upper cardinality bound.
- `UniformQuadraticLowerBound`: the full uniform asymptotic lower-bound claim.
- `arbitrarily_large_counterexamples`: for every C and N, constructs a genuine finite S at some n>=N with card S=n and angle count strictly below n²-C*n.
- `not_uniformQuadraticLowerBound`: logical negation of the precise lower-bound claim.
- `original_conjunction_false`: for every proposition LatticeAttainment, not (UniformQuadraticLowerBound and LatticeAttainment). This is an explicit necessary-conjunct disproof of the bilingual original; LatticeAttainment is not asserted or axiomatized.

Audit.lean is separate inspection-only source. No auxiliary mathematical computation is required. The optional helper's regular-polygon remark is unused.

## Repairs and evidence

`Solution-attempt-01.lean` is the initial complete attempt. Its first replay failed before elaborating it because the supplied standard library lacked the Affine angle module's object file (004 log). Building the pinned standard module succeeded (006 log). The second replay (008 log) identified an untyped image lambda inferred as real rather than natural and the unavailable name Finset.card_pair_le. Lean's recovery consequently reported declarations using sorry, but there was no source sorry/admit placeholder. Both issues were repaired by annotating the lambda argument as Nat and proving the cardinality of {0,pi} by standard simp. `Solution-attempt-02.lean` is that repaired source. Replay 009 succeeded with warningAsError=true. All these failed outputs and exact source snapshots are retained; failures are not passed off as successful checks.

The first full project build (010) successfully built Solution but failed only in Audit: `#print prefix` is not a Lean 4 command. `Audit-attempt-01.lean` preserves that failed inspection attempt. Replacing it with a read-only environment-name enumeration produced a successful full build (012). Extending #print axioms to every generated namespace declaration gave another successful build (013). That broader inspection showed ordinary compiler-stage auxiliary declarations for the computational axisPoint definition, one of which mentioned a compiler-generated Equiv lambda. None of the 16 authored declarations had that dependency. To remove these irrelevant runtime artifacts entirely, axisPoint was explicitly marked `noncomputable`; no mathematical definition or proof changed. This is `Solution-attempt-03.lean`, the final mathematical source. Full build 014 succeeded with 26 compiled namespace declarations, all of whose axiom sets are subsets of {propext, Classical.choice, Quot.sound}. Final strict direct source replays 015 and 016 both succeeded. Audit-before-noncomputable.lean and all earlier raw outputs are retained.
