# Independent mathematical and Lean review: conjecture 00000001569

## Verdict and scope

PASS. The frozen Lean project proves a genuine disproof of the original unrestricted distinct-angle lower bound, under the explicitly stated ordinary planar Euclidean convention. The report gives the same complete argument. No mathematical or formalization correction is required. This verdict covers the frozen mathematical source/configuration and the previously reviewed report, not the still-unreleased generic verifier/final submission packaging or any maintainer decision.

## Independence and inspected identities

The source-first semantic checklist and its hashed provenance were recorded before reading either report or implementation. The complete report and both rendered pages were reviewed before the frozen project was released. The entire frozen Solution.lean, Audit.lean, lakefile.toml, lake-manifest.json, lean-toolchain, and author current-problem access/helper/correspondence records were then read. No other conjecture or prior solution was consulted. The supplied neutral dependency aliases were used only for standard-library contents.

The following exact SHA-256 identities were independently verified both before and after the build:

- Solution.lean: `00be55d3ec046fa4a383ccc4d17e61b1b166e45b7c077e59e84e810ed7454e3e`
- Audit.lean: `5be7ece3798e0231459ea54f5c916baaedcd8faaacf0a969f259c2867249705f`
- lakefile.toml: `0820267122448b673fb729b332ffc0b383cea039cd07b9da34ad2a1e19455005`
- lake-manifest.json: `8ac538fc345b2c4d2de1df57330a940642b68222035c5d3ab992a5e1bc49df6f`
- lean-toolchain: `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea`
- Report TeX: `66511cf7cbe1936ad88abcd7a0d5fb0c8f4cf0f96aa408b11119aadc2ad4ce36`
- Report PDF: `ec8b20bc1e0048b9df61caf09ed35645e56babf8be645fc24fcd690deb0034cf`

The original's Git blob identity was independently computed from its exact bytes as `ec72f71c9bee352ef1bcb0201554f357dc7ff480`, agreeing with the supplied source identity and report. Its SHA-256 is `b625b615f8944e7f0d0b0b754e89786d0377a17159113dd05a0c05e8836ac751`. The report's repository commit identity agrees with supplied metadata; this review did not access the repository to reestablish the commit-to-blob mapping.

## Exact geometry and finite-set semantics

`Plane` is the canonical `EuclideanSpace ℝ (Fin 2)`, whose standard library definition is PiLp with exponent 2. The relevant PiL2 inner product/norm and vector notation were inspected. It is actual Euclidean geometry, not the max-norm product plane.

`angleSet S` is the image of the filtered Cartesian cube `S ×ˢ (S ×ˢ S)` under `EuclideanGeometry.angle a b c`. The three filter inequalities make all three points pairwise distinct, so in particular both rays from b are nonzero. Finset image deduplicates equal real values. `mem_angleSet_iff` proves the exact two-way membership characterization. No angle determined by an admissible triple is omitted, and repeated occurrences are not overcounted.

The actual standard `EuclideanGeometry.angle` definition was inspected: it is the unsigned inner-product angle of the displacement vectors a − b and c − b. The standard collinearity theorem used by the proof was also read: three points are collinear precisely when a=b, c=b, or their angle is 0 or π. Thus the proof's `resolve_left hab` and `resolve_left (Ne.symm hbc)` remove exactly the exceptional zero-ray cases. There is no replacement of angle by a surrogate label.

`axisPoint` is the coordinate vector (x,0). Its injectivity follows by evaluating coordinate 0. `configuration n` is the image of Finset.range n under the injective natural-to-real coordinate map. `configuration_card` establishes cardinality n, including n=0,1,2. This agrees exactly with the report's nonnegative integer-coordinate description.

`axis_collinear` supplies base point 0 and direction (1,0) to the standard affine-line characterization, proving every (x,0) lies on that line. Each configuration lies on it; collinearity passes to each triple. `configuration_angle_zero_or_pi` uses the inspected canonical angle theorem, and `configuration_angleSet_subset` transfers this to all and only the represented angle values. `configuration_angleSet_card_le` then uses genuine finite-set inclusion/cardinality to obtain an upper bound of 2 for every n.

The source imposes no non-collinearity or general-position condition, so these are admissible witnesses. Under a convention excluding 0 and π, their count could only decrease, as correctly noted in the report.

## Quantifiers and final theorem

`UniformQuadraticLowerBound` is exactly

  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  ∀ S : Finset Plane, S.card = n → n² − Cn ≤ |angleSet S|,

with real coercions for the numerical inequality. C and N are chosen before n and S. There is no restriction of S to the witness family and no per-configuration hidden constant.

`arbitrarily_large_counterexamples` quantifies every real C and every natural N. It picks m > max(C,2), lets k=max(N,m), and supplies configuration(k+1). The inequalities k>C and k>2 force (k+1)² − C(k+1)>2; the known angle count is at most 2. Its conclusion contains the natural threshold, exact cardinality, and strict violation. This is stronger than the precise negation because it also allows negative C.

`not_uniformQuadraticLowerBound` substitutes such a counterexample into any alleged C,N bound and contradicts the strict inequality. `original_conjunction_false` takes an arbitrary proposition for the unspecified attainment clause and negates its conjunction with the refuted first clause. It does not claim to have formalized or disproved a separate lattice-equidistribution proposition. This is the correct scope for a disproof of the source's conjunction.

Independent example endpoints in ReviewAudit.lean spell out the uniform proposition and its quantified counterexample in the canonical Euclidean plane and typecheck against the author's endpoint theorems. Their compiled output also prints the actual geometric definitions and important theorem types for inspection.

## Independent build and axiom coverage

A separate review project was created from the five frozen source/configuration files. No author-produced object was copied. All nine dependency package HEADs were independently checked against the pinned manifest; their tracked working trees were clean both before and after verification. Lean reports version 4.19.0, commit 6caaee842e94. The pinned Mathlib revision is c44e0c8ee63ca166450922a373c7409c5d26b00b, corresponding to the supplied v4.19.0 dependency identity.

Successful checks with exact command/output records:

1. `001-independent-full-build`: complete default-target Lake build, compiling Solution and Audit.
2. `002-solution-strict-replay`: direct Solution source replay with `-t0 -DwarningAsError=true`, writing the independently rebuilt object.
3. `003-audit-strict-replay`: direct Audit source replay with the same strict settings, importing that independently rebuilt Solution.
4. `004-independent-owner-audit`: independently authored environment audit with strict settings. It selects declarations by owning module via getModuleIdxFor?, not namespace, so private/generated declarations cannot escape by naming. It found Solution=26 and Audit=0, and rejected any axiom declaration, unsafe declaration, or transitive axiom outside {propext, Classical.choice, Quot.sound}. All 26 passed. The major geometry and endpoint theorem axiom sets were additionally printed explicitly.
5. `005-post-review-identities`: verified unchanged frozen/review source hashes, exact original Git blob, all nine dependency revisions/clean tracked status, source absence of proof-shortcut tokens, and successful statuses of checks 1–4.

No sorry, admitted proof, native_decide, extra axiom, unsafe proof declaration, or source-level proof escape is present. All compiled declaration axiom dependencies are subsets of the three standard logical axioms. The author's audit source contains read-only enumeration and print/check commands and creates no owned declarations; its namespace-based coverage was not the basis of the independent verdict.

The proof is entirely deductive. No numerical/auxiliary mathematical computation is needed. The verification scripts only run tools or check identities/results. Raw outputs and exit codes are retained, not reconstructed as successes. One initial optional runtime-source lookup failed because that source file was absent; this is disclosed in INITIAL_ACCESS_RECORD.md and did not affect compilation. All independent compile/replay/audit attempts succeeded on their first run.

## Remaining work

Inspect and run the final generic verifier and submission packaging once released. The mathematical author files must remain byte-identical to the inspected freeze. This review does not authorize repository/PR mutation or claim maintainer acceptance.
