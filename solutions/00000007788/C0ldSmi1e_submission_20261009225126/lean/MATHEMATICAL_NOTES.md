# Independent disproof of conjecture 00000007788

## Input and interpretation

The exact supplied English and Chinese statements define the samples as independent and uniform **on K**, and K is a solid convex body. The disproof uses the solid unit disk in the two-dimensional real Euclidean space. It does not use boundary sampling. The source predicts, at n = 2, a positive finite constant c such that the deficit is asymptotic to c N^(-2). A disproof of this necessary ball assertion disproves the conjunction, without choosing meanings for the separate under-specified constant-ratio and simplex-combinatorial clauses.

The supplied SHA256SUMS.json has SHA256 492540a5f2f6544e641ea4eabfd265a5064d89f93287908fc65faef70e7fe9a8. All five listed input hashes were checked. The original statement digest is a9f7f8b9409e9429768a897cb68df05fde8a518d8447ad5731c0fc3da37aeca0. Both language versions and both rule files were read before mathematical work. No prior solutions, selector notes, repository solution files, or web research informed this proof.

## Elementary argument

Let B be the closed Euclidean unit disk, let X_1,...,X_N be independent under normalized Lebesgue area on B, and let H_N be their convex hull. Write

D_N = 1 - E[area(H_N)] / pi.

For 0 <= r <= 1, the event E_r that all samples are in rB has probability (r^2)^N. On E_r, convexity implies H_N is contained in rB, and therefore area(H_N)/pi <= r^2. Everywhere in the support of the joint law, the normalized hull area is at most 1. Integrating the pointwise upper bound

area(H_N)/pi <= 1 - (1-r^2) 1_{E_r}

gives

D_N >= (1-r^2)(r^2)^N.

For t = 1/[2(N+1)] and r = sqrt(1-t), Bernoulli's inequality gives

(1-t)^N >= 1-Nt >= 1/2.

Consequently D_N >= t/2 = 1/[4(N+1)]. For N >= 1 this implies N^2 D_N >= N/8, so N^2 D_N tends to positive infinity. It cannot converge to any finite real c. In particular D_N cannot be asymptotic to c N^(-2), for any positive c.

This lower bound is deliberately coarse and does not assert a sharp actual asymptotic rate. No simulation or numerical estimate is required.

## Exact probability and geometry in Lean

`Plane` is `EuclideanSpace ℝ (Fin 2)`. `disk` is `Metric.closedBall 0 1`. `uniformDisk` is `ProbabilityTheory.cond volume disk`, the standard normalized restriction of Lebesgue measure. Its probability-measure instance is proved using the actual disk volume pi. `samples N` is the standard finite product measure `Measure.pi (fun _ => uniformDisk)` on `Fin N → Plane`, thereby representing independent uniform samples.

`hullArea x` is the actual Lebesgue measure of `convexHull ℝ (Set.range x)`, converted to a real and divided by pi. `deficit N` is one minus the Bochner expectation of `hullArea` under `samples N`. The proof establishes measurability and integrability of this exact area function, so no nonintegrable-zero convention is used to interpret the ordinary expectation.

Measurability is proved by showing that the joint graph of finite convex-hull membership is closed. Express the hull as the continuous weighted-sum image of the compact standard simplex. The graph is the projection, along that compact simplex, of the closed equation y = sum_i w_i x_i. The function x -> volume(H_N(x)) is measurable by the stock theorem for the measure of measurable sections. Nonnegativity and the almost-everywhere upper bound 1 then establish integrability.

## Authorship and isolation provenance

The primary author independently derived the smaller-concentric-disk event argument and the reciprocal-linear deficit lower bound from the supplied original statement. After deriving that approach, the primary author delegated a strictly generic analytic subtask to a fresh isolated child agent: given an arbitrary sequence D with D(N) >= 1/[4(N+1)], prove quadratic-normalization divergence and the resulting asymptotic inequivalence. The child read and verified only the supplied original/rules and searched stock Lean/Mathlib sources; it was not given prior solution material or external research. Its completed `GenericRate.lean` module was incorporated as `Conjecture7788/GenericRate.lean`. The primary author supplied the exact geometry, uniform probability law, hull measurability and integrability, lower bound, and final application, and read and compiled the child's complete module. This is internal independent collaboration, not an external mathematical source.

## Scope and reproduction

All mathematical arguments are symbolic. There is no auxiliary numerical computation whose coverage could be incomplete. The only auxiliary operations are hash verification and Lean compilation. The library sources and caches are unchanged. Authored modules belong to this fresh standalone project only.

The primary public results are `deficit_lower`, `normalized_deficit_tendsto_atTop`, `no_finite_normalized_limit`, `deficit_ratio_tendsto_atTop`, and `conjecture_00000007788_false`. The theorem `deficit_eq_expected_volume_deficit` proves the literal source correspondence, while `hullArea_integrable` and `hull_volume_integrable` establish ordinary expected-value semantics. `samples_rectangle` verifies the product probabilities of the independent uniform law. The literal source exponent at dimension two is checked in `source_exponent_dimension_two`.

`Audit.lean` records all 40 named declarations, their types and their axioms. The offline `verify.py` checks all nine exact dependency Git pins and clean status, removes only authored build outputs, clean-builds the project, replays all four authored Lean sources with warnings treated as errors, and audits every declaration against the whitelist `propext`, `Classical.choice`, `Quot.sound`. The raw command logs and final result are in `validation/`. `SOURCE_HASHES.json` fixes the exact proof/configuration/verification bytes.

No LaTeX/PDF or publication action has been performed at this stage.
