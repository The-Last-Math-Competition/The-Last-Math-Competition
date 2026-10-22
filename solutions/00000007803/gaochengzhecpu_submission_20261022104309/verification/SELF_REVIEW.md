# Author-agent adversarial self-review: 00000007803

Verdict: PASS

# 7803 — bounded isotropic log-concave iid samples cannot have the asserted Gumbel limit

## Exact source and scope

The parent fetched the exact bilingual source `round5/source/00000007803.md` and cleared previous submissions. It considers an isotropic log-concave sequence X_i, defines the maximum of their norms, and claims that M_N/sqrt(N)-c_N converges to a Gumbel-type extreme-value law, with c_N=sqrt(2 log N)/sqrt(N) and a correction proportional to

    d_N=(log log N)/(sqrt(2 log N) sqrt(N)).

There is no hypothesis requiring unbounded support or excluding dimension one. Take iid real variables uniform on [-sqrt(3),sqrt(3)]. They have mean zero, variance one and a genuine log-concave density. Their maxima are all at most sqrt(3), so the displayed statistic converges to zero almost surely. The original c_N and every fixed real multiple of the displayed correction tend to zero. Thus the proposed limit is the point mass at zero, and cannot be any Gumbel law with positive scale and finite location. This disproves the first distributional clause, independently of the additional claims about L_K and thin-shell constants.

The formal sample index is n>=0 with sample count N=n+1. `maximum n` is exactly max_{0<=i<=n}|X_i|, and every normalization and correction uses the same sample count `size n=n+1`. This is a harmless reindexing of all positive sample sizes, not a weakened subsequence.

## The actual one-dimensional isotropic log-concave measure

`r=sqrt(3)` with r>0 and r^2=3 is proved. `support=[-r,r]` and

    mu=(volume support)^(-1) times volume restricted to support

is Mathlib's conditional Lebesgue measure. `support_volume` proves its length is 2r; positivity and finiteness establish an actual IsProbabilityMeasure instance.

The real function `density` equals 1/(2r) on this interval and zero outside. `density_representation` proves the exact measure identity

    mu=volume.withDensity (ofReal composed with density).

Thus the density proof concerns the actual measure, not an unrelated function. `density_nonneg` proves nonnegativity. `density_logConcave` proves the standard multiplicative log-concavity inequality, for every real x,y and every t in [0,1]:

    f(x)^t f(y)^(1-t) <= f(tx+(1-t)y).

For t=0 or t=1 this is equality. If either endpoint is outside the support at an interior t, its positive power is zero. If both endpoints are inside, convexity of the actual interval keeps the combination inside and the constant density gives equality. No unimplemented Mathlib log-concave class or proxy predicate is assumed.

`integral_uniform` transfers a Bochner integral against the actual normalized measure to the interval integral divided by 2r. `integrable_id` and `integrable_square` establish genuine integrability on the compact interval and under its finite scalar normalization. Then `centered` and `unit_second_moment` compute

    integral x dmu=0,
    integral x^2 dmu=1.

In dimension one, these are precisely centering and identity covariance. Since the mean is zero, variance equals the displayed second moment. The isotropy hypothesis is established by actual measure integrals with their integrability, not assigned as a Boolean assumption.

## Actual infinite iid process

The sample space is Omega=N->R and `law=Measure.infinitePi (fun i=>mu)`, Mathlib's actual infinite product probability measure. `X i omega=omega i` is coordinate evaluation.

`cylinder` proves the finite-cylinder identity

    law {omega: omega_i in A_i for i in S}=product_{i in S} mu(A_i)

for every finite index set and measurable A_i. `marginal` proves each coordinate event has its true mu probability. `marginal_map` proves law.map(X_i)=mu, and `independent` proves Mathlib's full iIndepFun property by its standard finite-intersection factorization. These are actual independent, identically distributed random variables on a genuine infinite probability space; no mere bounded deterministic list substitutes for the source's stochastic sequence.

`coordinates_centered` and `coordinates_unit_second_moment` also transport the two actual integrals to each coordinate under the actual product law. The common marginal has exactly the log-concave density proved above.

The marginal support has probability one. Countable intersection yields `all_bounded`: with probability one, every coordinate satisfies |X_i|<=r simultaneously. This is important: the bound is on one common full-measure event for the whole sequence, rather than unrelated probability-one events with an unjustified uncountable intersection.

## True maximum and analytic normalization

`maximum` is recursively the absolute value of the first coordinate followed by an actual max with the next absolute coordinate. `maximum_le_iff` proves the exact characterization

    maximum(n,omega)<=b iff |X_i(omega)|<=b for every i<=n.

`maximum_measurable` proves measurability of every finite maximum. `maximum_bound` gives 0<=maximum(n,omega)<=r on the common full-measure event, for all n.

`size_tendsto` proves N=n+1 tends to infinity, and `sqrt_size_tendsto` and `inv_sqrt_size_tendsto` give the required square-root limits. `bounded_sequence_sqrt_zero` proves, for every bounded nonnegative real sequence m_n, that m_n/sqrt(n+1) tends to zero. This analytic fact needs no independence or coupling restriction, and is applied to each actual maximum path.

`center_tendsto` uses the genuine log(N)/N->0 theorem and continuity of square root to prove c_N->0. `correction_tendsto` uses log(x)/sqrt(x)->0 with x=log(N), then multiplies by 1/sqrt(N) and the constant 1/sqrt(2), to prove the exact displayed d_N->0. Both are actual limits of the original formulas, including their finite initial values under Mathlib's total log/division conventions; such initial values do not affect the infinite-sample limit.

For a centering sequence b_n tending to zero, `Z b n omega` is the actual maximum divided by sqrt(N), minus b_n. `almostSure_zero_limit` proves that Z tends almost surely to zero. `original_almostSure_zero` specializes to the stated c_N. `corrected_almostSure_zero` covers b_n=c_N+a*d_N for every fixed real a, including either sign of the original correction and any fixed conventional numeric coefficient.

## Direct contradiction using actual CDFs

`actualCDF b n x` is the actual product measure of the event {Z_b(n)<=x}, converted to a real probability. `Z_measurable` establishes measurability. `actualCDF_eq_cdf` proves that this event formula equals Mathlib's CDF of the actual pushforward law.map(Z_b(n)). It therefore does not use an invented probability distribution.

For every b_n->0 the deterministic upper bound r/sqrt(N)-b_n eventually lies below 1. Consequently `cdf_eventually_one` proves that the actual CDF at x=1 is exactly 1 for every sufficiently large sample count. This gives a particularly simple distributional contradiction without invoking an unformalized implication from almost sure convergence to weak convergence.

The standard Gumbel CDF with location u and positive scale s is

    G_{u,s}(x)=exp(-exp(-(x-u)/s)).

`gumbelCDF_continuous` proves its continuity. `gumbelCDF_lt_one` proves its value is strictly below 1 at every finite x. `ConvergesToCDF` expresses the standard necessary CDF condition for convergence in distribution: convergence of the actual CDF at every continuity point of the target CDF. This definition is accompanied by the equality to the actual Mathlib pushforward CDF, not substituted for the stochastic law. The Lean file does not prove an equivalence with Mathlib's complete weak-convergence framework or construct a Gumbel probability measure. Neither is needed: the contradiction refutes an explicit standard necessary condition for that claimed distributional convergence.

If the asserted Gumbel convergence held, the actual CDF at the continuity point x=1 would converge both to 1 and to G_{u,s}(1)<1. Uniqueness of real limits is a contradiction. `no_gumbel_limit` proves this for every b_n->0 and all real formula parameters; the target is a genuine Gumbel law when s>0. `original_center_no_gumbel` and `corrected_center_no_gumbel` give the exact original center and correction conclusions. Allowing a location parameter does not rescue the assertion.

## Author adversarial audit (not independent review)

1. Dimension one is within the source, and a uniform interval density is full-dimensional in R, not a lower-dimensional or discrete measure. It is also nondegenerate because variance is one.
2. Probability normalization, density representation, log-concavity and isotropy are all proved for the same actual measure. Integrability is explicit, so a nonintegrable Bochner integral returning zero cannot fake centering.
3. The random sequence is a genuine countable product measure with proved marginal laws and iIndepFun. Independence is stronger than the source's written hypotheses, so imposing an intended iid assumption does not invalidate the counterexample.
4. The maximum is the exact finite running maximum of absolute coordinate values, proved by an iff characterization and actual measurability. No prescribed deterministic maximum or proxy law is used.
5. One common full-measure bound covers all coordinates and all finite maxima. A countable intersection is legitimate and proved.
6. Every formula consistently uses sample count N=n+1. The theorem concerns the original positive sample sizes; it does not exploit a finite initial value or a sampling-count shift.
7. Both the stated center and the precise log-log correction converge to zero. Arbitrary fixed correction coefficients are covered, so a sign convention or missing factor 1/2 does not matter.
8. Actual almost sure convergence is proved. Independently, the direct actual-CDF contradiction excludes every positive-scale Gumbel with arbitrary finite location. A degenerate point mass is not a nondegenerate Gumbel extreme-value law.
9. This does not claim that no bounded random-variable maxima ever have an extreme-value limit under other normalizations. Uniform maxima have a different endpoint extreme-value theory; the refutation is specifically of the normalization and universal Gumbel claim written here.
10. No analysis of L_K, a thin-shell constant, or the asserted universal product is required once the first claimed distributional clause fails.
11. Only the standard propext, Classical.choice and Quot.sound dependencies are allowed by the explicit main-theorem audits. No extra assumptions about distributions or independence are introduced as new logical axioms. The author report does not constitute independent review; the parent performs its separate adversarial review and fresh build before any publication.

## Reproducible verification and handoff

Lean source: `round5/drafts/00000007803/lean/Main.lean`. Lean 4.19.0; Mathlib pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. The author runner `round14/other/check_7803.py` performs a full actual `lake build` and strict `lake env lean -DwarningAsError=true Main.lean`, recording exit codes, timings and hashes. Logs are `7803-build.log`, `7803-strict.log`, `7803-checks.json`; final source/log hashes are in `7803-HANDOFF.json`. No TeX, PDF or PR is created by this subagent.


Reviewed artifact hashes:

- Main.lean: `df250dba5f1a7c8d7dbb7f6c7a23d10a0b1f15dbff4b99d2d37c0f39755542d0`
- main.tex: `e717246358461c88caf59b06199b7f13822661aabc6b4287dcfffb6c817701d7`
- main.pdf: `b4d3bde00cfb1731a5d92a5e1cb18cd989c14d25cc361fd871a1c3dcacadec6d`
- SOURCE.md: `b1efcf1b604e529fa23dc60d0e81a391c9b81dba8f887e6bf1352e81b188f1c2`
