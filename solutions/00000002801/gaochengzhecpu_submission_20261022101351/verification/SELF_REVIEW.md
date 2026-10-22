# Author-agent adversarial self-review: 00000002801

Verdict: PASS

# 2801 — an irreducible periodic chain has a good empirical LDP rate with no Hessian

## Exact source scope

The exact bilingual source is `round5/source/00000002801.md`, freshly checked by the parent for previous submissions. It asserts that for irreducible Markov chains the empirical-measure LDP rate has a unique zero and a Hessian there equal to a spectral-gap-dependent multiple of Fisher information. It does not require aperiodicity, laziness, positive transition entries, or an absolute spectral gap.

The two-state deterministic alternating chain is irreducible, and its empirical-measure rate has a unique zero. However, its actual good LDP rate is infinite everywhere else. It is not locally real-valued even on the interior of the probability simplex, so its ordinary real Hessian does not exist. This disproves the asserted Hessian clause without choosing a spectral-gap convention or calculating a Fisher matrix.

## Actual finite chain and process law

The state space is Bool, ordered as false and true. The actual transition probabilities are

```
P = [[0,1],[1,0]],
transition(s) = PMF.pure(not s).
```

`transition_matrix` checks the PMF probabilities equal `ENNReal.ofReal (P s t)`. `P_stochastic` checks nonnegative entries and each row sum 1. `P_square` proves the genuine matrix identity P^2=I. `P_irreducible` uses the standard finite-state criterion: for every pair of states s,t there is a positive integer n with (P^n)(s,t)>0. Distinct states are connected in one step and equal states in two steps. Irreducibility does not imply aperiodicity; this example has period two.

Take initial state false and the actual path

```
X_k = false if k is even, true if k is odd.
```

The law on complete paths is the genuine probability mass function `PMF.pure state`. It is not merely a sequence assigned a Markov label. For every arbitrary candidate path w and every n, `process_path_probability` and `process_path_measure_probability` prove the exact finite-dimensional Markov factorization

```
Pr(X_0=w_0,...,X_n=w_n)
  = 1_{w_0=false} product_{k=0}^{n-1} transition(w_k)(w_{k+1}).
```

The second theorem is an equality for the actual probability measure, not only an outer-measure expression. The proof checks valid paths are uniquely the alternating path and that any failed initial condition or transition gives probability zero.

## Actual full empirical measures, not a scalar proxy

The ambient vector space E is the genuine real coordinate space Bool->R. Finite-state probability measures are represented by their complete vector of masses; this is the usual closed probability simplex in E. The actual empirical vector is

```
L_n(s) = #{0<=k<=n : X_k=s}/(n+1).
```

Both coordinates are explicit actual occupation counts. `occupation_probability_vector` proves every coordinate is nonnegative and the sum of all coordinates is 1. `pathOccupation` defines this full empirical vector for an arbitrary sample path; `empiricalLaw` is the genuine PMF pushforward of the process law through that function, converted to a probability measure. `empiricalLaw_probability` proves it is an actual probability measure. `empiricalLaw_eq` identifies the distribution as Dirac(L_n), as the actual deterministic chain requires.

The number of true states among the first m observations is floor(m/2); the count identity is proved exactly in `count_true`. Both coordinates satisfy

```
|L_n(s)-1/2| <= 1/(n+1).
```

Consequently the entire vector L_n converges in the genuine product topology of E to

```
pi = (1/2,1/2).
```

This is `occupation_tendsto`. `stationary_invariant` proves pi is a probability vector and pi P=pi. `stationary_unique` proves any normalized invariant vector is this same pi.

## Full standard good LDP, including log(0)=-infinity

The formal LDP definition is the standard open-set lower bound and closed-set upper bound, with speed equal to the actual sample count n+1:

```
-inf_{x in G} I(x) <= liminf_n (1/(n+1)) log(mu_n(G))     for every open G,
 limsup_n (1/(n+1)) log(mu_n(F)) <= -inf_{x in F} I(x)     for every closed F.
```

This is `HasLDP`. Speed n+1 is simply the number of observations X_0,...,X_n; renumbering observations from 1 yields the customary speed m. Empty-set infima are +infinity, as required.

The normalized logarithm `scaledLog` takes values in EReal. It is exactly minus infinity when the probability is zero; it is plus infinity for infinite mass, and otherwise it is the real logarithm of the positive finite probability divided by n+1. In particular `scaledLog_zero` and `scaledLog_one` prove the correct endpoint values. The actual probabilities in this example are always 0 or 1, so the positive-finite branch causes no integrability or logarithm-domain issue. **Real.log(0)=0 is never used as the logarithm of a zero probability.**

Use the rate function

```
I(x)=0 if x=pi,
I(x)=+infinity otherwise.
```

The function is nonnegative. `pointRate_inf` computes its actual infimum on every set, including the empty set. `convergent_dirac_ldp` proves the full open/closed-set LDP for every convergent deterministic sequence, using actual Dirac measures:

- If an open set contains the limit, the sequence eventually belongs to the set, so its probability is eventually 1 and its normalized logarithm is eventually 0. If the open set does not contain the limit, the required lower bound is minus infinity.
- If a closed set excludes the limit, its complement is a genuine open neighborhood of the limit, so its probability is eventually zero and its normalized logarithm is eventually minus infinity. If the closed set contains the limit, every normalized logarithm is at most zero, giving the required upper bound.

These bounds quantify over **all** open and closed sets in the actual ambient finite-dimensional space, not a few selected test events. They therefore also give the usual LDP on the closed probability simplex with its relative topology.

`pointRate_lowerSemicontinuous` proves actual lower semicontinuity. `pointRate_good` proves every finite real level set is compact: it is empty for a negative level, and the singleton {pi} at every nonnegative finite level. `empirical_good_ldp` combines the actual empirical-distribution LDP, lower semicontinuity and compact finite level sets. `unique_rate_zero` proves the zero is exactly pi.

For standard terminology and the precise open/closed-set definition, the parent actually opened S. R. S. Varadhan, *Large Deviations*, Spring 2010 notes, section 2 “General Principles”, https://math.nyu.edu/faculty/varadhan/LDP/1-2.pdf. The definition above follows those inequalities and the good/proper rate requirements. This reference supplies standard definitions only; the example's full LDP is proved directly in Lean.

## No ordinary Hessian even along the interior simplex coordinate

Consider the actual affine interior probability line

```
q(t) = (1/2-t,1/2+t).
```

For |t|<1/2 these are actual probability vectors, and q(t)=pi precisely when t=0. For every positive delta choose

```
t = min(delta,1/2)/2.
```

Then 0<t<delta, t<1/2, and I(q(t))=+infinity. These facts are all checked in `rate_infinite_in_every_simplex_neighborhood`.

`no_local_real_rate` proves there is no positive neighborhood and no real-valued function f on it representing I(q(t)). Thus the rate is not even locally real-valued at the stationary measure in the **interior** of the probability simplex; there is no classical real first derivative or ordinary real Hessian there. This is stronger than a failure of the proposed numerical Hessian formula. It makes no assertion about generalized extended-valued second epi-derivatives, which would be a different notion from the source's Fisher-information Hessian.

## Author adversarial review (not independent external review)

- Checked both source languages: only irreducibility is required; aperiodicity is not an implicit part of the standard definition of irreducibility. The source uses no stronger word such as primitive or uniformly mixing.
- This example is genuinely irreducible. Its deterministic transitions do not make it reducible: each state reaches the other in one step and itself in two.
- The actual process is defined on full sample paths by a genuine PMF, and all finite path probabilities are checked against the standard initial-law times transition-product formula. No process is supplied merely by its stationary distribution.
- Starting from a fixed state is a valid initial distribution. It does not change the transition matrix or its irreducibility. The universal source statement does not exclude it.
- The empirical vector contains both actual state masses and has a checked total of 1. A single summary statistic is not substituted for the empirical measure.
- The distribution of empirical vectors is the actual pushforward of the full process law, not a separately chosen sequence of Dirac measures. Its simplification to Dirac is proved.
- The LDP is the genuine full lower/upper bound on all open/closed sets, uses the real topology and EReal limits, and handles empty sets and probability zero with the standard infinities. No finite-event proxy replaces an LDP.
- The rate is actually lower semicontinuous with compact finite level sets and a unique zero equal to the actual unique stationary probability vector. The refutation concerns the Hessian clause rather than the already true unique-zero clause.
- Lack of a real-valued germ is proved along actual probability vectors strictly inside the simplex, so this is not an artefact of differentiating across an outer boundary or outside the space of probability measures.
- No choice of ordinary versus absolute spectral gap enters the proof. Even the existence of the claimed classical Hessian fails before any proposed constant is considered.
- No floating-point approximation, numerical experiment, `sorry`, `admit`, `native_decide`, custom axiom, or private evaluator is used. The final source prints the axioms of eleven principal results.
- The author has not claimed an independent review. The parent must still perform adversarial semantic review and a clean fresh build before publication.

## Reproduction and handoff

The project is `round5/drafts/00000002801/lean`, using Lean 4.19.0 and official Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

`round14/other/check_2801.py` runs an actual full `lake build` and an actual strict `lake env lean -DwarningAsError=true Main.lean`, preserving original command output and recording complete commands, timing, status, hashes and timestamps. Evidence files are `2801-build.log`, `2801-strict.log`, and `2801-checks.json` in that directory.

No auxiliary numerical verifier is required because the actual finite-path computations, occupation counts, matrix identities and all asymptotic inequalities are completely covered by Lean.

This agent has not authored a PDF, modified the parent's TeX, opened a PR, or modified shared snapshot/publication state.

## Frozen verification evidence

- Main.lean SHA-256: `20fa21e961e086618b41274b601220944f2f814af4c6e99881720ddacbee548d`
- Exact source SHA-256: `c7131d3693c1d0627bf0ec4611daee0aa23f6ef671c820804afadee4d9dbb833`
- Actual lake build: exit 0, 12.625 seconds.
- Actual strict Lean: exit 0, 11.875 seconds.
- Both checks ran on the same unchanged Main.lean hash.
- Eleven printed principal theorem audits use only `propext`, `Classical.choice`, and `Quot.sound`.


Reviewed artifact hashes:

- Main.lean: `20fa21e961e086618b41274b601220944f2f814af4c6e99881720ddacbee548d`
- main.tex: `671ea4f6bdba5d9d9f7c8f23f12c07c04224ec3c687c7eb707521ea7b9684504`
- main.pdf: `4c66cf65fa58954f1be43bd227829bc771f3fdd8516c893bd249dbbfc0196823`
- SOURCE.md: `c7131d3693c1d0627bf0ec4611daee0aa23f6ef671c820804afadee4d9dbb833`
