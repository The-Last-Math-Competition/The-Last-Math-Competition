# Author-agent adversarial self-review: 00000005501

Verdict: PASS

# 5501 — an actual M/M/1 open network contradicts the half-power queue-length scale

## Exact source and scope

The parent fetched and screened `round5/source/00000005501.md`. Both languages define an open network as a Markovian network with exponential service and assert that near stability its queue length has load-deficit exponent -1/2. Neither excludes a network with one station. The English additionally specifies a prefactor and a branching interpretation. A false exponent already disproves the whole conjunction; no claim about that undefined prefactor is needed.

Take one infinite-capacity queue, external Poisson arrivals at rate rho in (0,1), one exponential server with service rate 1, and departures out of the network. Its load is rho, its stability boundary is rho=1, and its dimensionless load deficit is delta=1-rho. This is the standard open M/M/1 queue. The parent opened Eytan Modiano's MIT 6.263 lecture slides at https://web.mit.edu/modiano/www/6.263/lec5-6.pdf, which specify this standard birth/death generator and its geometric stationary distribution. The mathematical proof below establishes stationarity and the actual expectation/probabilities without relying on a quoted queue-length formula.

## Genuine queue transition law, rather than a named random variable

`clockCoin` is an actual Bool PMF with arrival probability rho/(1+rho) and potential service probability 1/(1+rho). `tick rho n` maps this PMF to n+1 after arrival and max(n-1,0) after potential service. Thus potential service at an empty queue is an idle clock event. `tick_mass` proves the transition PMF equals the explicitly stated nonnegative matrix `T`.

`advance` performs actual repeated PMF bind transitions. `queueLaw` mixes these transitions by Mathlib's actual Poisson distribution with parameter (1+rho)t. This is Poisson uniformization at clock rate 1+rho. Uniformization is used as a definition of the queue's one-time law, not an assumed stationary answer. The source contains the complete law rather than an arbitrary geometric variable labelled as a queue.

`Q=(1+rho)(T-I)` is the uniformization generator. The five generator theorems check all its entries: Q(n,n+1)=rho; Q(n+1,n)=1; Q(0,0)=-rho; Q(n+1,n+1)=-(1+rho); every remaining entry is zero. These are exactly the M/M/1 rates. No derivative-at-time-zero theorem or independent construction of an entire exponential holding-time sample path is claimed; the standard equivalent Poisson uniformization construction specifies the Markovian queue used here.

## Stationarity and true expectation

`stationary` is Mathlib's normalized geometric PMF with success parameter 1-rho. `stationary_mass` proves its actual atom probability is

    pi_n=(1-rho)rho^n, n>=0.

`real_detailed_balance` proves pi_n T(n,m)=pi_m T(m,n) for every pair, by adjacent pairs and zero nonadjacent entries. `detailed_balance` transfers the identity to actual ENNReal PMF masses. `stationary_tick` sums it, using normalization of each actual PMF row, to prove pi.bind(tick)=pi. Induction gives `stationary_advance`; actual Poisson mixing gives `queueLaw_stationary` for every nonnegative real time. Thus the counterexample is a genuine stationary queue, not an approximation in heavy traffic.

`mean` is the nonnegative Lebesgue integral of the actual state n against this probability measure. `weighted_sum` proves the convergent weighted geometric series via Mathlib's HasSum theorem. `mean_eq` proves the integral equals the finite ENNReal value of rho/(1-rho). `deficit_times_mean` gives the exact identity

    delta E[N]=rho.

In particular the actual mean has exponent -1, with delta E[N] tending to 1. This is incompatible with a finite nonzero half-power prefactor. The ENNReal integral is never converted to a real value without first proving it equals ofReal of the finite positive formula, so no infinity-toReal=0 artifact is involved.

## Probability-scale contradiction, stronger than a mean-only argument

An expectation alone could in principle be driven by rare huge values. The second argument disproves the proposed scale for the actual distribution itself.

`cdf` is the toReal value of the actual stationary measure of {0,...,K}. The finite-set PMF theorem proves that this probability is the finite sum of the actual atoms. Each pi_n is at most delta because rho^n<=1. Thus `cdf_bound` proves

    0 <= P[N<=K] <= (K+1)delta.

Choose a_k=k+2, rho_k=1-a_k^(-2). `load_mem` proves rho_k lies strictly between zero and one for every k, and `load_tendsto` proves rho_k tends to the actual stability boundary 1. `deficit` and `sqrt_deficit` prove delta_k=a_k^(-2) and sqrt(delta_k)=1/a_k exactly.

The exact normalized mean is a_k-1/a_k (`normalized_mean_eq`), which tends to positive infinity (`normalized_mean_tendsto`). For every fixed natural M,

    P[N_{rho_k}<=M a_k] <= (M+1)/a_k -> 0.

This is `proposed_scale_not_tight`. Since a_k=delta_k^(-1/2), every fixed multiple of the proposed scale captures asymptotically zero probability. Equivalently, sqrt(delta_k)N_{rho_k} escapes to infinity in probability. Natural M suffice for arbitrary finite real cutoffs by choosing a larger integer M and using monotonicity of probability. `no_fixed_scaled_half_mass` explicitly rules out even eventual capture of probability 1/2 at each fixed M. Hence no finite-prefactor stationary scaling law on the proposed half-power scale is possible.

This failure along one legitimate sequence approaching the boundary refutes a universal near-boundary assertion. It does not claim that transient observations at a fixed time have this stationary asymptotic or that a differently defined centered fluctuation is being studied. The original asserts queue length, not a centered CLT statistic; stationary length is a valid instance and also the standard stationary heavy-traffic quantity.

## Convention for queue length excluding the customer in service

If queue length counts only waiting customers, let W=max(N-1,0). `waiting` is the actual pushforward PMF, not a substituted formula. `waitingCDF_eq` proves the exact event identity P[W<=K]=P[N<=K+1]. Therefore

    P[W_{rho_k}<=M a_k] <= (M+2)/a_k -> 0.

`waiting_proposed_scale_not_tight` and `no_fixed_waiting_scaled_half_mass` prove the same failure under this other common convention. The proof therefore does not depend on including or excluding the single customer in service.

## Author adversarial audit (not independent review)

1. One station is within the exact stated network definition. There is no source hypothesis requiring a nontrivial branch or multiple stations. A single service station is its own bottleneck.
2. The deficit is exactly 1-rho with service rate fixed at 1; changing whether rho denotes utilization or unnormalized arrival rate cannot change its order here.
3. Actual transition PMFs, all generator entries, repeated transitions and Poisson mixing identify the M/M/1 model, rather than merely assigning an interpretation to a geometric distribution.
4. Exact detailed balance and PMF normalization prove stationarity for all times. No unproved balance equation is used as a new axiom.
5. True expectation is an actual nonnegative measure integral. Summability, finite conversion, and positivity are proved.
6. A separate actual-measure cutoff bound rules out a rare-tail explanation of the expectation divergence and refutes a typical stochastic half-power scale.
7. The approach sequence is inside the stable regime for every index and converges to the genuine load boundary. Its exact square-root deficit is proved.
8. Both total population and waiting-only queue length are covered by actual PMF pushforwards.
9. No conclusion about the source's underspecified redistribution prefactor is required after the exponent clause is false. The result does not purport to determine all network exponents.
10. All main theorems are audited using `#print axioms`; only Lean's standard propext, Classical.choice and Quot.sound are allowed. The reproducible checker runs an actual full `lake build` and a strict `lake env lean -DwarningAsError=true Main.lean`, recording exit codes, timings and hashes. The author report does not replace the parent's separate adversarial review/fresh build.

## Deliverables

Main Lean source is `round5/drafts/00000005501/lean/Main.lean`, with Lean 4.19.0 and Mathlib pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. The checker and logs are `round14/other/check_5501.py`, `5501-build.log`, `5501-strict.log`, `5501-checks.json`. Actual final hashes and timings are recorded in `5501-HANDOFF.json` after checks finish. This agent creates no TeX, PDF or PR; those are the parent's responsibility after review.


Reviewed artifact hashes:

- Main.lean: `31fcdc1eb502f1129d18eca082d9961f47202e00e267acdad226717daf2041ad`
- main.tex: `795a316e2f2300da9f2e261fd40c31a4f6b3e8fe31b13e74454fc4d019ee7d4d`
- main.pdf: `e547441d3de30cee75ba240449d83e8daef3753cb547cb136a0904c62fe85caa`
- SOURCE.md: `53a7af6f2881735a3b5ff0bea6ab11b493ad70b67e414d4d975d65e00387eded`
