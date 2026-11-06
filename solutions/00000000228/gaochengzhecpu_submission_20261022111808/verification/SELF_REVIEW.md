# Author-agent adversarial self-review: 00000000228

Verdict: PASS

# 228 — the stated normalization of Stern square values degenerates to zero

## Exact source and conclusion

The parent fetched and screened `round5/source/00000000228.md`. Both languages specify Stern's actual diatomic recurrence s(0)=0, s(1)=1, s(2n)=s(n), s(2n+1)=s(n)+s(n+1), and claim that the distribution of

    a_n=s(n^2)/3^(log_2 n), n>=1,

converges to a continuous, nowhere differentiable fractal limit. The parent authorized this problem after excluding previous submissions.

The proof establishes the stronger full-sequence limit a_n->0. It also constructs the actual empirical PMF from uniform finite positive indices and proves that its CDF converges at every continuity point of the point mass at zero. Any proposed continuous limiting CDF is impossible. Thus the normalized values and their real empirical distributions degenerate, rather than yielding the asserted nondegenerate fractal distribution. No interpretation of the final spectral-dimension clause is needed after this first claim fails.

## Actual Stern sequence, with complete original semantics

`pair` recursively constructs adjacent natural-number values using two standard Stern matrices. For v=(a,b), the even step is L(v)=(a,a+b) and the odd step is R(v)=(a+b,b). The recursion uses n/2, with pair(0)=(0,1), and its termination is proved.

`pair_even` and `pair_odd` establish the true two binary recursions. `pair_second` proves pair(n).2=s(n+1), where `stern n=pair(n).1`. Therefore `stern_zero`, `stern_one`, `stern_even` and `stern_odd` prove all four original defining rules exactly. `stern_unique` proves that any sequence satisfying these rules equals the constructed sequence, so the construction cannot be a weaker surrogate. `stern_pos` proves s(n)>0 for every n>=1.

## A genuine three-bit global growth bound

If both coordinates of v are at most B, any three successive L/R steps have both coordinates at most 5B. `triple_step_bound` proves all eight Boolean cases using exact natural-number arithmetic. In conventional residue notation, pair(8k+r) has the following coordinates, writing pair(k)=(a,b):

    r=0: (a,3a+b)
    r=1: (3a+b,2a+b)
    r=2: (2a+b,3a+2b)
    r=3: (3a+2b,a+b)
    r=4: (a+b,2a+3b)
    r=5: (2a+3b,a+2b)
    r=6: (a+2b,a+3b)
    r=7: (a+3b,b).

Every row coefficient sum is at most 5. The Lean proof expresses these cases through the actual three-step recurrence `pair_three`; it does not assume the residue formulas as an extra axiom.

`pair_power_bound` proves, by induction on m and reducing n to n/8,

    n<=8^m implies s(n)<=5^m and s(n+1)<=5^m.

The base case covers n=0 and n=1 explicitly. The endpoint n=8^m is included, so there is no lost boundary pair. Consequently `square_numerator_bound` proves

    n<=8^(m+1) implies s(n^2)<=25^(m+1).

This is an all-n theorem, not finite testing or an estimate only on a dyadic subsequence.

## Matching the exact logarithmic denominator

`denominator n` is precisely the real power 3^(log(n)/log(2)), and `normalized n` is the actual natural-number Stern square value cast to R and divided by it. The denominator is strictly positive. At every positive index the normalized value is strictly positive. The total definition at n=0 is only a harmless extension; the actual empirical samples below always use n>=1.

`denominator_lower` proves

    8^m<=n implies 27^m<=3^(log_2 n).

It uses actual monotonicity of the logarithm, log(8)=3 log(2), log(2)>0, and monotonicity of the real power with base 3. No floating-point approximation to the exponent is used.

Combining these exact inequalities gives `normalized_block_bound`:

    8^m<=n<=8^(m+1) implies
    0<=a_n<=25*(25/27)^m.

For every positive n choose m=Nat.log 8 n. Mathlib's actual natural logarithm bounds prove 8^m<=n<8^(m+1). `nat_log_eight_tendsto` proves m tends to infinity with n. Since 0<25/27<1, the geometric upper bound tends to zero. `normalized_tendsto_zero` therefore proves a_n->0 along the entire positive integer sequence.

The arithmetic heart is the strict inequality 25<27: squaring the argument doubles the number of binary blocks, while the conjectured denominator grows by 27 for each 8-fold increase of n.

## Genuine finite empirical distributions

For N>=0, `empiricalPMF N` first samples i uniformly from Fin(N+1), then returns normalized(i.val+1). Thus its actual observations are the first N+1 positive indices 1,...,N+1. `empiricalLaw` is this PMF's actual probability measure. The use of N+1 prevents an empty index space and never samples the original undefined log(0) index.

For x>0 let `badIndices N x` be the actual finite set of indices whose normalized value exceeds x. `tail_count_formula` proves the exact actual-measure probability identity

    P_N[(x,infinity)]=#badIndices/(N+1).

This uses the genuine uniform PMF and its actual pushforward measure, not an assigned probability formula.

Because a_n->0, there is K such that a_n<=x whenever n>=K. Every bad sampled index i therefore has i.val+1<K. The injective map i->i.val sends the bad finite set into {0,...,K-1}, so `bad_count_bound` proves its cardinality is at most K. Consequently

    0<=P_N[(x,infinity)]<=K/(N+1)->0.

`empirical_tail_zero` proves this limit. `cdf_complement` and `empirical_positive_cdf` prove the actual CDF tends to 1 at every x>0. `empirical_nonpositive_cdf` proves that the actual CDF is exactly zero at every x<=0 and every finite N, since every sampled a_n is positive.

`actualCDF_eq_cdf` identifies the event-based expression with Mathlib's CDF of the actual empirical probability measure. `empirical_cdf_dirac_limit` proves convergence to the CDF of the actual `Measure.dirac 0` at every x!=0, exactly all continuity points of that limit CDF. This is the standard CDF description of weak convergence to the point mass. The Lean file does not additionally prove an equivalence with Mathlib's full weak-convergence framework; it proves these actual CDF limits directly.

## Excluding the claimed continuous limit

`no_continuous_cdf_limit` proves that no continuous function F can be the pointwise CDF limit of these actual empirical laws. If it were, finite-sample CDF(0)=0 forces F(0)=0, while the positive-threshold limits force F(x)=1 for every x>0. Continuity along x=1/(k+1)->0 would give F(0)=1, a contradiction.

For a continuous target distribution, convergence in law necessarily entails CDF convergence at all real points. Hence the explicit contradiction rules out the claimed continuous fractal limiting distribution. Independently, the actual normalized values themselves converge to the constant zero, so their limit is not a continuous nowhere differentiable function under a pointwise interpretation either. The result does not need to choose between different informal uses of the word fractal; the full actual empirical limit is explicitly degenerate.

## Author adversarial audit (not independent review)

1. All four original recurrence rules are proved, including s(1)=1, and uniqueness is explicit. The adjacent-pair representation is a faithful construction of the original sequence.
2. The three-bit factor 5 is verified for all eight exact Boolean cases in Lean. It is not inferred from a finite numerical search.
3. The power bound includes both adjacent coordinates and the endpoint n=8^m, so induction does not lose the next Stern value at block boundaries.
4. Squaring the argument and the exponent conversion 5^(2m)=25^m are explicit exact natural-number statements.
5. The denominator is the original real logarithmic power. Its comparison to 27^m is proved using actual logarithm and real-power lemmas, without a decimal exponent estimate.
6. The final limit holds for all positive n, not merely n=2^k or another zero-density subsequence. Natural log blocks cover every positive index.
7. Positivity is proved for every sampled value. The original log(0) index never enters the empirical PMF; n=1 is handled by the actual defining rules.
8. The empirical measure is an actual pushforward of a finite uniform PMF. Its exact tail count formula is proved, and the exceptional-index count is bounded by an actual injection into a finite interval.
9. Exact actual-CDF limits establish degeneration to the actual Dirac measure. A separate continuous-limit contradiction uses only a standard necessary CDF condition for the claimed convergence in distribution.
10. A point mass is not the asserted continuous nowhere differentiable fractal law. No claim about the vague spectral-dimension identity is needed to refute the conjunction.
11. The parent independently ran an auxiliary integer-only two-algorithm check on n<=10000, all eight residue formulas and the square block bound. This is supplementary evidence only; the Lean proof establishes the unbounded statements. The parent's checker is `round14/parent_checks/228_exact.py` and may be copied to draft-root verify.py by the parent for fresh validation.
12. Explicit main-theorem `#print axioms` audits permit only propext, Classical.choice and Quot.sound. The author report does not represent independent review. The parent performs separate adversarial reading and fresh validation before publication.

## Reproducibility

Lean source: `round5/drafts/00000000228/lean/Main.lean`. Lean 4.19.0, Mathlib pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. The author checker `round14/other/check_228.py` runs a real full `lake build`, then `lake env lean -DwarningAsError=true Main.lean`, recording logs, timings, exit codes and hashes. These are `228-build.log`, `228-strict.log`, `228-checks.json`, with final handoff metadata in `228-HANDOFF.json`. This subagent creates no TeX, PDF or PR.


Reviewed artifact hashes:

- Main.lean: `150061ab151b371dd96eb332744b8351e4c041b1307733d46d81ccd18c5298c4`
- main.tex: `1baa9cfcce08c0feb77b09ee6f059ca59465469f8866a84900ba3cddf6ca1ea1`
- main.pdf: `138b30d575c3cbfbf337ea2da172974bccb6fcbe7f010c2a381b8ce65b3493fd`
- SOURCE.md: `6ba19b08f83562332133dd91ce872803a5d37e566a9a231c45159998b7de25d8`
