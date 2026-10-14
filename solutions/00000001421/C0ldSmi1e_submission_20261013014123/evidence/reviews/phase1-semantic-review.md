# Independent phase-1 semantic review: conjecture 00000001421

## Verdict

**ACCEPT the finalized phase-1 plan for implementation as a disproof of the conjecture's explicit multiplicity/ordinary-spectral-gap sufficient condition, under standard total-variation cutoff semantics.** The proposed family is a genuine growing sequence of exactly-half-lazy, unweighted, symmetric, irreducible Cayley walks on finite abelian groups. Its spectral multiplicities and mixing times are derived from the actual transition matrices. The mathematics checks out. No mathematical replacement of the proposed family or its main argument is required.

This is **not** approval to assert that the source's undefined “conditional spectral gap,” “second-order behavior,” or unnamed comparison characterization has been formalized. The source does not supply mathematical definitions for those phrases. The final report must preserve the plan's explicit limitation: the stated numerical iff is false with the conventional ordinary spectral gap and total-variation mixing meanings. If an additional, nonstandard conditional quantity or extra hypothesis was intended, its meaning cannot be recovered from the source. This scope qualification is necessary for fidelity, not an additional conjecture hypothesis.

This review approves a plan, not a completed Lean development. The parent remains responsible for authorizing phase 2 and for the later full source/build/report review.

## Independence and materials

I independently read the exact English and Chinese statement and the two rule files in `1421/clean-author-input`. I asked the author to notify me when the plan was final, and read `1421/phase1-plan.md` only after that notification. My only library inspection was a search in the generic Mathlib Fourier and representation-theory sources. I did not read selector reports, other candidate proofs, competition submissions or PR solution content, or author eligibility/public metadata. No implementation was performed for this review.

## Mathematical audit

Write `N=n+4`. The state group is `G_N = ZMod 2 × ZMod N`, with order `2N`, and the support is

`S_N = {(0,h) : h ≠ 0} ∪ {(1,0)}`.

The two pieces are disjoint; their sizes are `N−1` and `1`. Negation preserves the support and zero is absent. Both coordinate directions are generated, so this is a genuine symmetric generating set, not a list of spectral labels. The displayed kernel is exactly `P(x,y)=1/2·1[x=y]+1/(2N)·1[y−x∈S_N]`. Its holding probability is exactly one half. Symmetry and translation invariance give uniform stationarity once row sums are checked. Every difference is a sum of at most two supported increments; holding fills any shorter path. Consequently every entry of `P²` is positive. These establish all usual finite-walk prerequisites without silently imposing them.

For an actual character `χ` on the second factor and sign character indexed by `ε`, convolution gives

`λ_(ε,χ) = 1/2 + (sum_(h≠0) χ(h) + (−1)^ε)/(2N)`.

The character sum is `N−1` for the trivial character and `−1` otherwise. Thus the spectrum, including multiplicities, is:

| Eigenvalue | Multiplicity |
|---|---:|
| `1` | `1` |
| `q=1−1/N` | `1` |
| `r=1/2` | `N−1` |
| `s=1/2−1/N` | `N−1` |

For `N≥4`, `1>q>r>s>0`. The proposed complete character basis makes these actual algebraic multiplicities, rather than merely counts of candidate eigenfunctions. The ordinary spectral gap, including the absolute-eigenvalue version for this positive spectrum, is `1/N`. The literal minimum nontrivial transition eigenvalue is `s`, of multiplicity `N−1`, so its multiplicity/gap ratio is `N(N−1)`. If “minimal nontrivial eigenvalue” instead means the smallest positive eigenvalue of `I−P`, that eigenvalue is `1/N`, of multiplicity `1`, and the ratio is `N`. Both divergences are correct. The plan therefore does not confuse the minimum transition eigenvalue with the gap mode.

The proposed power formula

`P^t(x,y) = [1 + σ q^t + (ND−1)(r^t+σs^t)]/(2N)`

has the correct identity matrix at `t=0`. Here `σ` records equality of the first coordinates and `D` equality of the second coordinates. It is exactly the decomposition into the four constant/mean-zero coordinate projections. The proof must establish this identity for the powers of the already-defined kernel; adopting it as a new definition of evolution would fail the bridge requirement.

For `t≥1`, the two sign inequalities are valid:

`r^t+s^t ≤ (r+s)^t=q^t`,

`(N−1)(r^t−s^t) ≤ q^t`.

For the latter, use `(N−1)(r−s)=q` and the geometric factorization of `r^t−s^t`; the sum of mixed monomials is bounded by `(r+s)^(t−1)`. These show that every stationary deviation has a nonnegative sign in the starting first-coordinate block and a nonpositive sign in the other block. Summing the deviations proves the actual total-variation distance is `q^t/2`. At time zero the distance is `1−1/(2N)`. Translation invariance makes this the worst-start distance as well. I checked all four combinations of the two coordinate equalities; none reverses the required sign.

The genuine least-threshold mixing times consequently satisfy `t_N(3/4)=1`. If `T_N=t_N(1/4)`, then `q^T_N≤1/2`. Bernoulli's inequality yields `1−T_N/N≤1/2`, hence `T_N≥N/2≥2`. Thus both the state-space size and the ordinary mixing time diverge; there is no bounded-time or fixed-group loophole.

The actual quarter-to-three-quarter transition width is `W_N=T_N−1>0`, and

`T_N/W_N = 1 + 1/(T_N−1) → 1`.

It is also uniformly at most `2`. Therefore the stated time/window separation fails. The usual quantified total-variation cutoff condition independently fails at tolerance `1/4`, since `t_N(1/4)/t_N(3/4)=T_N→∞`, rather than tending to `1`. This is a valid contradiction to the sufficient direction of the explicit iff; the necessity direction need not be addressed.

## Exact-statement fidelity and limits

1. **Metric and window:** The original names no norm and provides no precise rule for the window. The report must explicitly identify total variation and its fixed-threshold transition width. It must not suggest that the source explicitly specified those definitions. They are standard, substantive interpretations; the computed distances and least mixing times justify them. Proving failure of the quantified ordinary TV cutoff condition, in addition to one time/window ratio, makes the conclusion robust within that interpretation. Do not replace the window by an arbitrary scalar sequence supplied alongside the walk.
2. **Conditional gap:** The source's word “conditional” does not define an event, restriction, operator, or normalization. No new conditional quantity should be invented and then equated with the ordinary gap. The current plan appropriately identifies the gap it actually computes and discloses the textual ambiguity.
3. **Characters:** The support is not itself generally a group. The relevant actual characters are those of the group generated by the support, which here is all of `G_N`. The report should use that precise wording. For a finite abelian group, these complex group characters are the one-dimensional irreducible characters. Character count, eigenbasis completeness, and multiplicity must be connected, not independently stipulated.
4. **Final comparison clause:** An undefined comparison characterization cannot be independently proved or refuted. It also cannot rescue the explicit sufficient condition without adding content absent from the problem. The report should say the counterexample falsifies that sufficient condition and should not claim a general theorem about Diaconis–Saloff-Coste comparison methods.
5. **Scope of the Lean theorem:** A theorem giving an actual counterexample to the explicit numerical criterion is appropriate. A proposition named after the original conjecture must not conceal simplified scalar definitions and be presented as a literal formalization of every undefined phrase.

## Required theorem obligations for phase 2

The final report and aggregate Lean theorem must expose, or directly cite proved lemmas for, the following facts:

- The actual finite abelian groups, their orders `2(n+4)`, and divergence of these orders.
- The precise support, its cardinality, exclusion of zero, symmetry, and generation of the entire state group.
- Nonnegative stochastic kernel entries, exact half holding, symmetry/uniform stationarity, and actual irreducibility (positive two-step entries is sufficient).
- The actual additive characters, their complete basis of complex-valued functions, and the Markov-operator action on that basis. The list must be exhaustive, including the uniqueness of the stationary character/eigenvalue.
- The full characteristic polynomial of the complexified transition matrix, real ordering of its four eigenvalues, ordinary spectral-gap identification, and both genuine root/eigenspace multiplicity computations.
- The matrix-power formula and the finite-sum absolute-value TV formula, including `t=0` and all starting states; a separately defined closed scalar profile is insufficient.
- Nonemptiness of the threshold-time set for every positive tolerance and least-time attainment/minimality before using `sInf` as a mixing time.
- Exact `t_N(3/4)=1`, the lower bound and divergence of `t_N(1/4)`, positive real window denominators, divergence of both spectral ratios, convergence of the actual total/window ratio to `1`, and its failure to diverge to infinity.
- A precisely defined, quantified ordinary total-variation cutoff predicate and its negation at the actual family.

Two small drafting corrections to the plan should be observed during implementation: section 7 calls the generic cutoff predicate “optional” although the aggregate theorem requires `¬ HasTVCutoff`; make its definition and proof mandatory. Also include the state-space cardinality divergence explicitly in the aggregate obligations rather than leaving it only in the surrounding prose. Neither correction changes the mathematics.

## Release gate

The phase-1 mathematical route is approved. No phase-2 implementation or later submission may omit the above bridges, treat the supplied formulas as assumptions, or remove the stated interpretation limits. A later review must inspect the complete Lean definitions and all theorem hypotheses, compile the project with the pinned toolchain, check for admissions or untrusted shortcuts, and compare the complete LaTeX/PDF account to the formal claims. None of those completion checks has yet been performed by this phase-1 review.
