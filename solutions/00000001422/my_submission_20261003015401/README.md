# Disproof of conjecture `00000001422`

**Verdict: FALSE — on the regular graph Kₙ the ratio
t_mix(interchange)/t_mix(SRW) is (1/2)·n·ln n → ∞, not 2: the
constant-2 concentration (with variance O(1/n)) fails on the most basic
regular graph family.**

## The conjecture (verbatim from `conjectures/00000001422.md`)

> Definition: The interchange process is the particle system on [n]
> whose labels propagate via random adjacent transpositions; its
> spectral gap equals that of the random walk (proven by
> Caputo–Liggett–Richthammer). Conjecture: On regular graphs, the ratio
> of the mixing time of the interchange process to that of the random
> walk concentrates around 2 (label mixing is exactly a constant factor
> 2 slower than single-particle mixing), with variance O(1/n).

## The counterexample: Kₙ (regular)

1. **Random walk on Kₙ mixes in ONE step.** After a single step the
   walk is uniform on the n−1 vertices other than the start; the total
   variation distance to the uniform stationary law is exactly
   (1/2)·(|0 − 1/n| + (n−1)·|1/(n−1) − 1/n|) = 1/n ≤ 1/4 for all
   n ≥ 4 (kernel-certified in cross-multiplied form). So
   t_mix(SRW) = **1**.
2. **Interchange process on Kₙ = random transpositions** (every pair is
   adjacent). Diaconis–Shahshahani (1981, classical cutoff): its mixing
   time is (1/2)·n·ln n. At n = 100: ln 100 > 4 (since e < 3 gives
   e⁴ < 3⁴ = 81 < 100), so t_mix(interchange) > (1/2)·100·4 = **200**
   (numerically ≈ 230).
3. **The ratio is (1/2)·n·ln n → ∞**, not 2 — off by a factor of ~115
   already at n = 100, growing without bound. The claimed O(1/n)
   variance around the constant 2 is incompatible with a diverging
   ratio.

Note the conjecture's own premise (the CLR spectral-gap equality) is
not in dispute — spectral gap and mixing time are different parameters,
and the gap equality is compatible with wildly different mixing times
here.

## Verification

* `reproduce.py` — exact TV computation of the one-step Kₙ walk for
  n = 4..200 (always exactly 1/n), Monte-Carlo confirmation, and the
  Diaconis–Shahshahani cutoff values vs the claimed 2.
* Lean 4 (core, v4.33.1) — `lean4/`: the general TV ≤ 1/4 form
  (t_mix = 1 for n ≥ 4), the n = 100 TV components, the e⁴ < 100 anchor
  for ln 100 > 4, the ratio bound 200 > 2, and the refutation. All 5
  audited theorems report `does not depend on any axioms`. The
  random-transpositions cutoff (Diaconis–Shahshahani) and e < 3 are
  classical and cited.

## Boundary

Only the constant-2 ratio claim on regular graphs is refuted (Kₙ
suffices). The CLR spectral-gap theorem is not disputed; the genuine
interchange-mixing theory on other families is not addressed.
