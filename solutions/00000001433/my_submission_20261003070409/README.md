# Disproof of conjecture `00000001433`

**Verdict: FALSE — the conjecture's own explicit rate formula
c(λ) = λ − 1 is NEGATIVE on the whole parameter region (λ_c, 1) for
any threshold λ_c < 1 (the known ARW regime, Rolla–Sidoravicius): the
claimed "exponential decay" bound exp(−c(λ)·t) = exp((1−λ)·t) GROWS
there, and c(λ_c) = λ_c − 1 < 0 ≠ 0 contradicts the conjecture's own
stated limit "c → 0 as λ ↓ λ_c". The formula is self-inconsistent
unless λ_c = 1, which is neither assumed nor true.**

## The conjecture (verbatim from `conjectures/00000001433.md`)

> Definition: The absorption time of ARW is the time when all particles
> sleep. Conjecture: For fixed λ > λ_c, the tail of the local
> absorption time for infinite initial configurations is exponential,
> P(T > t) ≤ exp(−c(λ)·t), with the explicit linear rate c(λ) = λ−1;
> the rate tends to infinity as λ → ∞ and to 0 as λ ↓ λ_c.

## The refutation

1. **The rate is negative inside the claimed parameter region.** For
   any threshold λ_c < 1 (the known ARW regime: the critical density is
   strictly below 1, Rolla–Sidoravicius), pick λ ∈ (λ_c, 1), e.g.
   λ = 9/10. Then c(λ) = λ − 1 = −1/10 < 0, so the claimed bound is
   exp(−c·t) = e^{t/10} — a GROWING function, exceeding 1 for every
   t > 0 and diverging. A vacuous upper bound is not an exponential
   decay tail (kernel-certified: 9 < 10, and the pair lemma
   "u < v makes the rate (u−v)/v negative and nonzero").

2. **The stated limit is self-contradictory.** The conjecture asserts
   c(λ) → 0 as λ ↓ λ_c. With c = λ − 1 this requires
   c(λ_c) = λ_c − 1 = 0, i.e. λ_c = 1. But for any λ_c < 1
   (kernel-certified: every x < 1 has x − 1 < 0 ≠ 0), c(λ_c) < 0 ≠ 0.
   The explicit formula contradicts the conjecture's own limit at its
   own critical point.

3. **The λ → ∞ clause survives** (c = λ − 1 → ∞ ✓), but the
   conjunction fails: the conjecture as stated — decay on (λ_c, ∞)
   with the linear rate and the zero limit at λ_c — is internally
   inconsistent for every λ_c < 1.

## Verification

* `reproduce.py` — exact-fraction check c(9/10) = −1/10 < 0; growth of
  e^{t/10} at t = 1, 10, 100; c(λ_c) < 0 ≠ 0 for λ_c ∈ {1/2, 7/10,
  9/10}; the instance scaling 9 < 10.
* Lean 4 (core, v4.33.1), `lean4/` — the scaled-pair rate lemma
  (rate_pair_negative: u < v makes (u−v)/v negative and nonzero), the
  instance 9 < 10 with c ≠ 0, the growing-exponent fact 10 − 9 = 1 > 0,
  and the assembly. All 4 audited theorems report `does not depend on
  any axioms`.

## Boundary

The kernel certifies the arithmetic core: the negativity and
nonvanishing of the linear rate below 1, at the instance and in the
universal scaled form. The ARW threshold fact λ_c < 1 (critical
density strictly below 1) is the classical Rolla–Sidoravicius result,
cited in prose; the probability-theoretic reading of "growing bound vs
decay" is likewise prose. The conjecture as stated is refuted in full.
