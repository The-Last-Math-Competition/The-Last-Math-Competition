# Disproof of conjecture `00000004172`

**Verdict: FALSE under both readings — the true boundary density is
1/2, not 5/8.  (a) If "sets of density below 5/8 can completely
avoid nontrivial sum representations" means ALL such sets avoid
them: the interval A = {1, …, 60} ⊆ [1, 100] has density 3/5 = 0.6
< 5/8 = 0.625, yet 1770 ordered nontrivial sum pairs land in A
(1 + 1 = 2, 1 + 2 = 3, …).  (b) If it means THERE EXIST sum-free
sets of every density below 5/8: impossible for densities in
(1/2, 5/8) — the largest sum-free subset of [1, N] has size
⌈N/2⌉ (density exactly 1/2, attained by the odd numbers: odd +
odd = even ∉ odds), so no density-3/5 set can be sum-free.**

## The conjecture (verbatim from `conjectures/00000004172.md`)

> Definition: The dense circle method is the analysis of sum
> representations for positive-density sets. Conjecture: The
> boundary density for the method to be transferable is 5/8, and
> sets of density below this value can completely avoid nontrivial
> sum representations. (boundary density 5/8 of the dense circle
> method)

## The refutation

The sum-representation threshold for subsets of [1, N] is a
classical, sharp constant — and it is not 5/8.  A set with no
nontrivial sum representation (a + b ∉ A for all a, b ∈ A) is
sum-free; the largest sum-free subset of [1, N] has size ⌈N/2⌉
(Diananda–Yap; attained by the odd numbers, since odd + odd = even
∉ odds), i.e. density exactly 1/2.  Consequently:

* every set of density > 1/2 — in particular any density in
  (1/2, 5/8), e.g. the interval {1, …, 60} with density 3/5 = 0.6
  in [1, 100] — carries nontrivial sum representations (1770
  ordered pairs at N = 100);
* sum-free sets exist only at densities ≤ 1/2, so "sets of density
  below 5/8 can avoid" fails for every density in (1/2, 5/8).

The 5/8 constant is wrong under both readings; the genuine boundary
is 1/2, with the odds as the extremal example (brute-force verified
at N = 6, 8, 10).

## Verification

* `reproduce.py` — the dense interval {1..60} (density 0.6 < 0.625,
  1770 sum pairs inside); the odd-number sum-free set of size 50;
  the brute-force max-sum-free confirmation at N = 6, 8, 10.
* Lean 4 (core, v4.33.1), `lean4/` — `density_below` (3·8 < 5·5),
  `has_sums` (1+1 = 2, 1+2 = 3 ∈ A), `odds_sumfree`,
  `ceiling_exceeded` (60 > 50), `conjecture_refuted`.  All 5
  audited theorems report `does not depend on any axioms`.

## Boundary

The kernel certifies the density comparison, the sum-pair witnesses,
and the ceiling violation; the ⌈N/2⌉ sum-free ceiling (Diananda–Yap)
is classical, cited in prose and brute-force confirmed by the script
at small N.  The 5/8 boundary claim is refuted under both readings;
the true constant is 1/2.
