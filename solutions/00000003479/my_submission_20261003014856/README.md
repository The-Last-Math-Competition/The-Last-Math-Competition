# Disproof of conjecture `00000003479`

**Verdict: FALSE — the deterministic color-pair counting bound
2m ≤ h(h−1) forces h = Ω(√m) = Θ(n) for constant p, while the claimed
law (1+o(1))·√(np) is Θ(√n): the constant-1 concentration fails by a
factor of Θ(√n).**

## The conjecture (verbatim from `conjectures/00000003479.md`)

> Definition: Harmonious coloring is a proper coloring making
> edge-endpoint color sums pairwise distinct. Conjecture: The harmonious
> chromatic number of the random graph G(n,p) concentrates at (1+o(1))
> times the square root of np with concentration constant 1; the
> concentration holds uniformly for p at least log n/n.

## The refutation

In a harmonious coloring every unordered color pair appears on at most
one edge, so a graph with m edges harmoniously colored with h colors
satisfies the deterministic bound

    2m ≤ h(h−1)   ⟹   h ≥ √(2m).

For p = 1/2 constant (which satisfies p ≥ log n / n for all large n —
inside the conjecture's claimed uniform range), a typical realization
has m ≥ n²/6 w.h.p. (Chernoff), so typical instances force

    h ≥ √(2m) ≥ √(n²/3) = n/√3 = Θ(n),

while the claimed law gives (1+o(1))·√(np) = √(n/2) = Θ(√n). The two
scales differ by a factor of Θ(√n): no (1+o(1)) with constant 1 can
hold.

**Concrete anchor at n = 1000, p = 1/2:** typical 2m ≥ n²/3 = 333333,
and h(h−1) ≥ 333333 forces h ≥ **578** (any h ≤ 577 has h(h−1) ≤
577·576 = 332352 < 333333), while the claimed law's value
√(1000·½) = √500 < **23**. The claimed constant-1 concentration fails
by a factor of more than 25 — kernel-certified.

## Verification

* `reproduce.py` — exact integer arithmetic for the counting bound and
  the anchor; Monte-Carlo sampling of G(1000, 1/2) confirming
  m ≥ n²/6 in essentially all samples; a greedy harmonious-coloring
  lower-bound sanity check.
* Lean 4 (core, v4.33.1) — `lean4/`: the general counting lemma
  (2m ≤ h(h−1) → h² ≥ 2m), the 578-forcing anchor, the claimed value's
  bound < 23, the factor > 25, and the refutation. All 5 audited
  theorems report `does not depend on any axioms`. The color-pair count
  C(h,2) = h(h−1)/2 and the Chernoff edge bound are classical and
  cited.

## Boundary

Only the claimed √(np)-concentration is refuted (the counting bound is
independent of admissibility details); the true asymptotic of the
harmonious chromatic number of G(n,p) is not determined.
