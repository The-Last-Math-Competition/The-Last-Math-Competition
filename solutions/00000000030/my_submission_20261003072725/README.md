# Disproof of conjecture `000000030`

**Verdict: FALSE (under the definitions as given) — inside [N] a set of
positive density is exactly a nonempty set, so "intersective" means
S = [N]; but |{a² : a ∈ A}| ≤ |A| ≤ N^{1/2−c} < N.  The single
instance N = 4, A = {1, 2} satisfies the size hypothesis for every
c ≥ 0 (|A| = 2 = 4^{1/2}) while its square image {1, 4} misses the
nonempty witness {3}.**

## The conjecture (verbatim from `conjectures/000000030.md`)

> Sparsification of intersective sets: there exists an absolute c > 0
> such that whenever A ⊂ [N] with |A| ≥ N^{1/2−c}, the set
> {a² : a ∈ A} is intersective (it has nonempty intersection with
> every set of positive density).

## The refutation

Within the finite interval [N], a subset D has positive density
|D|/N > 0 exactly when D is nonempty.  So the conjecture's
"intersective" — meeting every set of positive density — means meeting
every nonempty subset of [N], in particular every singleton {x}, which
forces S = [N].  Kernel-certified as `singleton_reduction`.

But the square image is no larger than A itself, and the size
hypothesis only guarantees |A| ≥ N^{1/2−c} with 1/2 − c < 1 — far
below N.  One concrete instance refutes every absolute c ≥ 0 at once:

    N = 4,  A = {1, 2}:   |A| = 2 = 4^{1/2} ≥ 4^{1/2−c}  (c ≥ 0),
    square image S = {1, 4},
    witness D = {3}:  nonempty (density 1/4 > 0),  S ∩ D = ∅.

The exponent bound 4^{1/2−c} ≤ 4^{1/2} = 2 for c ≥ 0 uses the
monotonicity of real exponentiation (cited in prose; kernel anchor
2·2 = 4).  Hence for EVERY c > 0 there is an A satisfying the size
hypothesis whose square image is not intersective.

## Verification

* `reproduce.py` — enumerates all 15 nonempty subsets of [4]: {1, 4}
  fails intersectivity with witnesses {2}, {3}, {2, 3}; confirms the
  size hypothesis |A| ≥ 4^{1/2−c} for representative c values; and
  checks the general principle "meets every nonempty subset ⟺ S = [N]"
  over all 16 subsets of [4].
* Lean 4 (core, v4.33.1), `lean4/` — the singleton reduction
  (intersectivity forces S = [N], applied to the singleton {x}), the
  instance refutation (the witness {3} for S = {1, 4} in [4]), and the
  size anchor 2·2 = 4.  All 4 audited theorems report `does not depend
  on any axioms`.

## Boundary

The refutation is under the conjecture's own literal definition of
"intersective" (nonempty intersection with every positive-density set
inside [N]), which degenerates to S = [N].  The standard literature
notion (every positive-density set contains two elements differing by
an element of the set — the Sárközy/Furstenberg sense) is a different
statement and is not addressed.  Under the literal definition the
conjecture is refuted in full for every absolute c.
