# Disproof of conjecture `00000001032`

**Verdict: FALSE — the conjecture's exceptional class "v = q²+q+1 is a
prime power square" is EMPTY for every q, so the claim degenerates to
"no non-cyclic (v,k,1) planar difference set exists at all", which the
classical (91,10,1) non-cyclic difference sets of order 9 refute.**

## The conjecture (verbatim from `conjectures/00000001032.md`)

> Non-cyclic (v,k,1) planar difference sets do not exist outside
> v = q²+q+1 being a prime power square (planarity of difference-set
> realizability).

## The refutation

For every q ≥ 1 the number q²+q+1 lies strictly between consecutive
squares,

    q² < q²+q+1 < (q+1)² = q²+2q+1    (since q < 2q),

so it is never a perfect square (kernel-certified: if s² = q²+q+1 then
q < s from q² < s², and s < q+1 from s² < (q+1)² — impossible). For
q = 0, v = 1 = 1², but 1 is not a prime power (every prime power
square is ≥ 4, kernel-certified). Hence **no** v of the form q²+q+1 is
ever a prime power square: the "outside" case in the conjecture is the
entire universe, and the claim asserts that non-cyclic (v,k,1) planar
difference sets never exist.

That is false: non-cyclic planar difference sets exist classically —
the smallest are the (91,10,1) difference sets of the non-Desarguesian
projective planes of order 9 (Bruck; Hall). Here q = 9, v = 91 =
9²+9+1, and 91 = 7·13 is not even a square (kernel check:
9² < 91 < 10²) — let alone a prime power square. The conjecture's own
exceptional parameter fails to cover the known counterexamples.

## Verification

* `reproduce.py` — independent check of the squeeze for 1 ≤ q ≤ 10⁶
  (no q²+q+1 is a square), the q = 0 case, and the q = 9 parameter
  (91 not a square).
* Lean 4 (core, v4.33.1), `lean4/` — the squeeze lemmas, the
  no-square-root theorem for all q ≥ 1 (squaring monotonicity by
  trichotomy with kernel-checked strictness), the prime-power-square
  lower bound 4, and the q = 9 numeric check. All 7 audited theorems
  report `does not depend on any axioms`.

## Boundary

The kernel certifies the emptiness of the conjecture's exceptional
class (the arithmetic core, for all q) and its q = 9 instance. The
existence of non-cyclic (91,10,1) planar difference sets is a
classical result of finite geometry (Bruck / Hall; the order-9
non-Desarguesian planes), cited in prose. The conjecture as stated is
refuted in full.
