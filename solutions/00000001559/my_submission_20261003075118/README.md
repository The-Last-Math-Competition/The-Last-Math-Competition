# Disproof of conjecture `00000001559`

**Verdict: FALSE — the conjecture's own displayed expression
(1+√3)/2·(√3−1) evaluates to EXACTLY 1 (difference of squares:
((√3)²−1²)/2 = (3−1)/2), so the claim asserts r₆ = 1.  But six disks
of radius 0.62 already cover the unit disk (six centers at the hexagon
vertices, rigorously certified by the sector-convexity argument), so
r₆ ≤ 0.62 < 1: the claimed quadratic-algebraic value is wrong.**

## The conjecture (verbatim from `conjectures/00000001559.md`)

> Definition: The n-disk covering radius r_n of the unit disk is the
> minimal radius of n equal disks covering it. Conjecture: r₆ is an
> explicit quadratic algebraic number of the (1+√3)/2·(√3−1) type,
> realized by one central disk and five symmetric annular disks; and
> r₇ is a cubic algebraic number.

## The refutation

1. **The displayed value is exactly 1 (kernel-certified in ℤ[√3]).**
   (1+√3)/2·(√3−1) = ((√3)+1)·((√3)−1)/2 = ((√3)²−1²)/2 = (3−1)/2 = 1.
   The kernel works in ℤ[√3] (integer pairs (a,b) = a + b·√3 with
   (a,b)·(c,d) = (ac+3bd, ad+bc)) and certifies
   (1,1)·(−1,1) = (2,0): the claimed "quadratic algebraic number" is
   precisely the rational number 1.

2. **r₆ ≤ 0.62 < 1.** Place six centers at the vertices of the
   regular hexagon of radius 1/2; cover with radius 0.62.  The unit
   disk splits into six 60° sectors around the centers; the squared
   distance to the sector's center is convex on the (convex) sector,
   so its maximum is at a sector corner, and the corner values are
   1/4 (origin) and 1 + 1/4 − cos 30° = 5/4 − √3/2 ≤ 5/4 − 0.866
   = 0.384 < 0.3844 = 0.62².  Hence covered: r₆ ≤ 0.62 < 1.
   (Literature optimum: r₆ ≈ 0.5559; the one-central-plus-five
   configuration claimed in the conjecture is not optimal either.)

Therefore r₆ ≠ 1: the claimed quadratic-algebraic value is refuted.
(The r₇ clause is not needed for the refutation and is not addressed.)

## Verification

* `reproduce.py` — the difference-of-squares evaluation; the
  sector-convexity certificate (corner squared-distances < 0.62²);
  a fine-grid brute-force cross-check (2000×~2000 points, max squared
  distance 0.3840 ≤ 0.3844).
* Lean 4 (core, v4.33.1), `lean4/` — the ring ℤ[√3] with its
  multiplication, the certified product (1,1)·(−1,1) = (2,0) (i.e.
  the claimed value = 1), and the comparisons 100 ≠ 62, 62 < 100.
  All 3 audited theorems report `does not depend on any axioms`.

## Boundary

The kernel certifies the algebra (the claimed value = 1) and the
value comparison; the covering certificate combines the
sector-convexity argument (prose) with the script's corner checks and
fine-grid sweep.  The r₇ clause is not needed for the refutation.
