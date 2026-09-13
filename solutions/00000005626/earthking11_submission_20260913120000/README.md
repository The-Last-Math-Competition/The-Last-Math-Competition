# Disproof of conjecture 00000005626

**Verdict: FALSE.**

The conjecture claims that every 6-point subset of the plane in general
position contains an *empty pentagon*, with Horton-type sets as the unique
counterexample family.  We exhibit an explicit 6-point set in general
position that contains **no** empty pentagon, so the first clause fails.
We also point out that the second clause is incoherent (see below).

## Definition used

A 5-element subset `S` of a finite point set is an **empty pentagon** if

1. `S` is in **strictly convex position**: every one of its five points is
   an extreme point of `conv(S)`, and
2. `conv(S)` contains **no other point** of the ambient set.

Equivalently, a 5-subset fails to be an empty pentagon if one of its points
is not extreme (interior to the hull of the other four, or collinear on an
edge), or if the omitted ambient point lies in `conv(S)`.

## Counterexample

Take the five vertices of the convex pentagon

```
P1 = (0,0)   P2 = (4,0)   P3 = (5,2)   P4 = (2,4)   P5 = (-1,2)
```

together with the interior lattice point

```
C = (2,1).
```

All coordinates are integers, so every computation below is exact.

### General position

The six points are in general position: of the `C(6,3) = 20` triples, none
is collinear (checked by exact integer cross products in `reproduce.py` and
by `decide` in `lean4/Main.lean`, theorem `general_position`).

> **Necessary deviation.**  The interior point `(2,2)` suggested as an
> "e.g." is **not** admissible: it is collinear with `P3 = (5,2)` and
> `P5 = (-1,2)`.  Among all lattice points strictly interior to the
> pentagon, `(2,1)` is the unique one that is strictly inside the hull of
> every four of the five outer vertices and keeps all six points in general
> position.  This is verified by exhaustive search in `reproduce.py`.

### Convexity

With `cross(o,a,b) = (a-o) x (b-o)`, the five consecutive turns of the
outer pentagon are

```
cross(P1,P2,P3) =  8
cross(P2,P3,P4) =  8
cross(P3,P4,P5) = 12
cross(P4,P5,P1) =  8
cross(P5,P1,P2) =  8
```

All are strictly positive, so the five outer vertices are in strictly
convex position (counter-clockwise).

### Interiority

For a counter-clockwise convex polygon, a point is strictly interior iff it
lies strictly to the left of every directed edge.  For `C = (2,1)`:

```
cross(P1,P2,C) =  4
cross(P2,P3,C) =  5
cross(P3,P4,C) =  9
cross(P4,P5,C) =  9
cross(P5,P1,C) =  5
```

All are strictly positive, so `C` is strictly inside the pentagon.  In
fact `C` is strictly inside the hull of every four of the five outer
vertices (each of the corresponding four edge products is positive).

### No empty pentagon

There are exactly six 5-subsets.  Each fails:

| 5-subset | omitted point | reason |
|---|---|---|
| `{P1,P2,P3,P4,P5}` | `C` | strictly convex, but `C` is strictly inside its hull -> not empty |
| `{P2,P3,P4,P5,C}` | `P1` | `C` is non-extreme -> not in convex position |
| `{P1,P3,P4,P5,C}` | `P2` | `C` is non-extreme -> not in convex position |
| `{P1,P2,P4,P5,C}` | `P3` | `C` is non-extreme -> not in convex position |
| `{P1,P2,P3,P5,C}` | `P4` | `C` is non-extreme -> not in convex position |
| `{P1,P2,P3,P4,C}` | `P5` | `C` is non-extreme -> not in convex position |

The number of empty pentagons is therefore **0**, refuting the conjecture.

This generalises the standard construction: an `(n-1)`-point convex polygon
plus one interior point has no empty `n`-gon, because the interior point is
in the hull of every `n`-subset that omits it, and is non-extreme in every
admissible subset that contains it.

## Incoherence of the second clause

The conjecture also asserts that "Horton type [is] the unique counterexample
family".  But the first clause says *every* 6-point set has an empty
pentagon; if that were true there would be no counterexample at all, hence
no "unique counterexample family".  The two clauses cannot both be
meaningful.  (Our counterexample is not Horton type: it is a convex
pentagon with a single interior point.)

## Correct threshold

The true threshold is **10** points, not 6.  A 9-point Horton set can be
chosen in general position with no empty pentagon; every 10-point set in
general position contains an empty pentagon.  (The 9-point Horton set is the
classical extremal configuration for the no-empty-pentagon problem.)  Our
6-point example is a small explicit witness that the claimed threshold of 6
is far too low.

## Contents

```
README.md        this file
main.tex         standalone article with full details (builds to build/main.pdf)
reproduce.py     stdlib-only exact-arithmetic verification (plus optional sympy check)
lean4/           Lean 4 formalisation (core Lean + Std, no Mathlib, no sorry/axiom)
```

## Reproducing

```sh
# Exact arithmetic check (prints PASS/FAIL, exits 0 on success)
python3 reproduce.py

# Lean formalisation (toolchain leanprover/lean4:v4.33.1)
cd lean4
export PATH="/opt/homebrew/bin:$PATH"
lake build
lake env lean Check.lean   # prints '#print axioms' for each theorem

# Article
tectonic --outdir build main.tex   # produces build/main.pdf
```

All Lean proofs are by kernel `decide` over exact `Int` arithmetic.  There
is no `sorry`, no `axiom`, no `native_decide`, and no use of `ℝ`.  The
axiom check reports that every theorem depends on **no axioms**.

## Formalised statements (`lean4/Main.lean`)

* `general_position` — no three of the six points are collinear.
* `pentagon_strictly_convex` — the five consecutive cross products of the
  outer pentagon are all strictly positive.
* `centre_strictly_inside` — `(2,1)` is strictly to the interior side of
  each of the five edges.
* `no_empty_pentagon` — all six 5-subsets fail the emptiness test, where
  convex position and hull membership are decided by exact integer
  Caratheodory/Halfplane tests.
* `conjecture_00000005626_false` — the conjunction of the above, i.e. the
  conjecture is false.
