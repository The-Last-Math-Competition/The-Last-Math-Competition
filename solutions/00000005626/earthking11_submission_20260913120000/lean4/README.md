# Lean 4 formalisation — conjecture 00000005626 is false

Toolchain: `leanprover/lean4:v4.33.1` (pinned in `lean-toolchain`).
Core Lean + `Std` only.  **No Mathlib, no `ℝ`, no `sorry`, no `axiom`, no
`native_decide`.**  All arithmetic is exact `Int` arithmetic on `Int × Int`
points; all proofs are kernel `decide`.

## The counterexample

Five strictly convex outer vertices plus one interior lattice point:

```
P1 = (0,0)   P2 = (4,0)   P3 = (5,2)   P4 = (2,4)   P5 = (-1,2)
C  = (2,1)   -- strictly interior, all six points in general position
```

Note: `(2,2)` is collinear with `P3` and `P5`, so it is not in general
position.  `(2,1)` is the unique interior lattice point that is strictly
inside the hull of every four outer vertices and keeps the set in general
position.

## Files

* `Main.lean` — definitions and the five theorems.
* `Check.lean` — `import Main` + `#print axioms` for each theorem.
* `lakefile.toml`, `lean-toolchain` — build configuration.

## Definitions

* `cross o a b = (a.1 - o.1) * (b.2 - o.2) - (a.2 - o.2) * (b.1 - o.1)`.
* `inTri u v w p` — `p` in the closed triangle `uvw`, via same-sign cross
  products (handles either orientation).
* `inConv4` / `inConv5` — hull membership by Caratheodory's theorem in
  dimension 2 (some triple contains the point).  Both are exact `Bool`
  computations.
* `strictlyConvex5 a b c d e` — every one of the five points is extreme
  (not in the hull of the other four).  This test is **order-independent**.
* `emptyPentWith q a b c d e` — the five points are strictly convex and
  the sole remaining point `q` is not in their hull.  Since the ambient set
  has exactly six points, this is exactly `¬ empty pentagon`.

## Theorems

| theorem | statement |
|---|---|
| `general_position` | no three of the six points are collinear (20 triples) |
| `pentagon_strictly_convex` | the five consecutive cross products are all `> 0` |
| `centre_strictly_inside` | `C = (2,1)` is strictly on the interior side of each of the five edges |
| `no_empty_pentagon` | all six 5-subsets fail `emptyPentWith` |
| `conjecture_00000005626_false` | conjunction of the above |

## Building and checking

```sh
export PATH="/opt/homebrew/bin:$PATH"
lake build
lake env lean Check.lean
```

`Check.lean` prints, for each theorem, `does not depend on any axioms`
(no `sorryAx`, no `ofReduceBool`).
