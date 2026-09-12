# Lean 4 formalization: a point-transitive KTS(9) (disproof of conjecture 00000008420)

This directory contains a fully machine-checked, axiom-free Lean 4 proof that
there exists a point-transitive Kirkman triple system of order 9, refuting the
clause of TLMC conjecture 00000008420 asserting that "the smallest order of a
KTS with a transitive automorphism is the point-transitive type of order 15".

## The construction

The counterexample is the line system of the affine plane `AG(2,3)`:

- points are the 9 elements of `F_3^2` (modelled as `Fin 3 x Fin 3`, i.e. with
  wrapping mod-3 arithmetic, which carries exactly the additive structure of
  `ZMod 3` used here; the Lean 4 core has no `ZMod` without a Mathlib
  dependency, and this project is deliberately dependency-free);
- the 12 lines are indexed by `k : Nat` (`lineMem`):
  - `k = 3*m + b`, `k < 9`: `{(x, m*x + b) : x in F_3}` (slope `m`, intercept `b`);
  - `k = 9 + c`, `k <= 11`: the vertical line `{(c, y) : y in F_3}`.

## What is proved (all by `decide` over explicit finite enumerations)

| theorem | statement (as a Boolean check = true) | content |
|---|---|---|
| `sts_property` | 81 ordered pairs `(p,q)`, `p != q` | exactly one of the 12 lines contains both: Steiner triple system |
| `resolvable` | 4 classes `[0,1,2] [3,4,5] [6,7,8] [9,10,11]` | each class = 3 lines, every point on exactly one line of the class (pairwise disjoint + covering), classes partition the 12 lines; `4 = (9-1)/2` |
| `translation_invariant` | all `v` in `F_3^2`, all lines `k` | there is a line `k'` with `lineMem k p = lineMem k' (p + v)` for all `p`: translations are automorphisms |
| `transitive` | all `p, q` in `F_3^2` | some translation `v` maps `p` to `q`: the translation group acts transitively |
| `refute` | `9 < 15` | the point-transitive KTS order is strictly below the claimed minimum 15 |

## How to build and check

Requires [elan](https://elan.lean-lang.org) (the pinned toolchain
`leanprover/lean4:v4.33.1` is fetched automatically). No Mathlib, no network
beyond the initial toolchain download.

```sh
lake build          # compiles Main.lean
lake env lean Check.lean   # prints #eval results and #print axioms for every theorem
```

Expected output of `Check.lean`:

```
true
true
true
true
9
12
'Tlmc8420.sts_property' does not depend on any axioms
'Tlmc8420.resolvable' does not depend on any axioms
'Tlmc8420.translation_invariant' does not depend on any axioms
'Tlmc8420.transitive' does not depend on any axioms
'Tlmc8420.refute' does not depend on any axioms
```

Every theorem is proved by `decide` from closed Boolean expressions over the
9 points and 12 lines, so the kernel performs the entire finite enumeration;
there are no axioms (in particular no `sorryAx`, no `Classical.choice`, not
even `propext`).

Note on the encoding: the nine points are generated with `List.finRange`
rather than numeral literals because the core `OfNat (Fin n)` instances are
elaborated with `propext`; using `List.finRange` keeps every definition and
theorem literally axiom-free.

## File map

- `Main.lean` — the construction and all theorems (namespace `Tlmc8420`);
- `Check.lean` — `#eval` of the Boolean witnesses and `#print axioms` of every theorem;
- `lakefile.toml`, `lean-toolchain` — project configuration (target `Main`).
