# Lean 4 formalisation — Conjecture 00000001065 is FALSE

Core Lean 4 (`import Std` only), no Mathlib, no `sorry`, no `axiom`, no
`native_decide`. Toolchain: `leanprover/lean4:v4.33.1`.

## What is proved

The decisive `q = 2` case, completely.

Points of `F_2^2` are indexed row-major: `(0,0) -> 0`, `(0,1) -> 1`,
`(1,0) -> 2`, `(1,1) -> 3`. A subset is a 4-bit `Fin 16` bitmask. The six lines
of `F_2^2` are
`{0,2}, {1,3}` (horizontal), `{0,1}, {2,3}` (vertical),
`{0,3}, {1,2}` (diagonal).

* `IsKakeya m` — contains a full line in each of the 3 directions.
* `IsNikodym m` — for every point `p`, there is a line through `p` whose
  *other* points all lie in the set (`p` itself may be exceptional).

Theorems:

* `nikodym_two` — `{(0,0),(0,1)}` is Nikodym.
* `kakeya_three` — `{(0,0),(0,1),(1,0)}` is Kakeya.
* `nikodym_min` — some Nikodym set has size 2.
* `kakeya_min` — some Kakeya set has size 3.
* `no_kakeya_lt_three` — every subset of size `< 3` fails to be Kakeya.
* `no_nikodym_lt_two` — every subset of size `< 2` fails to be Nikodym.
* `difference_not_q_minus_one` — `(2 : Int) - 3 = -1 ∧ (1 : Int) ≠ -1`.
* `conjecture_00000001065_false` — collects all of the above.

Hence min Kakeya `= 3`, min Nikodym `= 2`, difference `= -1`, whereas the
conjecture predicts `q - 1 = 1`.

## Note on the exact statement

The conjectured statement `∀ S : List (Fin 2 × Fin 2), S.length = 2 → ...`
cannot be discharged by `decide`, because the universal quantifier ranges over
the infinite type `List (Fin 2 × Fin 2)` and has no decidable instance. We
therefore state the minimality facts over the finite type `Fin 16` of all
`2^4 = 16` bitmasks, which is exactly the "enumerate all 16 masks" route. The
list witnesses are connected to the masks by `maskOf`.

## Build and audit

```bash
export PATH="/opt/homebrew/bin:$PATH"
lake build
lake env lean Check.lean
```

Expected: `lake build` exits `0`, and every theorem in `Check.lean` depends on
no axioms beyond `propext` (which is used by the `decide` tactic); in
particular there is no `sorryAx` and no `ofReduceBool`. The pure arithmetic
theorem `difference_not_q_minus_one` depends on no axioms at all.
