# Lean formalisation (conjecture 00000004007)

Toolchain: `leanprover/lean4:v4.33.1` (see `lean-toolchain`).
Core Lean only: `import Std`, **no Mathlib**, no `sorry`, no `axiom`,
no `native_decide`, no `ℝ`.  (Core Lean has no real numbers, and `decide`
cannot reduce `Rat` operations, so everything is kept in `Nat`.)

## Build

```bash
export PATH="/opt/homebrew/bin:$PATH"
cd lean4 && lake build            # exit 0
lake env lean Check.lean          # axiom audit
```

## What is formalised

The file `Main.lean` formalises the **arithmetic core** of the refutation,
and nothing else.

Write `q` for the conjugate exponent of `p` (`1/p + 1/q = 1`, so `q > 1`
whenever `1 < p < ∞`).  Because the p-variation is the p-th root of a
supremum it is homogeneous of degree 1, `‖aX‖ = |a|·‖X‖`.  At `X = Y ≠ 0`
the conjectured inequality
`‖X+Y‖ ≤ (‖X‖^q + ‖Y‖^q)^{1/q}` becomes
`2 ≤ 2^{1/q}`, equivalently `2^q ≤ 2`, which is false for every `q > 1`.
That false inequality is the entire content of the obstruction, and it is
what is proved here:

* `q_eq_two_fails` — `¬ (2^2 ≤ 2)`, i.e. `¬ (4 ≤ 2)`.  The case `p = 2`
  (`q = 2`), by `decide`.
* `q_eq_two` — `2^2 = 4`, recorded for transparency, by `decide`.
* `q_eq_three_halves_fails` — `¬ (2^3 ≤ 2^2)`, i.e. `¬ (8 ≤ 4)`.  The case
  `p = 3` (`q = 3/2`; `2^{3/2} ≤ 2 ⟺ 2^3 ≤ 2^2`), by `decide`.
* `pow_two_gt_two` — `∀ q : Nat, 1 < q → 2 < 2^q`.  The general arithmetic
  fact (`q > 1` gives `2^q > 2`, so `2^q ≤ 2` fails), proved by induction
  in core Lean.
* `conjecture_00000004007_false` — collects the two explicit instances and
  the general fact, with a comment explaining that homogeneity reduces the
  conjecture to precisely these false inequalities.

## Axiom audit (`Check.lean`)

`Check.lean` runs `#print axioms` for each theorem.  The two `decide`-based
theorems and `q_eq_two` print

```
'Tlmc4007.q_eq_two_fails' does not depend on any axioms
'Tlmc4007.q_eq_two' does not depend on any axioms
'Tlmc4007.q_eq_three_halves_fails' does not depend on any axioms
```

while `pow_two_gt_two` and `conjecture_00000004007_false` depend only on the
core axioms `propext` and `Quot.sound` (introduced by `omega`/`by_cases`).
There is **no `sorryAx`** and **no `ofReduceBool`**.

## What is NOT formalised in Lean

* The p-variation itself as a real-valued functional on paths (no `ℝ` in
  core Lean): the definition `‖X‖ = (sup over partitions of Σ|increments|^p)^{1/p}`.
* The homogeneity `‖aX‖ = |a|·‖X‖` and the reduction `X = Y` of the
  conjecture to `2^q ≤ 2`.
* The concrete table of values for a two-point unit-step path and the
  raw-supremum / `p = 1` normalisations.

These are stated mathematically in `../main.tex` and verified with exact
rational arithmetic in `../reproduce.py`.  The Lean file supplies the exact
arithmetic inequalities on which the refutation rests; the failure is
elementary (`X = Y`), and this is precisely why the stated inequality
cannot be correct.
