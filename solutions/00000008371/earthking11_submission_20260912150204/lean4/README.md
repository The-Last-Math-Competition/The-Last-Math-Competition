# Lean 4 formalisation — disproof of conjecture `00000008371`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main` in
`lakefile.toml`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

Verified on the pinned toolchain: `lake build` succeeds, and `Check.lean` reports
only the standard axioms `propext`, `Classical.choice`, `Quot.sound` — in
particular no `sorryAx` and no Mathlib dependency.

## What is formalised

The conjectured count is

```lean
def spaceTreeFormula (n : Nat) : Rat :=
  (treeCount n : Rat) / 2
```

where `treeCount n = Nat.factorial (n - 2) * Nat.factorial (n - 3)`, so
`spaceTreeFormula n = (n-2)! (n-3)! / 2`. The vertex count of the asserted Johnson
graph `J(n,2)` is

```lean
def johnsonVertices (n : Nat) : Nat := n * (n - 1) / 2
```

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `formula_at_3` | `spaceTreeFormula 3 = 1/2` | Failure 1: the count is not integral |
| `no_count_is_half` | `¬ ∃ m : Nat, (m : Rat) = spaceTreeFormula 3` | Failure 1: no cardinality is `1/2` |
| `formula_at_4` / `formula_at_5` / `formula_at_6` | `F = 1`, `6`, `72` | formula values |
| `johnson_3` / `johnson_4` / `johnson_5` / `johnson_6` | `C(n,2) = 3, 6, 10, 15` | Johnson vertex counts |
| `natCast_mul_two_div_two` | `((a*2 : Nat) : Rat)/2 = a` | denominator cancellation |
| `mul_two_ne_one` | `∀ m : Nat, m*2 ≠ 1` | parity obstruction |
| `formula_ne_johnson_4` | `F(4) ≠ C(4,2)` (`1 ≠ 6`) | Failure 2 |
| `formula_ne_johnson_5` | `F(5) ≠ C(5,2)` (`6 ≠ 10`) | Failure 2 |
| `formula_ne_johnson_6` | `F(6) ≠ C(6,2)` (`72 ≠ 15`) | Failure 2 |
| `conjecture_00000008371_false` | conjunction of Failure 1 and the three Failure 2 instances | the disproof |

## Proof strategy

All closed numerical facts are decided on closed numerals:

- `Nat.factorial` is a structural recursion, so `decide` evaluates `treeCount n`
  for closed `n`; `Rat` division by a closed denominator is handled by rewriting
  the even numerator and cancelling (see `natCast_mul_two_div_two`), because the
  kernel does not reduce `Rat` normalization directly — `decide` on `Rat`
  arithmetic with `/` does *not* work in this toolchain;
- `formula_at_3` is a literal simplification: `1! * 0! = 1`, so
  `spaceTreeFormula 3 = (1 : Rat) / 2 = 1/2`;
- `formula_at_4`, `formula_at_5`, `formula_at_6` rewrite the even numerator
  (`2`, `12`, `144`) and cancel the denominator with
  `natCast_mul_two_div_two`;
- `no_count_is_half` clears denominators: from a witness `(m : Rat) = 1/2`,
  multiplying by `2` gives `(m*2 : Nat) : Rat = 1`, then `Rat.natCast_inj` gives
  `m*2 = 1`, which `mul_two_ne_one` refutes by parity;
- the mismatch theorems rewrite to `(1 : Rat) ≠ (6 : Rat)` etc. and use
  `Rat.natCast_inj` against `Nat` disequalities.

Core Lean suffices: no `norm_num`, `linarith`, `omega`, `positivity`, `Finset`,
`Nat.Prime`, `Nat.factorization`, or any Mathlib import is used.

## Note on `Nat.factorial`

The pinned toolchain (`leanprover/lean4:v4.33.1`) does **not** provide
`Nat.factorial` from `import Std` (it is only available with Mathlib, which is not
a dependency of this project). `Main.lean` therefore defines `Nat.factorial` by
structural recursion inside the `Nat` namespace:

```lean
namespace Nat
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n
end Nat
```

This keeps the definitional content — and the text of `spaceTreeFormula` — exactly
as specified, while remaining core Lean only.

## Scope note

The paper's Failure 3 (the Speyer–Sturmfels count `(2n-5)!!` of maximal cones of
`Trop(Gr(2,n))`) is **not** formalised: it is cited as context, whereas the
refutation is already complete from Failures 1 and 2, which are pure arithmetic.
The `n = 3` caveat of the paper is visible here too: `formula_at_3` and
`no_count_is_half` concern `n = 3`, and the three Johnson-mismatch theorems concern
`n = 4, 5, 6`, so the formalised refutation does not rely on `n = 3` alone —
excluding `n = 3` still leaves `F(4) ≠ C(4,2)`, `F(5) ≠ C(5,2)`,
`F(6) ≠ C(6,2)`. The all-`n` statement `F(n) > C(n,2)` for `n ≥ 6` is proved in
`main.tex` by an elementary induction but is not formalised here.
