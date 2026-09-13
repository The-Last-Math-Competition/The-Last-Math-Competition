# Lean 4 formalisation (conjecture 00000000458)

Toolchain: `leanprover/lean4:v4.33.1`; library `tlmc458` (entry point `Main`).

Core Lean 4 only: `import Std`, no Mathlib, no `sorry`, no `axiom`, and no
`native_decide` / `ofReduceBool`.

## Build

```
export PATH="/opt/homebrew/bin:$PATH"
cd lean4
lake build
```

The axiom audit is `Check.lean` (build it with `lake build Check`, or compile
directly with `lean Check.lean` after `lake build`); every `#print axioms`
line should report no axioms beyond `propext`.

## What is formalised

* `modulus_nonneg`, `no_abs_eq_neg_one`: an integer absolute value (`iabs`,
  defined in-file because core Lean has no `|·|` on `Int`) is nonnegative, so
  it can never equal `-1`.
* `formula_at_three`, `formula_at_three_literal`, `contradiction_sign`,
  `contradiction_sign_strong`: the claimed value `(3-2)(-1)^3 = -1` is
  negative, contradicting its being an absolute value.  This is the decisive,
  enumeration-free refutation.
* `Tree`, `rotations`, `closure`, `muRel`, `mobiusTamari`: a full, computable
  model of the Tamari lattice `T_n` (binary trees with `n` internal nodes,
  right-rotation order) and the Möbius recurrence
  `μ(x,x)=1`, `μ(x,z)=-Σ_{x≤y<z} μ(x,y)`.
* `card_T3`, `bottom_is_min`, `top_is_max`: `T_3` has the five Catalan(3)
  shapes, with the left comb as minimum and the right comb as maximum.
* `mu_T3`, `abs_mu_T3`: `μ(T_3) = 1`, so `|μ(T_3)| = 1 ≠ -1`.
* `conjecture_00000000458_false`: the collected refutation (sign
  contradiction plus `|μ(T_3)| = 1 ≠ (3-2)(-1)^3`).

The general statement `|μ(T_n)| = 1` for all `n` is verified up to `n = 8` by
`../reproduce.py`.
