# Lean formalisation (conjecture 00000000750)

Core Lean 4, toolchain `leanprover/lean4:v4.33.1`, `import Std` only. No
Mathlib, no `sorry`, no `axiom`, no `native_decide`.

## What is formalised

`Main.lean` (namespace `Tlmc750`) formalises the finite-difference /
Mahler-coefficient core of the refutation for the counterexample
`f(x) = x + 1`:

- `diff`, `diffN` — the forward difference operator and its iterates.
- `mahlerCoeff f n = diffN n f 0` — the `n`-th Mahler coefficient
  `a_n = Δⁿ f (0)`.
- `diff_id_add_one` — `Δ (x+1) = 1` (constant function).
- `diffN_id_add_one_two_add` — `Δ^{m+2} (x+1) = 0` for every `m`.
- `diff_id_add_one_vanishes` — `∀ n ≥ 2, diffN n (x+1) 0 = 0`.
- `mahler_coeffs` — the coefficient sequence of `x+1` is `(1, 1, 0, 0, …)`.
- `claimed_ne_one_2_2`, `claimed_ne_one_2_3`, `claimed_ne_one_3_1`,
  `claimed_ne_one_3_2`, `claimed_ne_one_5_1`, `claimed_ne_one_5_2` —
  `p^{k-1}(p-1) ≠ 1` for `(p,k) = (2,2), (2,3), (3,1), (3,2), (5,1), (5,2)`,
  each by `decide`.
- `conjecture_00000000750_false` — collects all of the above.

Together these say: the Mahler coefficient sequence of `x + 1` is eventually
constant `0`, so its minimal eventual period is `1`, while the conjectured
exact period `p^{k-1}(p-1)` is `≠ 1` for the listed pairs. Hence the conjecture
is refuted.

## Scope and honesty

The Lean file formalises only the arithmetic core: finite differences, the
coefficient sequence, and the period mismatch over `Nat`. It does **not**
formalise

- the `p`-adic space `Z_p`, its topology, or Haar measure;
- the isometry / `1`-Lipschitz property and minimality of `x + 1`;
- the Mahler expansion as an infinite series in `Z_p` (only the coefficients).

Those aspects are argued in `../main.tex` and checked numerically in
`../reproduce.py`. In particular minimality of `x+1` (the orbit of `0` is
`Z`) and the measure-preserving property are stated and proved in the paper,
not here. The formal theorem `conjecture_00000000750_false` should therefore be
read as the finite-difference core of the refutation, not as a fully
p-adic-formal refutation.

The `#print axioms` output in `Check.lean` shows only the standard Lean axioms
`propext` and `Quot.sound` (from `funext`/`omega`); there is no `sorryAx` and
no `ofReduceBool`.

## Build

```
cd lean4
lake build                 # builds Main
lake env lean Check.lean   # prints axioms per theorem
```
