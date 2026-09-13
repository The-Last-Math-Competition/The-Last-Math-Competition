# Lean formalisation (`tlmc1299`)

Core Lean 4 only (`import Std`), **no Mathlib**, no `sorry`, no `axiom`, no
`native_decide` / `Lean.ofReduceBool`. Toolchain:
`leanprover/lean4:v4.33.1` (see `lean-toolchain`).

## Build

```sh
lake build                 # builds library Main (default target)
lake env lean Check.lean   # prints #print axioms for every theorem
```

## Files

* `Main.lean` — the Ducci map, the seed, the iterate, and all theorems.
* `Check.lean` — `import Main` plus one `#print axioms` per theorem.

## Model

The Ducci map on `n`-tuples is `T(x)_i = |x_i - x_{i+1}|` with cyclic indexing.
For `n = 5` we work with `Fin 5 → Nat`:

* `T x i = (x i - x (i+1)) + (x (i+1) - x i)`, using truncated subtraction.
  For naturals `(a - b) + (b - a) = |a - b|`, since one of the two subtractions
  vanishes; cyclic indexing is `Fin 5` addition (`i + 1`).
* `s = (0,0,0,1,1)`, written by matching on `i.val`.
* `iter 0 = s` and `iter (k+1) = T (iter k)`.

### Decidability

Core Lean (`import Std`) provides **no** `DecidableEq` instance for function
types, so `by decide` cannot discharge a goal of the form `iter k = s` directly.
We therefore phrase all finite checks pointwise over `Fin 5`, where
`∀ i : Fin 5, P i` and `∃ i : Fin 5, P i` are decidable (finite domain), and
recover the function-level statement with `funext`:

* `returns_at_15 : iter 15 = s` is proved by `funext i; revert i; decide`,
  i.e. the pointwise statement `∀ i : Fin 5, iter 15 i = s i` is decided.

## Theorems

| Theorem | Statement |
| --- | --- |
| `returns_at_15` | `iter 15 = s` (the seed lies on a cycle of length dividing 15) |
| `no_return_below_15` | `∀ k : Fin 15, k.val ≠ 0 → ¬ (∀ i, iter k.val i = s i)` |
| `distinct_first_15` | `∀ k, 1 ≤ k → k < 15 → iter k ≠ s` |
| `fifteen_not_divides_five` | `¬ (15 ∣ 5)` |
| `min_period_five` | `(∃ k, 1 ≤ k ∧ iter k = s) ∧ ¬ (∃ k, 1 ≤ k ∧ k < 15 ∧ iter k = s)` |
| `conjecture_00000001299_false` | `iter 15 = s ∧ (∃ k, 1 ≤ k ∧ iter k = s) ∧ ¬ (∃ k, 1 ≤ k ∧ k < 15 ∧ iter k = s) ∧ ¬ (15 ∣ 5)` |

## Axiom audit

Running `lake env lean Check.lean` prints

```
'Tlmc1299.returns_at_15' depends on axioms: [propext, Quot.sound]
'Tlmc1299.no_return_below_15' depends on axioms: [propext]
'Tlmc1299.distinct_first_15' depends on axioms: [propext]
'Tlmc1299.fifteen_not_divides_five' depends on axioms: [propext]
'Tlmc1299.min_period_five' depends on axioms: [propext, Quot.sound]
'Tlmc1299.conjecture_00000001299_false' depends on axioms: [propext, Quot.sound]
```

The only axioms are `propext` and `Quot.sound` (the latter entering through
`funext`); there is no `sorryAx` and no `Lean.ofReduceBool`.
