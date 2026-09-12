# Lean 4 formalisation — disproof of conjecture `00000001097`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main` in
`lakefile.toml`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm the
absence of `sorryAx` and of Mathlib dependencies.

## What is formalised

The refutation is reduced to the explicit finite instance `q = 5`, `d = 2`, where
`gcd(d - 1, q - 1) = gcd(1, 4) = 1`. The root count is a computable function that
enumerates the triples `(a, b, x)` with `a, b, x < q` (that is, `Fin q`) using a
hand-written nested `List.foldl`/`List.map`; core Lean has no `List.product`, and
`List.range q` enumerates `Fin q`. The exact mean is therefore obtained by
enumeration rather than by Mathlib's `Finset` or `ZMod`.

Closed rational values are built with the primitive `mkRat`, which reduces under
`decide`; core `Rat.add`/`Rat.sub`/`Rat.mul`/`Rat.inv` are `@[irreducible]` and do
not. Comparisons of `mkRat` numerals are decided directly, and the one rational
identity needing subtraction is proven through `Rat.ext` with `Rat.sub_def`.

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `rootTripleCount_5_2` | `rootTripleCount 5 2 = 25` | explicit enumeration over `Fin 5` |
| `mean_5_2` | `rootTripleCount 5 2 = 5 * 5` | `#triples = #pairs`, i.e. the mean is `1` |
| `meanRootCount_5_2` | `meanRootCount 5 2 = 1` | the exact mean at `q = 5`, `d = 2` is `1` |
| `gcdB_1_4` | `gcdB 1 4 = 1` | `gcd(1, 4) = 1` on the bounded gcd |
| `claimedExponent_5_2` | `claimedExponent 5 2 = 1` | the conjectured exponent is `1` |
| `claimed_main_term_at_5_2` | `(1 : Rat) + mkRat 4 5 = mkRat 9 5` | claimed value is `9/5` (`mkRat 4 5` encodes `4/5`) |
| `claimedMainTerm_5_2` | `claimedMainTerm 5 2 = mkRat 9 5` | same, through the definition |
| `contradiction` | `¬ ((1 : Rat) = claimedMainTerm 5 2)` | `9/5 ≠ 1` |
| `second_moment_5` | `secondMoment 5 = mkRat 9 5` | exact second moment at `q = 5` |
| `variance_5` | `secondMoment 5 - 1 = varianceValue 5` | variance `9/5 - 1 = 4/5`, not `9/5` |
| `conjecture_00000001097_false` | conjunction of the exact value and the false claim | the disproof |

## Proof strategy

The arithmetic facts are decidable on closed `Nat`/`Int`/`mkRat` numerals, so each
theorem is closed by `decide` (with `Rat.ext` + `Rat.sub_def` for the single
rational subtraction in `variance_5`). This keeps the development entirely within
core Lean and avoids Mathlib-only tactics.

- **Exact mean.** `rootTripleCount q d` filters the hand-enumerated list of all
  triples `(a, b, x) ∈ Fin q × Fin q × Fin q` for the vanishing of
  `x^d + a*x + b` modulo `q`. For `q = 5`, `d = 2` there are `25` such triples out of
  `5 * 5 = 25` pairs `(a, b)`, so the mean `25 / 25` is `1`; `decide` evaluates the
  enumeration.
- **Claimed main term.** `gcdB` is a bounded, closed computable gcd. At `q = 5`,
  `d = 2` it gives `gcdB 1 4 = 1`, so the conjectured value is
  `1 + (5 - 1) / 5^1 = 9/5`, encoded as the `mkRat` fraction `9/5`.
- **Contradiction.** `9/5 ≠ 1`, formalised as
  `¬ ((1 : Rat) = claimedMainTerm 5 2)`.
- **Variance.** The exact second moment at `q = 5` is `2 - 1/5 = 9/5`; subtracting
  the square of the mean `1` gives `4/5`, so the claimed `9/5` is the second
  moment, not the variance.

## Scope note

The formalisation is deliberately finite and instance-based. It proves the
conjecture false at the single pair `(q, d) = (5, 2)`, which is enough to disprove a
universally quantified statement. It does not formalise the general bijection
argument `M(q, d) = 1` for arbitrary prime powers, nor the general second moment
`2 - 1/q`; those are proved in `main.tex` and checked numerically in `reproduce.py`.
Reducing the general field-theoretic statements to core Lean would require a
formalisation of finite fields, which is beyond the core-only constraint observed
here. No Mathlib type (`Finset`, `ZMod`), no Mathlib tactic (`norm_num`, `linarith`,
`omega`), and no `sorry` is used.
