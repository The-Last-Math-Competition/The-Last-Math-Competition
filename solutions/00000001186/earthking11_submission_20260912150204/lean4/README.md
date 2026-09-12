# Lean 4 formalisation — disproof of conjecture `00000001186`

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

`ω(n)` is defined as `distinctPrimeCount n`, a computable function counting the
distinct prime divisors of `n` by a bounded loop over `List.range (n + 1)`, using a
computable primality test `primeB` (bounded trial division over `List.range n`). No
Mathlib definitions (`Nat.factorization`, `Finset`, `Nat.Prime`) are used.

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `factor_60` | `60 = 2^2 * 3 * 5` | factorisation |
| `factor_504` | `504 = 2^3 * 3^2 * 7` | factorisation |
| `factor_660` | `660 = 2^2 * 3 * 5 * 11` | factorisation |
| `distinctPrimeCount_60` | `ω(60) = 3` | base value |
| `distinctPrimeCount_504` | `ω(504) = 3` | Contradiction 1 |
| `distinctPrimeCount_660` | `ω(660) = 4` | Contradiction 2 |
| `distinctPrimeCount_504_ne_four` | `ω(504) ≠ 4` | no group of order 504 has 4 distinct primes, so `m(4) ≠ 504` |
| `distinctPrimeCount_660_ne_five` | `ω(660) ≠ 5` | no group of order 660 has 5 distinct primes, so `m(5) ≠ 660` |
| `no_order_504_has_four_distinct_primes` | `order = 504 → ω(order) ≠ 4` | Contradiction 1, order-parameterised |
| `no_order_660_has_five_distinct_primes` | `order = 660 → ω(order) ≠ 5` | Contradiction 2, order-parameterised |
| `four_times_sixty_lt_504` | `(4 : Nat) * 60 < 504` | Contradiction 3: Nat encoding of `504 / 60 > 4` |
| `Omega_60` / `Omega_504` / `Omega_660` | exponent sums `4`, `6`, `5` | multiplicity-reading discussion |
| `conjecture_00000001186_false` | conjunction of the three contradictions | the disproof |

## Proof strategy

Everything is decidable arithmetic on closed numerals, so each theorem is proved by
`decide` (or by rewriting an assumed order and reusing the closed result). This keeps
the development entirely within core Lean:

- `ω(504) = 3` and `ω(660) = 4` are the exact values of a computable function, so
  `decide` closes both the equalities and the disequalities `≠ 4`, `≠ 5`;
- `504 = 2^3·3^2·7` and `660 = 2^2·3·5·11` are closed `Nat` equalities closed by
  `decide`, giving the three-distinct-prime and four-distinct-prime facts directly;
- the ratio contradiction `504 / 60 > 4` is encoded as the `Nat` inequality
  `4 * 60 < 504` (equivalent since `60 > 0`) and closed by `decide`; the direct
  `Rat` form is avoided because core `Rat.blt` is `@[irreducible]` and cannot be
  reduced by `decide` in this toolchain;
- `conjecture_00000001186_false` is the conjunction of the three.

Core Lean suffices: no `norm_num`, `linarith`, `omega`, `positivity`, `Finset`,
`Nat.Prime`, `Nat.factorization`, or any Mathlib import is needed.

## Note on the group-theoretic phrasing

The conjectured definition refers to nonabelian simple *groups*, but the refutation is
purely arithmetic: a group of order 504 has exactly the distinct prime divisors of
504, namely `2, 3, 7`. A statement quantifying over actual groups would need
`Fintype`/`Nat.card` from Mathlib; here the same content is captured by the
order-parameterised theorems `no_order_504_has_four_distinct_primes` and
`no_order_660_has_five_distinct_primes`, which say that *any* order equal to 504 (resp.
660) has `ω` different from 4 (resp. 5). The classification of finite simple groups is
not used.
