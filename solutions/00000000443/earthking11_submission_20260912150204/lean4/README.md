# Lean 4 formalisation — disproof of conjecture `00000000443`

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

The exact dimension is `wittDim n`, a computable `Int`-valued implementation of
Witt's formula

$$\dim L_n = \frac1n \sum_{d \mid n} \mu(d)\, 2^{\,n/d}.$$

The ingredients are all hand-written and computable, with no Mathlib definitions
(no `Finset`, `Nat.Prime`, `Nat.factorization`):

- `primeB n` — primality by bounded trial division over `List.range n`;
- `distinctPrimeCount n` — `ω(n)`, the number of distinct prime divisors;
- `squarefreeB n` — square-freeness, checking `d * d ∤ n` for `d ≥ 2`;
- `mobius n` — the Möbius function `μ : Nat → Int` (`0` if not square-free, else
  `(-1)^ω(n)`);
- `divisors n` — the positive divisors of `n`, a bounded loop over `List.range`;
- `wittSum n` / `wittDim n` — the divisor sum and its exact integer quotient by `n`;
- `claimedBound n = 2^(n-1) - 2^((n+1)/2)` and
  `claimedGap n = 2^((n-1)/2) / 2`, with
  `actualGap n = |claimedBound n - wittDim n|`.

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `mobius_one` / `mobius_two` / `mobius_four` | `μ(1)=1`, `μ(2)=-1`, `μ(4)=0` | Möbius values |
| `wittDim_one` … `wittDim_twelve` | `dim L_n = 2,1,2,3,6,9,18,30,56,99,186,335` | exact dimensions |
| `wittDim_four` | `wittDim 4 = 3` | Failure (A) input |
| `bound_four` | `(2^3 : Int) - 2^2 = 4` | Failure (A) input |
| `claimedBound_four` | `claimedBound 4 = 4` | Failure (A) input |
| `inequality_fails_at_four` | `wittDim 4 < (2^3 : Int) - 2^2` | Failure (A) at `n = 4` |
| `inequality_fails_4_to_12` | `wittDim n < claimedBound n` for `n = 4,…,12` | Failure (A) on the range |
| `gap_fails_at_three` | `wittDim 3 = 2 ∧ 2^2 - 2^2 = 0 ∧ 2 ≠ 2^((3-1)/2)/2` | Failure (B) at `n = 3` |
| `actualGap_three_ne` | `actualGap 3 ≠ claimedGap 3` | Failure (B), functional form |
| `gap_fails_at_seven` | `actualGap 7 ≠ claimedGap 7` | Failure (B) at `n = 7` |
| `gap_fails_at_eleven` | `actualGap 11 ≠ claimedGap 11` | Failure (B) at `n = 11` |
| `gap_holds_at_five` | `actualGap 5 = claimedGap 5` | records the coincidence at `n = 5` |
| `conjecture_00000000443_false` | conjunction of (A) and (B) | the disproof |

## Proof strategy

Every numerical fact is a closed computation on numerals, so each theorem is
discharged by `decide` against the computable definitions above (the
`[4, 12]` range is stated as a finite conjunction of decidable strict
inequalities). No induction or case analysis is needed, and no Mathlib tactic
(`norm_num`, `linarith`, `omega`) is used. The only tactics appearing are `decide`
and, implicitly, the kernel's reduction of `List.range` / `List.filter` /
`List.foldl` over concrete lists.

Consequences:

- `wittDim 4 = 3` and `claimedBound 4 = 4`, hence
  `wittDim 4 < claimedBound 4`: the universal inequality (I) fails at `n = 4`;
- `actualGap p ≠ claimedGap p` at `p = 3, 7, 11`: the prime-gap identity (II) fails
  there (`actualGap 5 = claimedGap 5` is retained only to show the `n = 5`
  coincidence, and `n = 2` is excluded because `(n-1)/2` is not integral);
- `conjecture_00000000443_false` is the conjunction, so either failure alone
  refutes the conjecture.

## Scope note

The Lean development formalises the arithmetic core: the exact Witt dimensions, the
claimed bound, the two independent failures, and the final combined theorem. The
conjecture is a conjunction of a universal inequality and a prime-gap identity; the
formalisation refutes it by closed counterexamples at `n = 4` (inequality) and
`n = 3, 7, 11` (gap). No structure theory of free Lie algebras is formalised, and
none is needed: the disproof is entirely numerical and is captured by `decide` on
computable definitions in core Lean.
