# Lean 4 formalisation — disproof of conjecture `00000000437`

Core Lean only (`import Std`), no Mathlib, no `Finset`, no `Nat.Prime`
(Mathlib-only), no `sorry`. The project pins `lean-toolchain` to
`leanprover/lean4:v4.33.1` and defines the package `tlmc437` with the library
`Main` in `lakefile.toml`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of `Lean.ofReduceBool` (the marker left behind by
`native_decide`). No `native_decide` is used anywhere: every finite closed fact
is discharged by `decide`.

## What is formalised

Witt's formula is encoded exactly as in the conjecture,

```lean
def muF : Nat → Nat → Int            -- fuel-based Möbius function
def mu (n : Nat) : Int := muF n n
def divisors (n : Nat) : List Nat :=
  (List.range (n + 1)).filter (fun d => decide (d ∣ n))
def wittNum (n : Nat) : Int :=
  (divisors n).foldl (fun acc d => acc + mu d * (2 : Int) ^ (n / d)) 0
def witt (n : Nat) : Int := wittNum n / (n : Int)
def isPow2 (n : Nat) : Bool :=
  (List.range (n + 1)).any (fun k => 2 ^ k == n)
```

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `minFac_20` | `minFac 20 = 2` | ascending search returns the smallest prime factor |
| `minFac_24` | `minFac 24 = 2` | guards the composite-divisor pitfall (see below) |
| `mu_12` | `mu 12 = 0` | `12` is not squarefree |
| `mu_30` | `mu 30 = -1` | `30 = 2·3·5` is squarefree with three primes |
| `witt_1` | `witt 1 = 2` | first value |
| `witt_2` | `witt 2 = 1` | second value (odd) |
| `witt_6` | `witt 6 = 9` | iff-violation value (odd) |
| `witt_8` | `witt 8 = 30` | fallback value (even) |
| `witt_24` | `witt 24 = 698870` | catches the corrupted-`minFac` value `698869` |
| `witt_1_even` | `witt 1 % 2 = 0` | parity fact |
| `witt_2_odd` | `witt 2 % 2 = 1` | parity fact |
| `witt_6_odd` | `witt 6 % 2 = 1` | parity fact |
| `witt_8_even` | `witt 8 % 2 = 0` | parity fact |
| `isPow2_1` | `isPow2 1 = true` | `1 = 2^0` is a power of two |
| `isPow2_2` | `isPow2 2 = true` | `2 = 2^1` is a power of two |
| `isPow2_6` | `isPow2 6 = false` | `6` is not a power of two |
| `isPow2_8` | `isPow2 8 = true` | `8 = 2^3` is a power of two |
| `witness_1_2_parity` | `witt 1 % 2 ≠ witt 2 % 2` | **sharpest witness** |
| `fallback_2_8_parity` | `witt 2 % 2 ≠ witt 8 % 2` | **fallback witness** |
| `iff_reading_fails` | `isPow2 6 = false ∧ witt 6 % 2 = 1` | **iff-violation** |
| `parity_not_determined_by_pow2` | `¬ (∀ n m, isPow2 n = isPow2 m → witt n % 2 = witt m % 2)` | negates the functional reading |
| `conjecture_00000000437_false` | conjunction of the witnesses | collected refutation |

## Proof strategy

- **Möbius by factorisation.** `minFacAux` searches candidate divisors in
  **ascending** order (`p = 2, 3, 4, …`) and returns the first `p ≥ 2` with
  `p ∣ N` and `p·p ≤ N`; if none exists it returns `N`, so `N` is `1` or prime.
  `muF` then uses the standard recursion: for `n ≥ 2` with smallest prime
  factor `p` and cofactor `m = n/p`, `μ n = 0` if `p ∣ m`, else `μ n = -μ m`.
  Integer arithmetic (`Int`) is used for the signed Möbius sums.
- **Finite facts by `decide`.** `witt 1 = 2`, `witt 2 = 1`, `witt 6 = 9`,
  `witt 8 = 30`, `witt 24 = 698870`, the parities, the power-of-two flags, and
  the collected `conjecture_00000000437_false` are all closed terms and are
  proved by `decide`. `set_option maxRecDepth 1000000` gives `decide` enough
  fuel; `decide` is kernel-checked and does not introduce
  `Lean.ofReduceBool`.
- **Negating the functional reading.** `parity_not_determined_by_pow2` applies
  the putative function to `n = 1`, `m = 2` (both flag `true`, proved by
  `decide`) and contradicts `witness_1_2_parity`.

## The ascending-`minFac` pitfall

The smallest-prime-factor routine **must** return the smallest factor. A naive
"largest divisor `≤ √N`" search returns the composite `4` for `N = 20` and
`N = 24` (since `4·4 ≤ 20` and `4·4 ≤ 24`), which silently corrupts `μ` and
produces the **wrong** value `witt 24 = 698869` instead of the correct
`witt 24 = 698870`. This project therefore uses an ascending search and proves
`minFac 20 = 2`, `minFac 24 = 2`, and `witt 24 = 698870` as guards. (The
verifier that preceded this submission found exactly this failure mode.)

## Scope note

- The refutation target is the **parity clause**. The value `witt n` is defined
  by Witt's formula exactly as stated; nothing here formalises the shuffle
  algebra or its Lie-primitive space, because the conjecture's numerical clause
  is accepted as true and only its parity clause is refuted.
- The formalised witnesses are finite and unconditional: `witt 1 = 2`,
  `witt 2 = 1`, `witt 6 = 9`, `witt 8 = 30`, and `witt 24 = 698870` are
  kernel-checked closed computations. They pin the parities of `L_1`, `L_2`,
  `L_6`, `L_8` and hence refute the functional reading, the restricted
  convention, and the iff reading.
- The **repaired** characterisation (`L_n` odd iff `v_2(n) ∈ {1,2}` and the odd
  part is squarefree) is stated and proved on paper in `main.tex` and checked
  numerically for `n ≤ 60` in `reproduce.py`; it is not formalised in Lean (it
  needs a `v_2`/squarefreeness development and is not required for the
  refutation).

## Environment

Lean 4.33.1, Lake, no Mathlib. `lake build` needs no cache download. The axiom
audit reports no `sorryAx` and no `Lean.ofReduceBool`: the `minFac`, `mu`, and
`isPow2` facts depend on no axioms at all, while the `witt`/parity facts use
only `propext`.
