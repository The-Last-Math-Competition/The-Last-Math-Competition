# Lean 4 formalisation — disproof of conjecture `00000000226`

Core Lean only (`import Std`), no Mathlib, no `sorry`, no `axiom`, no
`native_decide`. The project pins `lean-toolchain` to
`leanprover/lean4:v4.33.1` and defines the library `Main` in `lakefile.toml`.

## Build and audit

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build
lake env lean Check.lean
```

`lake build` exits 0. `Check.lean` prints `#print axioms` for every theorem so
a reviewer can confirm the absence of `sorryAx` and of `Lean.ofReduceBool`, and
the absence of any Mathlib dependency.

## What is formalised

The conjecture claims that the proportion of Cullen numbers `C_n = n*2^n + 1`
with least prime factor 3 is an explicit rational, and that the Cullen and
Woodall proportions (`W_n = n*2^n - 1`) sum to 1. The formalisation proves the
residue facts that refute this and the resulting non-sum:

- both sequences are odd for `n ≥ 1`, so "least prime factor 3" is the same as
  "divisible by 3";
- `2^n mod 3` and `(n*2^n) mod 3` are periodic in `n` with period 6;
- `3 | C_n ↔ n mod 6 ∈ {1,2}` and `3 | W_n ↔ n mod 6 ∈ {4,5}`;
- the two proportions are `2/6 = 1/3` each, summing to `2/3 ≠ 1`.

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `two_pow_mod_three_period6` | `2^n % 3 = 2^(n % 6) % 3` | exponent periodic with period 6 |
| `mul_two_pow_mod6` | `(n*2^n) % 3 = ((n%6)*2^(n%6)) % 3` | core periodicity |
| `cullen_period6` | `(n*2^n+1) % 3 = ((n%6)*2^(n%6)+1) % 3` | Cullen periodicity |
| `woodall_period6` | `(n*2^n+2) % 3 = ((n%6)*2^(n%6)+2) % 3` | Woodall periodicity (`+2` = `−1 mod 3`) |
| `cullen_div3_iff` | `(n*2^n+1) % 3 = 0 ↔ n%6 = 1 ∨ n%6 = 2` | Cullen equivalence |
| `woodall_div3_iff` | `(n*2^n+2) % 3 = 0 ↔ n%6 = 4 ∨ n%6 = 5` | Woodall equivalence (`+2` form) |
| `W_mod3_eq_add_two` | `1 ≤ n → W_n % 3 = (n*2^n+2) % 3` | convert `−1` to `+2` for `n ≥ 1` |
| `woodall_W_div3_iff` | `1 ≤ n → W_n % 3 = 0 ↔ n%6 = 4 ∨ n%6 = 5` | Woodall equivalence, true `W_n` |
| `cullen_odd` | `0 < n → C_n % 2 = 1` | `C_n` odd |
| `woodall_odd` | `1 ≤ n → W_n % 2 = 1` | `W_n` odd |
| `residue_table` | table for `n = 6..11` | the residue table |
| `proportions_sum` | `2 + 2 = 4 ∧ 4 ≠ 6` | `1/3 + 1/3 = 2/3 ≠ 1` over denominator 6 |
| `two_thirds_ne_one` | `2 * 1 ≠ 1 * 3` | cross-multiplied `2/3 ≠ 1` |
| `four_ne_six` | `4 ≠ 6` | `4/6 ≠ 6/6` |
| `conjecture_00000000226_false` | conjunction of the two equivalences and the non-sum | the collected disproof |

## Proof strategy

- `two_pow_mod_three_period6` writes `n = 6*(n/6) + n%6` with
  `Nat.div_add_mod`, expands `2^(a+b) = 2^a * 2^b` and `2^(6*(n/6)) =
  (2^6)^(n/6)`, uses `(2^6) % 3 = 64 % 3 = 1`, and cancels the resulting
  factor `1` (`Nat.pow_mod`, `Nat.mul_mod`, `Nat.mod_eq_of_lt`).
- `mul_two_pow_mod6` combines `Nat.mul_mod` with the reduction `n % 3 =
  (n % 6) % 3` (`Nat.mod_mod_of_dvd`, since `3 ∣ 6`) and the period-6 lemma.
- The two equivalences reduce `n` modulo 6 and finish on the six concrete
  residues by `decide`; the disjunction `n%6 ∈ {0,…,5}` is supplied by `omega`.
- `W_mod3_eq_add_two` uses `n*2^n ≥ 1` for `n ≥ 1` and `Nat.add_mod_right`:
  `n*2^n − 1 + 3 = n*2^n + 2`.
- `cullen_odd`/`woodall_odd` use `2^n % 2 = 0` for `n > 0`
  (`Nat.two_pow_mod_two_eq_zero`).
- `proportions_sum` and `four_ne_six` are `Nat` facts over the common
  denominator 6. Core `Rat` multiplication/inversion is irreducible, so
  `decide` cannot reduce `ℚ`; the equality `2/3 ≠ 1` is therefore witnessed by
  comparing the numerators `4` and `6` of `2/3 = 4/6` and `1 = 6/6`.

Core Lean suffices: no `norm_num`, `linarith`, `positivity`, `Finset`,
`ZMod`, `Matrix`, or any Mathlib import is used. The only axioms reported are
`propext` and, for the theorems that use `omega`/`rw`/`decide` on dependent
data, `Quot.sound`.

## Scope note

The formalisation establishes the exact residue facts and the arithmetic
`1/3 + 1/3 = 2/3 ≠ 1`. It does not formalise limits or densities of subsets of
`ℕ` (that would require `Filter`/`Tendsto` infrastructure from Mathlib). The
density conclusion is instead a direct consequence of the proven periodicity:
each set occupies exactly two of the six residue classes modulo 6, so its
density is the rational `2/6 = 1/3`, and the two densities sum to `2/3`. The
numerical script `../reproduce.py` verifies the periodicity exhaustively and
checks the exact rational arithmetic.

## Environment

Lean 4.33.1, Lake, standard library only, no Mathlib. `lake build` needs no
cache download.
