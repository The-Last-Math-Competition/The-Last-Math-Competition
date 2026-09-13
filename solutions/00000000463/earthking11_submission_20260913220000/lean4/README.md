# Lean 4 formalisation — disproof of conjecture `00000000463`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main` in
`lakefile.toml`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of Mathlib dependencies.

## What is formalised

The conjecture's count runs over `n` with `n^(n−2)` squarefree. The key point is
that no `n ≥ 4` qualifies. `Nat.Prime` and `Nat.minFac` are **not** available in
`import Std`, so primality is defined here as a `Prop` and, separately, as a
bounded trial-division test.

```lean
/-- Bounded trial-division primality test. -/
def primeB (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range n).all fun d => decide (d < 2 ∨ n % d ≠ 0)

/-- Primality as a Prop: p ≥ 2 and the only divisors of p are 1 and p. -/
def Prime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- Squarefree: no prime square divides n. -/
def Squarefree (n : Nat) : Prop := ∀ p : Nat, Prime p → ¬ (p * p ∣ n)
```

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `primeB_two`, `primeB_three`, `primeB_four`, `primeB_five` | `primeB 2 = true`, etc. | the bounded test on concrete values |
| `exists_prime_dvd` | `∀ n ≥ 2, ∃ p, Prime p ∧ p ∣ n` | every `n ≥ 2` has a prime divisor (strong induction) |
| `sq_dvd_pow_of_dvd` | `p ∣ n → 2 ≤ n−2 → p*p ∣ n^(n−2)` | the divisibility step |
| `not_squarefree_pow` | `∀ n ≥ 4, ¬ Squarefree (n^(n−2))` | **main theorem** |
| `squarefree_one` | `Squarefree 1` | `1` is squarefree |
| `squarefree_three` | `Squarefree 3` | `3` is squarefree |
| `squarefree_two_pow` | `Squarefree (2^(2−2))` | `n = 2`: `2^0 = 1` |
| `squarefree_three_pow` | `Squarefree (3^(3−2))` | `n = 3`: `3^1 = 3` |
| `squarefree_of_le_three` | `n ≤ 3 → Squarefree (n^(n−2))` | all small cases |
| `sqfree_pow_le_three` | `Squarefree (n^(n−2)) → n ≤ 3` | converse |
| `sqfree_pow_iff_le_three` | `∀ n ≥ 1, Squarefree (n^(n−2)) ↔ n ≤ 3` | **characterisation** |
| `sqfreeCount` | recursive count of indices `n ≤ N` with `n ≤ 3` | the count, by the characterisation |
| `sqfreeCount_eq_min` | `sqfreeCount N = min N 3` | closed form |
| `sqfreeCount_le_three` | `∀ N, sqfreeCount N ≤ 3` | **the count is bounded** |
| `sqfreeCount_10 … _1000000` | `sqfreeCount (10^k) = 3` | the table of the write-up |
| `conjecture_00000000463_false` | `∀ N, sqfreeCount N ≤ 3` | the conjecture's left side cannot be asymptotic to `c·N/√log N` |

## Proof strategy

- **Prime divisor existence** (`exists_prime_dvd`). Strong induction on `n`. If
  `n` is prime, `p = n`; otherwise `¬ Prime n` together with `2 ≤ n` yields (via
  `Classical.not_forall` and `Classical.not_imp`) a divisor `d` with
  `d ≠ 1`, `d ≠ n`. Then `2 ≤ d < n` and the induction hypothesis gives a prime
  divisor of `d`, which divides `n` by `Nat.dvd_trans`.
- **Divisibility step** (`sq_dvd_pow_of_dvd`). `p ∣ n` gives
  `p*p ∣ n*n = n^2` (`Nat.mul_dvd_mul`, `Nat.pow_two`) and `n^2 ∣ n^(n−2)`
  (`Nat.pow_dvd_pow`, using `2 ≤ n−2`), so `p*p ∣ n^(n−2)` by `Nat.dvd_trans`.
- **Main theorem** (`not_squarefree_pow`). A prime divisor `p` of `n ≥ 4`
  satisfies `p*p ∣ n^(n−2)`, contradicting `Squarefree (n^(n−2))`.
- **Small cases.** `squarefree_one` and `squarefree_three` unfold
  `Squarefree`, bound `p ≤ p*p ≤ 1` (resp. `≤ 3`) via `Nat.le_of_dvd`, and
  contradict `2 ≤ p` by `Nat.mul_le_mul` and `omega`. The `n = 2` and `n = 3`
  statements reduce to these by definitional reduction.
- **Characterisation and count.** `sqfree_pow_le_three` uses
  `Classical.byContradiction` and `not_squarefree_pow`; the converse is the case
  analysis `n = 0,1,2,3`. `sqfreeCount` is defined by recursion and its closed
  form `min N 3` is proved by induction, giving the bound `≤ 3`.

## Axiom audit

`lake env lean Check.lean` reports:

- concrete computations (`primeB_*`, `sqfreeCount_10 … _1000000`): **no axioms**;
- `sq_dvd_pow_of_dvd`: `propext`;
- `squarefree_one`, `squarefree_three`, `squarefree_two_pow`,
  `squarefree_three_pow`, `squarefree_of_le_three`, `sqfreeCount_eq_min`,
  `sqfreeCount_le_three`, `conjecture_00000000463_false`: `propext`,
  `Quot.sound`;
- `exists_prime_dvd`, `not_squarefree_pow`, `sqfree_pow_le_three`,
  `sqfree_pow_iff_le_three`: `propext`, `Classical.choice`, `Quot.sound`.

No `sorryAx` appears for any theorem.

## Scope note

- The general statement is fully formalised and symbolic, not merely checked on a
  finite range: `not_squarefree_pow` holds for **every** `n ≥ 4`, and
  `sqfreeCount_le_three` holds for **every** `N`.
- `Prime` is the elementary `Prop`-level definition above (`Nat.Prime` is absent
  from `import Std`). `primeB` is the bounded trial-division Boolean test; it is
  used to verify concrete small primes. The general proofs use `Prime`; the
  equivalence of `primeB` with `Prime` on the tiny range used is not formalised
  (it is not needed, since the general theorem is symbolic).
- The count is formalised through the proved characterisation
  `Squarefree (n^(n−2)) ↔ n ≤ 3` for `n ≥ 1`, whence `sqfreeCount` counts exactly
  the squarefree indices. The convention at `n = 1` is `1^(1−2) = 1^0 = 1` in
  `Nat` (truncated subtraction), which is squarefree; excluding `n = 1` just
  lowers the count from 3 to 2 and changes nothing about boundedness.
- `c·N/√(log N) → ∞` for `c > 0` (and `log` is real) is not formalised in Lean;
  it is standard real analysis and is stated in prose in `main.tex`. The Lean
  content is precisely the boundedness of the counting function, which is the
  substantive combinatorial fact.

## Environment

Lean 4.33.1, Lake, no Mathlib. `lake build` needs no cache download.
