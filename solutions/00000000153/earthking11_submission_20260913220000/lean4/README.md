# Lean 4 formalisation — disproof of conjecture `00000000153`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main` in
`lakefile.toml` (project name `tlmc153`).

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`lake build` succeeds with exit code `0`. `Check.lean` prints `#print axioms`
for every theorem. Expected output: every theorem depends on
`[propext, Quot.sound]` only; none reports `sorryAx`.

## What is formalised

| Object | Definition / statement | Role |
|:-------|:-----------------------|:-----|
| `IsPrime p` | `2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p` | primality; core Lean/`Std` have **no** `Nat.Prime`, so we define it |
| `T x` | `⟨(x.val + 1) % 4, _⟩ : Fin 4` | the shift `T x = x + 1` on `Z/4` |
| `iter n x` | direct recursion: `iter 0 x = x`, `iter (n+1) x = T (iter n x)` | the iteration `T^n x`; `Function.iterate` and `f^[n]` are Mathlib-only, so it is defined by hand |
| `four_not_dvd_of_isPrime` | `IsPrime p → ¬ 4 ∣ p` | **key arithmetic fact**: no prime is divisible by 4 |
| `iter_val` | `(iter n x).val = (x.val + n) % 4` | closed form of the dynamics |
| `FullOrbit x y` | `∃ n, iter n x = y` | full-orbit reachability |
| `minimal x y` | `FullOrbit x y` | every full orbit is all of `X`; `T` is a single 4-cycle |
| `IsMinimal` | `∀ x y, FullOrbit x y` | minimality of `(Fin 4, T)` |
| `isMinimal` | `IsMinimal` | the system is minimal |
| `PrimeOrbitAt x y` | `∃ p, IsPrime p ∧ iter p x = y` | prime-index orbit `{T^p x : p prime}` |
| `PrimeOrbit x y` | `PrimeOrbitAt x y` | the prime-index orbit as a predicate |
| `primeOrbitAt_not_self x` | `¬ PrimeOrbitAt x x` | the prime orbit omits its base point; a prime `p` with `T^p x = x` would give `4 ∣ p` |
| `primeOrbitAt_not_univ x` | `¬ (∀ y, PrimeOrbitAt x y)` | the prime orbit is a proper subset of `X`, for **every** `x` |
| `prime_iter_zero_val_ne_zero` | `IsPrime p → (iter p 0).val ≠ 0` | for `x = 0`: equivalently `p % 4 ≠ 0` for every prime |
| `zero_not_mem_primeOrbit` | `¬ PrimeOrbitAt 0 0` | the prime orbit of `0` omits `0` |
| `PrimeOrbitClosure x` | `Fin 4 → Prop := PrimeOrbitAt x` | **model of the closure** of the prime orbit (discrete topology: closure = set) |
| `primeOrbitClosure_not_univ x` | `¬ (∀ y, PrimeOrbitClosure x y)` | the closure of the prime orbit is not all of `X`, for every `x` |
| `conjecture_00000000153_false` | `IsMinimal ∧ ∀ x, ¬ (∀ y, PrimeOrbitClosure x y)` | the packaged refutation at every `x` |
| `conjecture_00000000153_false_at_zero` | `(∀ y, FullOrbit 0 y) ∧ ¬ (∀ y, PrimeOrbitClosure 0 y)` | the refutation specialised to `x = 0` |

## Proof strategy

1. **Primality.** `IsPrime p := 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p`.
2. **`4 ∤ p` for prime `p`.** From `4 ∣ p` we get `2 ∣ p`; applying the
   divisor condition to `m = 2` gives `2 = 1` (false) or `p = 2`; then `4 ∣ 2`
   is false. This is `four_not_dvd_of_isPrime`.
3. **Closed form.** `iter n x = x + n mod 4` is proved by induction on `n`,
   the successor step being pure modular arithmetic closed by `omega`
   (`iter_val`).
4. **Minimality.** For any `x, y : Fin 4`, the iterate count
   `(y.val + 4 - x.val) % 4` reaches `y`. Finite modular arithmetic, `omega`
   (`minimal`).
5. **The prime orbit omits its base point.** If `iter p x = x` for a prime `p`,
   then `(x.val + p) % 4 = x.val`. Writing `x.val + p = 4·((x.val + p)/4) +
   (x.val + p) % 4` (`Nat.div_add_mod`) and substituting gives `4 ∣ p`,
   contradicting step 2 (`primeOrbitAt_not_self`).
6. **Not all of `X`.** Apply step 5 with `y = x`: the prime orbit misses `x`,
   so it is not `univ` (`primeOrbitAt_not_univ`). The `x = 0` instance is
   `zero_not_mem_primeOrbit`, and the equivalent form `p % 4 ≠ 0` is
   `prime_iter_zero_val_ne_zero`.
7. **Closure.** Since `Fin 4` is finite, its topology is discrete and every
   subset is closed, so `closure(S) = S`. The closure of the prime orbit is
   therefore modelled by `PrimeOrbitClosure x := PrimeOrbitAt x`, and
   `primeOrbitClosure_not_univ` is the set inequality `closure ≠ univ`.
8. **Packaging.** `conjecture_00000000153_false` conjoins minimality with
   "for every `x`, the prime-index orbit closure is not `X`".

## Scope note

* **The closure is modelled, not built from a topology library.** `Fin 4` is
  finite, so with the discrete topology every subset is open and closed and
  `closure S = S`. The formalisation therefore represents
  `closure(primeOrbit x)` by the predicate `PrimeOrbitAt x` itself, and proves
  the set inequality `¬ (∀ y, PrimeOrbitAt x y)` (equivalently: the orbit omits
  `x`). No topology library, no `TopologicalSpace`, and no `IsClosed` is
  needed for the refutation. This modelling step is stated explicitly here so a
  reviewer can see exactly what is and is not formalised.
* **Stronger than needed.** `primeOrbitAt_not_univ` holds for **every**
  `x : Fin 4`, so the conjecture's conclusion fails at all four points, not
  only at `x = 0`. The `x = 0` statement (the point named in the conjecture's
  quantifier) is also exposed separately.
* **`Nat.Prime` is defined, not imported.** Core Lean and `Std` provide no
  `Nat.Prime`; it is Mathlib-only and Mathlib is not installed. `IsPrime` is
  the standard irreducibility definition. Only `p = 2` needs the definition in
  the proof of `4 ∤ p`.
* **The orbit is over primes, not over positions.** The conjecture writes
  `{T^{p_n} x : n ≥ 1}`, the primes enumerated in order. The formalisation uses
  `{T^p x : p prime}`; the two sets are equal because `n ↦ p_n` is a bijection
  onto the primes. Including `p = 2` does not change the outcome, since
  `2 % 4 = 2 ≠ 0`.
* **Not formalised.** The general theory of topological dynamical systems and
  the definition of minimality as "every orbit dense" are used only through the
  concrete finite model; the equivalence "minimal ⇔ every full orbit is `X`"
  is immediate for `Fin 4` because the orbit set is finite and closed. The
  caveat about adding a no-isolated-points / infinitude hypothesis is a
  mathematical remark about the statement's scope, not a Lean statement.

## Environment and pitfalls

* Lean 4.33.1, Lake, **no Mathlib**. `lake build` needs no cache download.
* Axiom audit: every theorem reports exactly `[propext, Quot.sound]`; there is
  no `sorryAx` and no Mathlib dependency.
* Core-Lean limitations encountered and avoided in this file:
  * `Nat.Prime` does not exist (defined `IsPrime` here).
  * `Function.iterate` and the notation `f^[n]` do not exist (defined `iter` by
    recursion here).
  * `Set`, `Finset`, `ZMod`, `Fintype`, `fin_cases`, `norm_num`, `ring`,
    `interval_cases` are Mathlib-only and are **not** used. The file relies on
    `omega`, `simp`, `rw`, `rcases`, `induction`, `Fin.ext`,
    `Nat.div_add_mod`, `Nat.dvd_of_mod_eq_zero`, and `Nat.mod_eq_of_lt`, all of
    which are available in core Lean / `Std`.
