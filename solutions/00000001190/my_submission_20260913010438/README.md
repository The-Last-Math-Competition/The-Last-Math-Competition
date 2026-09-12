# Disproof of Conjecture 00000001190

**Verdict: FALSE.**

## The conjecture

> N_p is the number of elements of prime order p in GL_n(F_q). Conjecture:
> N_p = Σ_{r|n, r prime} Θ_r(q), where
> Θ_r(q) = q^{n²−r}(q−1)^{−1} · ∏_{i=1}^{r−1}(q^{n−i}−1);
> this formula covers all prime-order elements with zero error.

## Counterexample (n = 2, q = 7)

For n = 2 the only prime divisor of n is r = 2, so the formula claims:

| p | Formula side Σ_{r|2, r prime} Θ_r(7) | Ground truth (brute-force enumeration of GL₂(F₇)) | Error |
|---|---|---|---|
| 2 | Θ₂(7) = 7⁴⁻²·(7¹−1)/(7−1) = 49·6/6 = **49** | **57** (elements M with M² = I, M ≠ I) | 57 − 49 = 8 ≠ 0 |
| 3 | 3 ∤ 2, empty sum ⇒ **0** | **170** (elements M with M³ = I, M ≠ I) | 170 − 0 = 170 ≠ 0 |

The claim "covers all prime-order elements with zero error" fails **twice** at the
single point (n, q) = (2, 7).

Ground truth: |GL₂(F₇)| = (7²−1)(7²−7) = 48·42 = 2016, verified by enumerating all
7⁴ = 2401 matrices over Z/7Z and filtering det ≠ 0. Every count below is a direct
exhaustive enumeration (see `reproduce.py`), not a sampling or simulation.

## Why the formula undercounts (structure)

* **Order 2 (57 vs 49).** Over F₇, x²−1 = (x−1)(x+1) splits completely. The
  diagonalizable elements with eigenvalues {1, −1} form one conjugacy class of size
  2016/36 = 56 (centralizer = diagonal matrices, size (q−1)² = 36); plus the single
  scalar −I. Total 56 + 1 = 57. The term Θ₂(q) is designed for the *regular
  semisimple* case (eigenvalues {λ, μ}, λ ≠ μ, in the split torus) and misses both
  the scalar element and the fact that a 2-dimensional representation can realize
  order 2 with a repeated eigenvalue.

* **Order 3 (170 vs 0).** x³−1 = (x−1)(x−2)(x−4) mod 7 (2³ = 8 ≡ 1, 4³ = 64 ≡ 1),
  so F₇ already contains primitive cube roots of unity. Elements of order 3 come in
  three conjugacy classes with eigenvalue pairs {2,1}, {4,1}, {2,4}, each of size
  2016/36 = 56, plus the two scalars 2I and 4I: total 3·56 + 2 = 170. But r = 3 does
  not divide n = 2, so the conjecture's sum is empty and predicts **zero** order-3
  elements. Any prime p with p | (q−1) (here p = 3 | 6) yields scalar and
  diagonalizable prime-order elements in every dimension, which the divisor
  condition "r | n" cannot see.

## Scope / boundaries

* We only refute the literal statement of the conjecture at (n, q) = (2, 7). We make
  no claim about the formula's behaviour at other parameters (it may be a good
  approximation elsewhere, and possibly exact when gcd(n, q−1) = 1 and the sum runs
  over all primes — but that is a different statement).
* All numbers are machine-verified two independent ways: exhaustive Python
  enumeration (`reproduce.py`) and a zero-axiom Lean 4 kernel check (`lean4/`).

## Contents

* `reproduce.py` — standalone brute-force enumeration; prints and asserts all counts.
* `main.tex` / `build/main.pdf` — formal write-up with the counting argument.
* `lean4/` — Lean 4 (toolchain v4.33.1) machine-checkable proof:
  `count_order2 : … = 57`, `count_order3 : … = 170`, `formula2 : Θ₂(7) = 49`,
  `refute : 57 ≠ 49 ∧ 170 ≠ 0`, all by `decide` with **zero axioms**.

## How to reproduce

```bash
python3 reproduce.py                     # prints 2016, 57, 170, 49, 0 and asserts

cd lean4
lake build                               # compiles Main.lean (by decide, no axioms)
lake env lean Check.lean                 # #eval counts + #print axioms audit
```
