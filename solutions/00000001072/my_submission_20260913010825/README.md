# Submission: Disproof of Conjecture 00000001072

**Verdict: FALSE**

## The conjecture (quoted)

> Let G(n,k,q) denote the number of k-dimensional planes of F_q^n.
> Conjecture: The prime-factor spectrum of the Gaussian-binomial formula
> G(n,k,q) = q^{(n−k)k}·[n choose k]_q consists exactly of the primes
> ≤ q^n − 1; every prime factor divides some q^i − 1 with i ≤ n, and
> conversely each such prime occurs for suitable (n,k).

## Counterexample I — "every prime factor divides some q^i − 1 with i ≤ n" is false

Take **(n, k, q) = (2, 1, 2)**:

| Quantity | Value |
|---|---|
| G(2,1,2) = 2^{(2−1)·1} · (2²−1)/(2−1) | **6** = 2·3 |
| Prime-factor spectrum of 6 | **{2, 3}** |
| q^1 − 1 = 2¹ − 1 | **1** (no prime factors) |
| q^2 − 1 = 2² − 1 | **3** (prime factors {3}) |
| Does the prime 2 divide some q^i − 1, i ≤ 2? | **NO** — 2 ∤ 1 and 2 ∤ 3 |

Yet 2 is a prime factor of G(2,1,2) = 6. The claim is violated.

## Counterexample II — "spectrum consists exactly of the primes ≤ q^n − 1" is false

Take **(n, k, q) = (2, 1, 3)**:

| Quantity | Value |
|---|---|
| G(2,1,3) = 3^{(2−1)·1} · (3²−1)/(3−1) | **12** = 2²·3 |
| Prime-factor spectrum of 12 | **{2, 3}** |
| Primes ≤ q^n − 1 = 3² − 1 = 8 | **{2, 3, 5, 7}** |
| {2,3} vs {2,3,5,7} | **not equal** — 5 ≤ 8 and 7 ≤ 8, but 5 ∤ 12 and 7 ∤ 12 |

The spectrum is a proper subset of the claimed set, so "exactly" fails.

**Supporting evidence**, (n, k, q) = (3, 1, 2): G(3,1,2) = 2^{2·1}·(2³−1)/(2−1) = 4·7 = **28**,
spectrum **{2, 7}**, while the primes ≤ 2³−1 = 7 are {2, 3, 5, 7} — 3 and 5 are missing.

All values were independently recomputed, and for k = 1 additionally verified by
direct brute-force enumeration of the affine lines of F_q^n as sets of points
(6, 12 and 28 lines respectively), so the counterexamples do not depend on the
formula's interpretation. See `reproduce.py`.

## Scope / boundaries

- We refute only the two directional claims of the conjecture:
  (a) "every prime factor divides some q^i − 1 with i ≤ n", and
  (b) "the spectrum consists exactly of the primes ≤ q^n − 1".
- The Gaussian-binomial counting formula itself, G(n,k,q) = q^{(n−k)k}·[n choose k]_q,
  is of course correct (for k = 1 it agrees with direct enumeration; more generally
  the formula is the conjecture's own definition of G).
- The third ("conversely") clause is not needed for the refutation and is not adjudicated here.

## Contents

- `reproduce.py` — self-contained script (stdlib only, no absolute paths): recomputes
  everything and asserts both violations. Run with `python3 reproduce.py`.
- `main.tex` + `build/main.pdf` — formal write-up of the disproof.
- `lean4/` — Lean 4 (core only, no Mathlib) machine-checked verification.
  Build with `cd lean4 && lake build`, then `lake env lean Check.lean`.
  All theorems are proved with `rfl`/`decide`: **zero axioms, zero `sorry`**
  (see `lean4/README.md` for the axiom audit).
