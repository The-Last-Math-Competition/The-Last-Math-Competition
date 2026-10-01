# Disproof of TLMC Conjecture 00000000462

**Verdict: FALSE**

## Conjecture (as stated)

tau(C_n(1,2)) — the number of spanning trees of the circulant graph on n vertices
with jumps 1 and 2 — satisfies a linear recurrence whose largest real characteristic
root tends to alpha^2 with alpha = 2 + sqrt(3), i.e. (2+sqrt(3))^2 = 7 + 4*sqrt(3)
≈ 13.9282 ("directly verifiable against the matrix-tree theorem").

## Attack

**1. Exact closed form (n ≥ 5).** The Laplacian eigenvalues of C_n(1,2) are
lambda_k = 2(1-cos(2πk/n)) + 2(1-cos(4πk/n)) = 2(1-c_k)(3+2c_k). With
prod_{k=0}^{n-1}(x - cos(2πk/n)) = 2^{1-n}(T_n(x)-1) and
T_n(-3/2) = (-1)^n L_{2n}/2 (L = Lucas numbers), the matrix-tree theorem gives

    tau(C_n(1,2)) = n * (L_{2n} - 2*(-1)^n) / 5     (n ≥ 5).

Certified by exact integer Bareiss determinants of the Laplacian minor for
n = 5,6,7,8,9,10,12,15,20,24 and by eigenvalue products (rel. err < 1e-14) for
n = 40, 80 — see `reproduce.py`.

**2. True growth rate.** Since L_{2n} ~ phi^{2n} and n^{1/n} → 1,

    tau^{1/n} → phi^2 = (3+sqrt(5))/2 ≈ 2.6180,

squeezed by phi^2 (n/5)^{1/n} ≤ tau^{1/n} ≤ phi^2 (1 + phi^{-2n})^{1/n} (n/5)^{1/n}.
Samples (recomputed, matching the verifier's 2.81 / 2.76 / 2.71):

| n  | tau^{1/n} |
|----|-----------|
| 20 | 2.805939  |
| 40 | 2.757735  |
| 80 | 2.710359  |

**3. Eigenvalue ceiling.** Every eigenvalue lambda_k ≤ 8 termwise; the sharp
supremum of f(t) = 4 - 2cos t - 2cos 2t is 25/4 = 6.25 at cos t = -1/4. Hence
tau^{1/n} ≤ ((1/n)*6.25^{n-1})^{1/n} < 6.25 < 8 for all n ≥ 5, while the claimed
root limit alpha^2 = 7 + 4*sqrt(3) > 8 (since sqrt(3) > 1/4). The claimed limit is
impossible: the growth rate the conjecture's own reading ("directly verifiable
against the matrix-tree theorem") demands, tau^{1/n} → alpha^2, is contradicted by
tau^{1/n} → phi^2 ≈ 2.618, separated rigorously by

    phi^2 < 3 < 25/4 = 6.25 < 8 < 9 < alpha^2 < 14.

Moreover the sequence n ↦ tau(n)/n is C-finite with characteristic roots phi^2 and
-phi^{-2} only (Lucas recurrence), so the minimal recurrence has largest real root
phi^2 ≠ alpha^2 for every n, not just in the limit.

## Verified integers (Lean-certified, zero axioms)

| n  | tau(C_n(1,2)) |
|----|-----------------------|
| 5 | 125 |
| 6 | 384 |
| 7 | 1183 |
| 8 | 3528 |
| 9 | 10404 |
| 10 | 30250 |
| 12 | 248832 |
| 15 | 5581500 |
| 20 | 915304500 |
| 24 | 51599794176 |
| 40 | 418891171182561000 |
| 80 | 43867453323674409143926999140738000 |

Decisive sandwich at n = 80 (all four links are Lean theorems via `decide`):
5^80 < tau(80)*2^80 ∧ tau(80) < 8^80 ∧ 1 < 48 ∧ 48 < 49, i.e. 5/2 < tau^{1/80} < 8
and 8 < alpha^2 < 14.

## Boundary

* The closed form is valid for n ≥ 5 (jumps 1, 2, -1, -2 distinct mod n).
* n = 1, 2: degenerate (self-loops / parallel edges); n = 3: multigraph
  (jump 2 ≡ -1); n = 4: jump 2 ≡ -2 and C_4(1,2) = K_4 with tau = 16, while the
  formula would give 36 — excluded, consistent with the n ≥ 5 restriction.
* Irrelevant to the verdict: the conjecture is asymptotic in n.

## Machine verification

`lean4/` (core Lean 4.33.1, no Mathlib): `lake build && lake env lean Check.lean`
prints "does not depend on any axioms" for all 25 declarations. Zero axioms
(no propext, no Quot.sound, no sorry, no native_decide).

## Reproduce

```
python3 reproduce.py          # standalone; standard library only
```
