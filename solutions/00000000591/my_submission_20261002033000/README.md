# Disproof of TLMC conjecture 00000000591

**Verdict: FALSE.**

## The conjecture

Wilf's conjecture: `e * n(S) >= g(S) + e` for a numerical semigroup `S` of
embedding dimension `e`, with `n(S) = #{s in S : 0 <= s <= g(S)}` and `g(S)` the
Frobenius number. The new-direction conjecture 00000000591 claims that on
embedding-dimension-3 semigroups the surplus satisfies

    (3*n(S) - g(S) - 3) / g(S)  ->  0    as g(S) -> infinity,

with an explicit convergence rate.

## The attack

1. **Universal ceiling (pairing bound).** For any numerical semigroup and
   `0 < x < g`, the pair `x` and `g-x` cannot both be nongaps (else
   `g = x + (g-x)` would be a nongap); if `g` is even, `g/2` is a gap. Hence
   `n <= ceil(g/2)` and `surplus/g <= (g-3)/(2g) < 1/2` — for *every*
   numerical semigroup, of any embedding dimension.

2. **An explicit family attaining the ceiling.** For distinct primes `p,q,r`,
   the complete-intersection semigroup `S = <pq, pr, qr>` has embedding
   dimension 3 and is symmetric, so `n = (g+1)/2` exactly and
   `surplus = (g-3)/2`, i.e. `surplus/g = (g-3)/(2g) -> 1/2` as
   `g = 2pqr - pq - pr - qr -> infinity`. The convergence-to-0 claim fails
   maximally. All three formulas were verified computationally on every prime
   triple with `200 <= g <= 5000`.

3. **Lean-verified concrete instances** (core Lean 4.33.1, all proofs
   `rfl`/`decide`, zero axioms, zero `sorry`):

   | S | g | n | surplus | surplus/g |
   |---|---|---|---|---|
   | <17,23,29> | 215 | 104 | 94 | 0.4372 |
   | <9,13,101> | 95 | 48 | 46 | 0.4842 |
   | <15,33,55> | 227 | 114 | 112 | 0.4934 |
   | <35,55,77> | 603 | 302 | 300 | 0.4975 |

   For each: `g` is certified as *the* Frobenius number (gap at `g`, plus
   `min` consecutive nongaps above `g`), `n` is the exact nongap count on
   `[0,g]`, and `surplus/g > 2/5`. One member of the symmetric family was
   additionally computed to `g = 2,194,011` with ratio `0.4999993`.

4. **Statistical sweep.** Among all triples `6 <= a < b < c <= 30` generating a
   numerical semigroup with `g >= 200` (97 semigroups), 93 have
   `surplus/g in [0.40, 0.505]`; generic consecutive-odd triples
   `<2k+1, 2k+3, 2k+5>` drift from 0.43 (k=10) to 0.496 (k=200). The ratio is
   pinned near 1/2, never near 0.

## Boundary (what remains true)

- Wilf's inequality itself holds on every example here (e.g. `3*104 = 312 >= 218`)
  — the disproof targets only the new vanishing-rate direction.
- The pairing bound shows the ratio can never exceed `(g-3)/(2g) -> 1/2`, so
  `1/2` is the exact asymptotic ceiling; symmetric semigroups attain it, and the
  conjecture's `-> 0` is false in the strongest possible way.
- `<9,13,101>` has `g = 95 < 200` (as in the original verdict note); the
  g >= 200 requirement is covered by the other instances and the family results.

## Files

- `main.tex`, `build/main.pdf` — write-up.
- `reproduce.py` — independent recomputation of every number above
  (`python3 reproduce.py`, prints PASS/FAIL per claim).
- `lean4/` — Lean package; `lake build && lake env lean Check.lean` must print
  "does not depend on any axioms" for all 21 theorems.
