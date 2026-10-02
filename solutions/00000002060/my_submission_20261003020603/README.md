# Disproof of conjecture `00000002060`

**Verdict: FALSE — the cyclic group C₁₂ = Z/12Z is a finite member of
the variety of groups, so 12 IS in its spectrum; and 12 = 4·3 has two
distinct prime divisors (2 and 3) plus the square divisor 4: it is
neither a prime power nor squarefree — the claimed "not realizable"
complement IS realized.**

## The conjecture (verbatim from `conjectures/00000002060.md`)

> Definition: The spectrum of a locally finite variety is the set of
> cardinalities of its finite algebras. Conjecture: The limit set of
> spectra of all finite members of the variety of groups equals the set
> of prime powers ∪ squarefree orders (a formula); the complement
> (neither prime powers nor squarefree) is not realizable.

## The counterexample: C₁₂

1. **C₁₂ exists in the variety of groups.** Z/12Z under addition is a
   12-element group (classical).
2. **12 is not a prime power.** 12 has the two distinct prime divisors
   2 and 3 (kernel-certified: 2 | 12 = 2·6, 3 | 12 = 3·4, 2 ≠ 3). A
   prime power pᵏ (k ≥ 1) has the single prime divisor p — so 12 is not
   a prime power (and 12 itself is not prime: 4 | 12 with 4 ≠ 1 ≠ 12,
   kernel-certified).
3. **12 is not squarefree.** 4 = 2·2 divides 12 (12 = 4·3,
   kernel-certified): a square divisor > 1 exists.

So the claimed complement (orders neither prime powers nor squarefree)
IS realized — by the most basic finite abelian group after C₆ — and the
"spectrum = prime powers ∪ squarefree" formula is false. (Also: the two
allowed classes do not even cover 12's neighbors — e.g. 18 = 2·3² is
neither — the complement is infinite.)

## Verification

* `reproduce.py` — factorizes 12 = 2²·3; enumerates the divisors of 12
  and checks that exactly {2, 3} are prime (so 12 is not a prime power)
  and that 4 | 12 (so 12 is not squarefree); confirms C₁₂ = Z/12Z is a
  12-element group; sweeps n = 2..60 showing the complement contains
  12, 18, 20, 24, 28, ... (infinite).
* Lean 4 (core, v4.33.1) — `lean4/`: the divisor certificates
  (2 | 12, 3 | 12, 4 | 12 with 12 = 4·3), the primality failure of 12,
  and the refutation. All 6 audited theorems report `does not depend on
  any axioms`. The existence of Z/12Z as a 12-element group is
  classical and cited.

## Boundary

Only the displayed spectrum formula is refuted (via C₁₂); the genuine
theory of spectra of group varieties is not addressed.
