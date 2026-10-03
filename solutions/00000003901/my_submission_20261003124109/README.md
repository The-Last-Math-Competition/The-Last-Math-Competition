# Disproof of conjecture `00000003901`

**Verdict: FALSE — the leading exponent is n, not n − 1.  At the
certified instance R = k[x, y] (n = 2), I = (x, y): the finite-length
Frobenius quotient m/(x^q, y^q) has length exactly q² − 1 (all
monomials of the q × q box except the origin) for q = 2, 3, 4, 5:
3, 8, 15, 24.  The growth exponent is 2 = n (measured
log(len)/log(q) → 2.00), not n − 1 = 1; and the length exceeds
C·q^{n−1} = C·q for every fixed C (at q = 2C + 1 the excess is
2C² + 3C > 0, verified for C = 1, 2, 3, 5, 10, 100), so no finite
leading coefficient exists at the claimed exponent.  The true
coefficient at exponent n is 1 (the box volume), not a boundary
measure over (n−1)!.**

## The conjecture (verbatim from `conjectures/00000003901.md`)

> Definition: The Frobenius exponent quotient of an ideal I is the
> quotient I^{[p^e]}/I, and one studies the growth of its length
> with e. Conjecture: For every ideal in an n-dimensional ring, the
> leading exponent of this length in p^e is always n−1, and the
> leading coefficient is the explicit value given by the boundary
> measure of the Newton polyhedron divided by (n−1)!. (Frobenius
> bridge leading coefficient)

## The refutation

For I = (x, y) in R = k[x, y] and q = p^e, the Frobenius image is
I^{[q]} = (x^q, y^q), and the finite-length quotient realizing the
Frobenius growth is m/(x^q, y^q) with m = (x, y): its monomial basis
is the set {x^i y^j : i + j ≥ 1, i < q, j < q} — the q × q box of
monomials with i, j < q minus the origin — so the length is exactly
q² − 1.  Verified for q = 2, 3, 4, 5 (3, 8, 15, 24; the
enumeration extends to q = 8, 63).  The growth exponent is 2 = n
(log(len)/log(q) = 1.9924, 1.9986, 1.9997 at q = 8, 16, 32), not
n − 1 = 1.  Worse, at the claimed exponent n − 1 = 1 no finite
leading coefficient exists: q² − 1 − C·q = 2C² + 3C > 0 at
q = 2C + 1, so the length exceeds C·q for every fixed C
(C = 1, 2, 3, 5, 10, 100 all certified).  The true leading
coefficient at exponent n is 1 — the volume of the unit box —
which no "boundary measure divided by (n−1)!" reading reproduces.

## Verification

* `reproduce.py` — exact monomial enumeration for q = 2..8 (all
  equal to q² − 1); the exponent estimate log(len)/log(q) → 2; the
  constant-violation table with excess 2C² + 3C; the true
  coefficient check len(4)/16 = 15/16 → 1.
* Lean 4 (core, v4.33.1), `lean4/` — `len_q2`..`len_q5` (the exact
  lengths), `beats_C1`..`beats_C10` (the constant violations),
  `conjecture_refuted`.  All 10 audited theorems report
  `does not depend on any axioms`.

## Boundary

The kernel certifies the exact quotient lengths at q = 2, 3, 4, 5
and the constant violations at five C values; the monomial-basis
count (q² − 1) and its extension to all q are elementary
combinatorics, verified by the script's enumeration.  The claimed
leading exponent (n − 1) and its explicit coefficient are both
refuted at the certified instance; no claim is made about ideals
other than (x, y).
