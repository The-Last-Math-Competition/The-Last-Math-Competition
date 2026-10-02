# Disproof of conjecture `00000001581`

**Verdict: FALSE — the F_5-point count of the PVI monodromy manifold
(the Fricke surface) is not confined to N_5 ∈ {21, 26, 31}: the full
table over every κ ∈ F_5 is (41, 6, 16, 36, 26), and the count varies
with κ.**

## The conjecture (verbatim from `conjectures/00000001581.md`)

> Definition: The isomonodromy deformation and its monodromy manifold.
> Conjecture: The count of Q-points of the PVI monodromy manifold is
> N_p = p² + ap + 1 with a ∈ {−1, 0, 1} (point-count patterns).

## Object and computation

The PVI monodromy manifold is the Fricke surface (the GIT character
variety of the four-punctured sphere / the isomonodromy family)

    M_κ : x² + y² + z² − xyz = κ,

where κ is fixed by the local monodromy data: for the standard
specialization (p, q, r) = (1, 1, 1) one gets κ = 0; the generic
once-punctured-torus family runs over all integer κ. We enumerate ALL
F_5-points of M_κ for every κ ∈ F_5 (125 triples per row, no sampling):

| κ (mod 5) | 0  | 1 | 2  | 3  | 4 (=−1) |
|-----------|----|---|----|----|---------|
| N₅        | 41 | 6 | 16 | 36 | 26      |

The claimed pattern allows only N₅ ∈ {21, 26, 31}.

## The refutations

1. **Not well-defined:** the count varies with κ (41 ≠ 6), so "the
   count N_p of the monodromy manifold" cannot be a function of p alone;
   the pattern clause silently fixes no κ.
2. **Numerically false for every standard normalization:** κ = 0 (local
   data (1,1,1)) gives 41; κ = 1 gives 6; κ = 2 gives 16; κ = 3
   (e.g. the (1/2,1/2,1/2) local data reduced mod 5) gives 36 — all
   outside {21, 26, 31}. Only κ ≡ −1 (mod 5) coincidentally hits 26.
3. Even granting the conjecture the freedom to choose κ, the three
   claimed values are wrong as a pattern: two of the three allowed
   values (21, 31) occur for NO κ ∈ F_5.

## Verification

* `reproduce.py` — exhaustive triple loop over F_5³ (no sampling),
  reproducing the full table; also counts over F_2, F_3, F_7 for
  context: the counts are polynomials of degree 3 in general position
  behavior, not quadratic point-count patterns.
* Lean 4 (core, v4.33.1) — `lean4/`: the complete enumeration is a
  closed kernel computation per κ (Int arithmetic, no truncation); the
  five table entries, the four out-of-set violations, and the
  count-varies clause are all certified. All 10 audited theorems report
  `does not depend on any axioms`.

## Boundary

Only the displayed point-count pattern is refuted (at p = 5, where the
claimed pattern is checkable in full); the isomonodromy theory itself is
not addressed.
