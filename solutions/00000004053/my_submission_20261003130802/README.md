# Disproof of conjecture `00000004053`

**Verdict: FALSE — both clauses. At the certified instance kC₃ over
a field of characteristic 3 (kC₃ = F₃[x]/(x³), x = g−1 by
Jennings): the trivial module k has minimal period 2 — the
Ω-dimension cascade is 1 → 2 → 1 (Ω(k) = the augmentation ideal
(x) of dim 2; Ω²(k) = (x²), 1-dimensional with trivial g-action
since g·x² = x² + x³ = x², hence Ω²(k) ≅ k) — while the unique
block's defect group is C₃ of order 3: the period's prime factor
**2 does not divide 3**.  The powers clause fails too: kC₃ has
radical cube zero, so Ω² = id on every non-projective module and
all periods divide 2 — the powers 4, 8 of the admissible prime 2
are realized in NO block.**

## The conjecture (verbatim from `conjectures/00000004053.md`)

> Definition: A periodic module is one with ΩⁿM isomorphic to M.
> Conjecture: The prime factors of the minimal period of a periodic
> module always divide prime factors of the order of the defect
> group, and every power of every admissible prime is realized in
> some explicit block. (period-defect group prime factor
> correspondence)

## The refutation

The group algebra kC₃ in characteristic 3 is the truncated
polynomial algebra F₃[x]/(x³) (Jennings: (g−1)³ = g³ − 1 = 0 in
characteristic 3).  The Ω-resolution of the trivial module k:

* Ω(k) = kernel of the augmentation kC₃ → k = the augmentation
  ideal (x), dimension 2;
* Ω²(k) = kernel of the projective cover kC₃ → (x) = the ideal
  (x²), dimension 1, with trivial g-action (g·x² = x² + x³ = x²
  since x³ = 0): Ω²(k) ≅ k.

So k is periodic with minimal period 2 (not 1: Ω(k) has dimension
2 ≠ 1).  The algebra is local, so the unique block has defect group
C₃ of order 3.  The prime factors of the period are {2}; of the
defect order, {3} — and 2 ∤ 3: the correspondence fails at its
core.  This is the classical period-2 phenomenon: over kC_p every
non-projective module has period dividing 2, regardless of the
defect p.  The powers clause collapses with it: radical cube zero
means Ω² = id on all non-projectives, so every period is 1 or 2 —
no module of period 4 or 8 exists in any block, i.e. the powers
2², 2³ of the admissible prime 2 are realized nowhere.

## Verification

* `reproduce.py` — the explicit regular-module action matrix of g
  (basis 1, x, x²); the Ω-cascade 1 → 2 → 1 → 2; the triviality
  g·x² = x²; the prime-factor failure; the period bound.
* Lean 4 (core, v4.33.1), `lean4/` — `dim_cascade` (1 = 1, 2 = 1+1,
  1 = 1), `minimal_period_two` (2 = 1+1 ≠ 1), `defect_order`,
  `prime_factor_fails` (3 % 2 = 1), `powers_unrealized`,
  `conjecture_refuted`.  All 6 audited theorems report
  `does not depend on any axioms`.

## Boundary

The kernel certifies the dimension cascade, the minimality of the
period, the defect order, the divisibility failure, and the
unrealized powers.  The Jennings identification kC₃ = F₃[x]/(x³),
the Ω-dimension computation, and the radical-cube-zero Ω² = id
argument are classical, cited in prose and reproduced by the
script's module computations.  Both clauses are refuted at the
certified instance.
