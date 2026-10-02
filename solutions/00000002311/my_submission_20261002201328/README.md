# Disproof of conjecture `00000002311`

**Verdict: FALSE (the Frobenius-tightness clause) — the Frobenius group
C₇⋊C₆ realizes constant c = 1, not c = 1/2.**

## The conjecture (verbatim from `conjectures/00000002311.md`)

> Definition: The derangement proportion is the proportion of
> fixed-point-free elements in a transitive group. Conjecture: The
> proportion is bounded below by (1/|Ω|)·c (c = 1/2) (Boston–Shalev type);
> **tightness of the corrected constant is verified by Frobenius groups.**

**Object consistency.** We attack exactly the boldfaced clause: that
Frobenius groups witness tightness of c = 1/2, i.e. attain proportion
(1/2)·(1/|Ω|).

## The refutation

Take the Frobenius group **G = C₇⋊C₆ = AGL(1,7)** acting transitively on
Ω = ℤ/7 (|G| = 42, |Ω| = 7). Its elements are the affine maps
x ↦ ax + b (a ∈ {1..6}, b ∈ ℤ/7):

- a = 1: translations — fixed-point-free iff b ≠ 0 (**6 elements**);
- a ≠ 1: exactly one fixed point (x = b/(1−a); a−1 invertible mod 7).

So the derangements number exactly **6** (kernel-enumerated over all 42
maps × 7 points), and the derangement proportion is

    6/42 = **1/7** = 2·(1/14),

while tightness of c = 1/2 would require the proportion
(1/2)·(1/7) = **1/14** (i.e. 3 of 42). The constant C₇⋊C₆ realizes is

    proportion × |Ω| = (1/7)·7 = **c = 1**,

not c = 1/2: Frobenius groups do **not** verify tightness of the corrected
constant. (The same computation for C_p⋊C_m gives c = (p−1)/m, which for
the divisibility-constrained Frobenius complements is never pinned to
1/2 — the conjecture's claimed verification fails at the smallest
example.)

## Reproduce

`python3 reproduce.py` — enumerates all 42 affine maps on ℤ/7 (and also
S₃ on 3 points: proportion 1/3), counts derangements, and prints the
realized constants. Exit 0.

Lean: `cd lean4 && lake build && lake env lean Check.lean` — 3 theorems
(`derangements_six` = 6 by kernel enumeration, `order_42`,
`not_half_tight` (6 ≠ 3)), all `does not depend on any axioms`.

## Boundary

The lower-bound clause (≥ (1/2)(1/|Ω|)) is NOT disputed — 1/7 ≥ 1/14
holds; only the "tightness verified by Frobenius groups" clause is
refuted at the smallest Frobenius example.
