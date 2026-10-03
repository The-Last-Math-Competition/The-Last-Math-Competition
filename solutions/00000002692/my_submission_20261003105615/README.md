# Disproof of conjecture `00000002692`

**Verdict: FALSE — all three clauses fail at the certified instance
f(x) = 5x + x² on Z_5. (1) The multiplier f'(0) = 5 is 0 mod p = 5,
and 0 has NO multiplicative order mod 5 (0^k = 0 ≠ 1 for all k ≥ 1):
the conjecture's denominator does not exist. (2) The basin of 0 is
exactly 5Z_5 — measure 1/5 of the ball, denominator 5 = p, not any
"order of the multiplier" (verified as an exact 1/5-fraction on the
grid models Z/25, Z/125, Z/625). (3) The basin-boundary shell
5Z_5∖25Z_5 maps straight to 0 (f(x) = x(5+x) ≡ 0 mod 25 for
x ≡ 0 mod 5), so its points are not periodic — the boundary of the
basin is not the closure of periodic points (periodic points mod 25:
{0, 21 = −4, 1, 6, 11, 16}, all off the shell).**

## The conjecture (verbatim from `conjectures/00000002692.md`)

> Definition: p-adic contraction of dynamical systems: iterative
> convergence on p-adic balls. Conjecture: The measure of the
> attracting basin of a p-adic contraction is an explicit fraction of
> the ball volume; the denominator of the fraction is the order of
> the multiplier mod p, and the boundary of the basin is the closure
> of periodic points.

## The refutation

Take f(x) = 5x + x² = x(5 + x) on Z_5 with the attracting fixed
point 0 (multiplier f'(0) = 5: a contraction in the p-adic sense,
|f(x)| ≤ |x|/5 near 0).  The conjecture's three clauses:

1. **Denominator = ord_p(multiplier)**: here 5 mod 5 = 0, and 0 has
   no multiplicative order modulo 5 — the denominator does not
   exist.  Even the charitable reading ord(0) = 1 would give the
   fraction 1/1, while the true basin is
2. **Explicit fraction**: the basin of 0 is exactly 5Z_5 (x ∈ 5Z_5
   ⟹ |f(x)| ≤ |x|/5 ⟶ 0; x ∉ 5Z_5 ⟹ |f(x)| = |x| = 1 forever),
   i.e. measure exactly 1/5 of the ball — denominator p = 5, not an
   order.  Verified exactly on the grid models: the basin is the set
   of multiples of 5, a 1/5-fraction at depths k = 2, 3, 4
   (5/25, 25/125, 125/625).
3. **Boundary = closure of periodic points**: the basin-boundary
   shell 5Z_5∖25Z_5 consists of points x with f(x) ≡ 0 (mod 25)
   (x(5+x) ≡ 0 mod 25 whenever x ≡ 0 mod 5, 25 ∤ x) — one step into
   the basin, never to return.  These points are NOT periodic: mod
   25 the periodic points are {0, 21 = −4 (fixed), 1, 6, 11, 16
   (a 4-cycle)}, all off the shell.  The boundary of the basin is
   not the closure of periodic points.

## Verification

* `reproduce.py` — no order of 0 mod 5 (k = 1..99); basin =
  multiples of 5 exactly at depths 2..4 (1/5-fraction); periodic
  points mod 25 enumerated; the shell {5,10,15,20} maps to 0 and is
  disjoint from the periodic set.
* Lean 4 (core, v4.33.1), `lean4/` — `multiplier_zero_mod_p`,
  `zero_has_no_order` (∀ k ≥ 1, 0^k ≠ 1, by cases on k),
  `basin_fraction` (5·5 = 25), `denominator_mismatch` (5 ≠ 1),
  `shell_maps_to_zero` / `shell_not_periodic` (f mod 25 on
  {5,10,15,20}), `conjecture_refuted`.  All 7 audited theorems
  report `does not depend on any axioms`.

## Boundary

The kernel certifies the depth-2 grid instance (Z/25): the
multiplier's residue, the non-existence of its order, the basin
fraction, and the shell's one-step-to-zero behavior.  The passage to
Z_5 (the basin = 5Z_5 identification and its measure) is classical
non-archimedean dynamics, cited in prose and verified by the script
at depths 2..4.  All three clauses of the conjecture are refuted at
this instance.
