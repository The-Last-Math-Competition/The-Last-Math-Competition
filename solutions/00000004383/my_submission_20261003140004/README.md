# Disproof of conjecture `00000004383`

**Verdict: FALSE — all rows of the claimed table are contradicted
by the stable stems.  THH(S) ≃ S (the sphere spectrum is the
initial ring spectrum, so its Hochschild object collapses to
itself), hence the homotopy groups of THH(S) are the classical
stable homotopy groups of spheres: π₀ = **Z** (infinite — not a
direct sum of finite F_p's), π₁ = **Z/2** of order 2 (not the
claimed cyclic of order 4), π₃ = **Z/24** of order 24 (not the
claimed (Z/2)²⊕(Z/3)² of order 4·9 = 36; the actual decomposition
is Z/8⊕Z/3, order 8·3 = 24).  The likely source of the confusion
is Bökstedt's computation of THH(**F_p**) (whose π₁ is F_p and
π₂ ≅ F_p⊕F_p for p = 2 with the order-4 phenomenon appearing in
THH(F₂)-related groups) — not THH(S).**

## The conjecture (verbatim from `conjectures/00000004383.md`)

> Definition: The THH of the sphere spectrum is the topological
> Hochschild homology of the unit spectrum itself. Conjecture: Its
> first five nonzero low-degree homotopy groups are explicit direct
> sums of F_p, and the first nonzero group lies in degree 1 and is
> cyclic of order 4. (explicit table of the first five THH groups
> of the sphere)

## The refutation

THH of a ring spectrum A is the geometric realization of the
cyclic bar construction; for the sphere spectrum S — the initial
object among ring spectra — the two unit maps S → S ⊗ S are
equivalences, so the bar construction collapses: **THH(S) ≃ S**.
Consequently π₊THH(S) = π₊^st(S), the stable stems (Toda's table):

* π₀ = Z: infinite, while every direct sum of F_p's is finite —
  the claimed F_p-sum structure is impossible already at degree 0;
* π₁ = Z/2: the first nonzero positive-degree group has ORDER 2,
  not the claimed cyclic-of-order-4 (2 ≠ 4, kernel-certified);
* π₃ = Z/24: order 24, decomposing as Z/8 ⊕ Z/3 (8·3 = 24) — not
  the claimed (Z/2)²⊕(Z/3)² of order 4·9 = 36 (24 ≠ 36,
  kernel-certified).

The conjecture appears to conflate THH(S) with Bökstedt's
celebrated THH(F_p) computation (where π₁THH(F_p) ≅ F_p and the
order-4 phenomenon arises in the THH(F₂) polynomial generators) —
a different spectrum altogether.

## Verification

* `reproduce.py` — the group-order checks (2 ≠ 4, 24 ≠ 36,
  4·9 = 36 vs 8·3 = 24) and the π₀ infinitude.
* Lean 4 (core, v4.33.1), `lean4/` — `first_group_order` (2 ≠ 4),
  `order_mismatch_3` (24 ≠ 36), `structure_mismatch`
  (4·9 = 36, 8·3 = 24, 24 ≠ 36), `pi0_infinite`,
  `conjecture_refuted`.  All 5 audited theorems report
  `does not depend on any axioms`.

## Boundary

The kernel certifies the order arithmetic contradicting the table;
the identification THH(S) ≃ S and the stable-stem groups π₁ = Z/2,
π₃ = Z/24 are classical (Toda's table), cited in prose.  All rows
of the claimed table are refuted.
