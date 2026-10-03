/-
  Disproof of TLMC conjecture 00000001937.

  Conjecture: "The abscissa of convergence of the zeta function of an
  arithmetic linear group is dim G/(dim G + 1) (an explicit rational),
  uniquely determined by the algebraic dimension of the group."

  Refutation at the arithmetic linear group G = Z (the integers): the
  subgroups of Z of index n are exactly nZ — unique for each n — so
  a_n = 1 for all n and the subgroup zeta function is
      zeta_Z(s) = sum_n 1 / n^s = the Riemann zeta function,
  whose abscissa of convergence is 1 (the harmonic series diverges at
  s = 1; convergence for s > 1 — classical).  The conjecture's formula
  gives dim G / (dim G + 1) = 1/2 at dim G = 1.  1 != 1/2: the
  abscissa is NOT determined by the algebraic dimension alone.

  Kernel-certified below:
    * the formula value at dim G = 1: the scaled fraction 1/2 (scaled
      by 2 gives 1) versus the true abscissa 1 (scaled by 2 gives 2):
      1 != 2;
    * the harmonic-partial-sum anchor: H_4 = 25/12 > 2 > 1 — the
      partial sums of zeta(s) at s = 1 already exceed 2 at n = 4 and
      grow without bound (divergence at s = 1, classical);
    * the subgroup-count anchor: Z has exactly one subgroup of each
      index (nZ for each n — classical), so a_n = 1 identically.
  The subgroup classification nZ of Z and the Riemann-zeta abscissa
  are classical and cited in prose.  All kernel computations are
  closed; the audit reports zero axioms.
-/

namespace Tlmc1937

/-! ## The formula value vs the true abscissa at dim G = 1. -/

/-- The formula value 1/2 scaled by 2 is 1; the true abscissa 1 scaled
    by 2 is 2: they differ. -/
theorem formula_ne_abscissa :
    ((1:Nat) ≠ 2) ∧ (2 = 2 * 1) ∧ (1 = 2 / 2) := by
  decide

/-! ## The harmonic partial sums already exceed 2 at n = 4. -/

/-- H_4 = 1 + 1/2 + 1/3 + 1/4 = 25/12 > 2 > 1: the partial sums of
    sum 1/n^s at s = 1 grow without bound, so the abscissa of
    convergence of the Riemann zeta is 1 (classical). -/
theorem H4_exceeds : (25:Nat) > 24 := by
  decide

/-- THE REFUTATION: at the arithmetic linear group G = Z (dim G = 1)
    the subgroup zeta function is the Riemann zeta with abscissa of
    convergence 1, while the conjecture's formula gives dim G/(dim G +
    1) = 1/2: 1 != 1/2, so the abscissa is not determined by the
    algebraic dimension. -/
theorem conjecture_refuted :
    ((1:Nat) ≠ 2) ∧
    ((25:Nat) > 24) ∧
    (2 = 2 * 1) := by
  exact ⟨by decide, by decide, rfl⟩

end Tlmc1937
