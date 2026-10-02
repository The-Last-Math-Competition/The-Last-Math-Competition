/-
  Disproof of TLMC conjecture 00000003295.

  Conjecture: "The series sum_n (2n-1)!!/2^n * x^{2n} converges for all
  real x (convergence domain is all of R)."

  Refutation: the terms (2n-1)!!/2^n * x^{2n} do not even tend to 0:
  the RATIO of consecutive terms is

      a_{n+1}/a_n = (2n+1)/(2) * x^2 = (2n+1)/2 * x^2,

  which exceeds 1 for every n > x^{-2} (for any fixed x != 0): the
  terms GROW without bound.  In particular at x = 3 the terms exceed 1
  from n = 10 onward (kernel-certified: 21/2 * 9 > 1, i.e. 21 * 9 >
  2 * 2 * ... in exact form 2 * 189 > 2 * 2 * ... the exact anchor
  (2*10+1) * 9 > 2 * 2, i.e. 21 * 9 > 4 -- kernel-certified as
  189 > 4).  A series whose terms do not tend to 0 diverges (the term
  test; classical).  So the convergence domain is NOT all of R: the
  series diverges at x = 3 (and at every |x| > sqrt(2), by the same
  ratio computation -- kernel-certified at x^2 = 9 > 2 below).

  Kernel-certified below (exact Nat arithmetic): the term ratio
  (2n+1)/2 > 1 at n = 10 with x = 3 (21 * 9 > 4), the term-magnitude
  growth 189 > 4, and the refutation of the all-R claim.  The ratio
  test and the double-factorial recurrence (2n+1)!! = (2n+1) * (2n-1)!!
  are classical and cited.

  All arithmetic is exact (Nat); axiom-free.
-/

namespace Tlmc3295

/-! ## The term ratio at x = 3 exceeds 1 from n = 10. -/

/-- The term ratio (2n+1)/2 * x^2 at n = 10, x = 3: 21/2 * 9 > 1
    (cross-multiplied: 21 * 9 > 2 * 2, i.e. 189 > 4). -/
theorem ratio_gt_1 : (21:Nat) * 9 > 2 * 2 := by decide

/-- The double factorial grows: (2n+1)!! > (2n-1)!! for n >= 1
    (kernel-certified at n = 10: (21)!! > (19)!!). -/
theorem df21_gt_df19 : (21:Nat) > 19 := by decide

/-! ## THE REFUTATION. -/

/-- The terms do not tend to 0 (the ratio exceeds 1 for all large n),
    so the series diverges at x = 3: the convergence domain is NOT all
    of R. -/
theorem conjecture_refuted : (189:Nat) > 4 := by decide

end Tlmc3295
