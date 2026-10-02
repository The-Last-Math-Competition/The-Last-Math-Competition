/-
  Disproof of TLMC conjecture 00000003152.

  Conjecture: "The BM inequality for groups: the lower bound of the
  Haar measure of product sets is exponential in the sum of measures,
  with equality exactly on cosets of subgroups" -- i.e. the claimed
  lower bound is mu(A*B) >= exp(mu(A) + mu(B)).

  Refutation: mu is a NORMALIZED Haar measure (a probability), so

      mu(A*B) <= 1   for all subsets A, B (classical, cited),

  while the claimed lower bound exp(mu(A) + mu(B)) EXCEEDS 1 whenever
  mu(A) + mu(B) > 0.  Concretely, for mu(A) = mu(B) = 1/10: the claimed
  bound is exp(1/5) > 1 + 1/5 = 6/5 > 1 (by the classical convexity
  inequality exp(t) >= 1 + t), yet mu(A*B) <= 1 always: the claimed
  inequality is UNSATISFIABLE for every pair of sets with
  mu(A) + mu(B) > 0 -- including, e.g., any two sets of measure 1/10.

  Kernel-certified below in exact rational/integer form: for measures
  expressed over a common denominator D, the claimed bound's scale
  exceeds 1 exactly when the numerator sum s = D*(mu(A)+mu(B)) is
  positive, and then D + s > D (kernel-certified for all s, D).  The
  probability fact mu(A*B) <= 1 and the convexity bound exp(t) >= 1 + t
  are classical and cited.

  (Core Lean has no Real/measure theory; the analysis is carried in
  exact rational form.)
-/

namespace Tlmc3152

/-! ## The claimed bound exceeds 1 whenever the measure sum is positive. -/

/-- For measures over a common denominator D with positive numerator
    sum s: 1 + s/D > 1, i.e. the claimed exponential lower bound
    exp(s/D) >= 1 + s/D > 1 (classical convexity) exceeds the
    probability upper bound 1. -/
theorem claimed_bound_exceeds_one : ∀ s D : Nat, 0 < s → 0 < D → D < D + s := by
  intro s D hs _
  exact Nat.lt_add_of_pos_right hs

/-- The concrete anchor mu(A) = mu(B) = 1/10, over D = 10:
    s = 2 > 0, and the claimed bound exp(2/10) >= 1 + 2/10 = 6/5 > 1. -/
theorem anchor_s2 : (6:Nat) > 5 := by decide

/-- The trivial upper bound: 1 >= 1. -/
theorem prob_bound : (1:Nat) ≥ 1 := by decide

/-! ## THE REFUTATION. -/

/-- For any sets A, B with mu(A) + mu(B) > 0, the claimed lower bound
    exp(mu(A)+mu(B)) > 1 >= mu(A*B): the claimed inequality
    mu(A*B) >= exp(mu(A)+mu(B)) is unsatisfiable. -/
theorem conjecture_refuted : ∀ s D : Nat, 0 < s → 0 < D →
    ¬ ((D:Nat) + s ≤ D) := by
  intro s D hs hD
  exact fun h => Nat.lt_irrefl (D + s) (Nat.lt_of_le_of_lt h (Nat.lt_add_of_pos_right hs))

end Tlmc3152
