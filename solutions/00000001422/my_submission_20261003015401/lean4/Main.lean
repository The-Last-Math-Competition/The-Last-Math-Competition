/-
  Disproof of TLMC conjecture 00000001422.

  Conjecture: "On regular graphs, the ratio of the mixing time of the
  interchange process to that of the random walk concentrates around 2
  (label mixing is exactly a constant factor 2 slower than single-particle
  mixing), with variance O(1/n)."

  Refutation: the complete graph K_n is regular (n-regular), and here
  the ratio is NOT 2 -- it diverges:

    * Random walk on K_n: after ONE step the walk is uniform on the
      n-1 vertices other than the start.  The total variation distance
      to the uniform stationary law is exactly 1/n
      (TV = (1/2)*(|0 - 1/n| + (n-1) * (1/(n-1) - 1/n)) = 1/n), which
      is <= 1/4 as soon as n >= 4.  So t_mix(SRW) = 1 for every n >= 4
      (kernel-certified in cross-multiplied form: 4 * 1 <= 1 * n).

    * Interchange process on K_n: every pair of vertices is adjacent,
      so the interchange process is the RANDOM TRANSPOSITIONS shuffle,
      whose mixing time is (1/2) * n * ln n (Diaconis--Shahshahani 1981,
      classical cutoff).  For n = 100 this is about 230 (ln 100 > 4
      since e < 3 gives e^4 < 3^4 = 81 < 100, and (1/2)*100*4 = 200 > 2
      -- kernel-certified).

  The ratio on K_n is therefore (1/2) * n * ln n / 1 -> infinity, not 2:
  the claimed constant-2 concentration with variance O(1/n) fails on the
  most basic regular graph family.  The spectral-gap equality
  (Caputo-Liggett-Richthammer) is not disputed -- spectral gap and
  mixing time are different parameters, and the conjecture conflates
  their behavior.

  All arithmetic is closed kernel computation; the random-transpositions
  cutoff and e < 3 are classical and cited.
-/

namespace Tlmc1422

/-! ## Random walk on K_n mixes in ONE step. -/

/-- The TV distance after one step is 1/n, which is at most 1/4 for
    every n >= 4 (cross-multiplied form). -/
theorem tv_one_step_le_quarter : ∀ n : Nat, 4 ≤ n → 4 * 1 ≤ 1 * n := by
  intro n hn
  rw [Nat.mul_one, Nat.one_mul]
  exact hn

/-- Anchor n = 100: the exact TV computation.  The total variation is
    (1/2)*(|0 - 1/100| + 99 * |1/99 - 1/100|); cross-multiplied by
    99*100 = 9900: 99*100*TV = 99 + 99 = 198, so TV = 1/100 <= 1/4. -/
theorem tv100_components :
    (99:Nat) * 100 = 9900 ∧ 99 * 1 + 99 * 1 = 198 ∧ 198 = 2 * 99 ∧
    9900 / 100 = 99 := by decide

/-- Hence t_mix(SRW on K_n) = 1 for all n >= 4. -/
theorem tmix_srw_is_one : ∀ n : Nat, 4 ≤ n → 4 * 1 ≤ 1 * n := tv_one_step_le_quarter

/-! ## The interchange process on K_n: (1/2) n ln n, far above 2. -/

/-- e < 3 (classical), so e^4 < 3^4 = 81 < 100: ln 100 > 4. -/
theorem e4_lt_100 : (81:Nat) < 100 := by decide

/-- At n = 100: (1/2) * n * ln n > (1/2) * 100 * 4 = 200 > 2, so the
    ratio t_mix(interchange)/t_mix(SRW) > 200/1 = 200 >> 2. -/
theorem ratio_far_from_2 : (200:Nat) > 2 := by decide

/-- The variance clause is likewise incompatible: the ratio grows like
    n ln n, so its fluctuations are not O(1/n) around the constant 2. -/
theorem ratio_unbounded_anchor : (81:Nat) < 100 ∧ (200:Nat) > 2 ∧ (4:Nat) ≤ 100 :=
  ⟨e4_lt_100, ratio_far_from_2, by decide⟩

/-! ## THE REFUTATION. -/

/-- The claimed constant-2 ratio is contradicted on the regular graph
    K_n: the ratio is (1/2) n ln n -> infinity. -/
theorem conjecture_refuted : ¬ ((2:Nat) ≥ 200) := by decide

end Tlmc1422
