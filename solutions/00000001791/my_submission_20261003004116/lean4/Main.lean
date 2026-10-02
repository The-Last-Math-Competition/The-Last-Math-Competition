/-
  Disproof of TLMC conjecture 00000001791.

  Conjecture: "The union of lct values over polynomial families of
  degree <= d is a discrete layer {1/m : m = 1,...,d} U {n + 1/m}; the
  explicit layers of the jump set are given by the Sano-Nemethi Newton
  upper bound."

  Refutation at d = 3: the polynomial f(x, y) = x^2 + y^3 has (total)
  degree 3 and its log canonical threshold at the origin is the
  classical value

      lct_0(f) = 1/2 + 1/3 = 5/6,

  the weighted-homogeneous threshold of the isolated singularity
  (weights wt(x) = 3, wt(y) = 2; Saito's theorem for quasi-homogeneous
  singularities).  But 5/6 lies in NEITHER layer of the claimed set
  {1/m : m = 1,2,3} U {n + 1/m}:

    * 5/6 is not among 1, 1/2, 1/3 (kernel-certified below in the
      cross-multiplication form 5*m <> 6, valid for positive
      denominators);
    * 5/6 is not n + 1/m for any n >= 0 and m in {1,2,3}: for n = 0 this
      is the previous point; for n >= 1, n + 1/m > 5/6, certified in
      the positive-integer cross-multiplication form
          5*m < 6*n*m + 6   (kernel-certified, all n >= 1, m = 1,2,3),
      i.e. by the standard equivalence for positive denominators
          a/b <> c/d  <=>  a*d <> c*b   (a, c >= 0; b, d > 0).

  So the degree-3 family already produces an lct value outside the
  claimed discrete layer, and the claimed characterization of the jump
  set is false.
-/

namespace Tlmc1791

/-! ## Layer 1: 5/6 is not among 1/m for m = 1, 2, 3. -/

/-- Cross-multiplied: 5m <> 6 for m in {1,2,3}, so 5/6 <> 1/m. -/
theorem recip_ne : ∀ m : Nat, (m = 1 ∨ m = 2 ∨ m = 3) → 5 * m ≠ 6 := by
  intro m hm
  rcases hm with h | h | h
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide

/-! ## Layer 2: 5/6 is not n + 1/m. -/

/-- For n >= 1 and m in {1,2,3}: 5m < 6nm + 6, i.e. 5/6 < n + 1/m in
    cross-multiplied form. -/
theorem shift_gt : ∀ n : Nat, ∀ m : Nat,
    (m = 1 ∨ m = 2 ∨ m = 3) → 1 ≤ n → 5 * m < 6 * n * m + 6 := by
  intro n m hm hn
  have hpos : ∀ j : Nat, j = 1 ∨ j = 2 ∨ j = 3 → (0:Nat) < j := by
    intro j hj
    rcases hj with h | h | h
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
  have h6n : (6:Nat) ≤ 6 * n := Nat.le_mul_of_pos_right 6 hn
  have h6 : 6 * m ≤ 6 * n * m := Nat.mul_le_mul_right m h6n
  have h56 : (5:Nat) ≤ 6 := by decide
  have h5m6m : 5 * m ≤ 6 * m := Nat.mul_le_mul h56 (Nat.le_refl m)
  have hstep1a : (5:Nat) * m < 5 * m + 6 :=
    Nat.lt_add_of_pos_right (k := 6) (by decide)
  have hstep1b : 5 * m + 6 ≤ 6 * m + 6 := Nat.add_le_add_right h5m6m 6
  have hstep1 : (5:Nat) * m < 6 * m + 6 :=
    Nat.lt_of_lt_of_le hstep1a hstep1b
  have hstep2 : 6 * m + 6 ≤ 6 * n * m + 6 := Nat.add_le_add_right h6 6
  exact Nat.lt_of_lt_of_le hstep1 hstep2

/-- Hence 5/6 <> n + 1/m for every n >= 1 and m in {1,2,3} (the strict
    cross-multiplied inequality precludes equality). -/
theorem shift_ne : ∀ n : Nat, ∀ m : Nat,
    (m = 1 ∨ m = 2 ∨ m = 3) → 1 ≤ n → 6 * n * m + 6 ≠ 5 * m := by
  intro n m hm hn
  have := shift_gt n m hm hn
  exact Nat.ne_of_gt this

/-! ## The refutation. -/

/-- 5/6 is outside both layers: the degree-3 jump value 5/6 = 1/2 + 1/3
    (lct of x^2 + y^3) is not in {1/m : m = 1,2,3} U {n + 1/m}. -/
theorem lct_56_outside :
    (∀ m : Nat, (m = 1 ∨ m = 2 ∨ m = 3) → 5 * m ≠ 6) ∧
    (∀ n : Nat, ∀ m : Nat, (m = 1 ∨ m = 2 ∨ m = 3) → 1 ≤ n →
      6 * n * m + 6 ≠ 5 * m) :=
  ⟨recip_ne, shift_ne⟩

end Tlmc1791
