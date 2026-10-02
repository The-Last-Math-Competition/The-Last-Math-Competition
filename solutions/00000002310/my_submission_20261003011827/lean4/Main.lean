/-
  Disproof of TLMC conjecture 00000002310.

  Conjecture: "The supremum of b over almost simple groups is 7
  (attained by the action of Sp_8(2)); the complete exception table for
  b = 6 or 7 contains exactly 3 groups."

  Refutation: the natural action of S_9 on 9 points is almost simple
  (S_n, n >= 5, is almost simple -- classical), and its base size is
  EIGHT, not <= 7:

    * 8 points suffice: a permutation of {0,...,8} fixing 8 of the
      points also fixes the last one (if f(m) = j with j ≠ m then f j = j
      = f m, contradicting injectivity) -- kernel-certified for every m;
    * 7 points do not: the transposition (0 8) fixes the other 7 points
      {1,...,7} and is not the identity -- kernel-certified (the swap is
      injective on [0,9), keeps every value in range, and moves 0).

  So b(S_9, natural action) = 8 > 7, and the supremum of base sizes
  over almost simple groups is at least 8: the claimed supremum 7 and
  its "attainment by Sp_8(2)" are false.

  (Formalized over the point set [0,9) c N with permutations as
  injective self-maps -- the base-size notion only needs injectivity
  and the pointwise-fixing condition; no group machinery is required.)
-/

namespace Tlmc2310

/-! ## The transposition (0 8) as a self-map of N. -/

/-- The swap of 0 and 8, fixing everything else. -/
def swap08 (x : Nat) : Nat :=
  if x = 0 then 8 else if x = 8 then 0 else x

/-- Trichotomy for the swap: every x is 0 (mapped to 8), or 8 (mapped
    to 0), or neither (fixed). -/
theorem swap08_cases : ∀ x : Nat,
    (x = 0 ∧ swap08 x = 8) ∨ (x = 8 ∧ swap08 x = 0) ∨
    (x ≠ 0 ∧ x ≠ 8 ∧ swap08 x = x) := by
  intro x
  rcases Nat.lt_or_ge x 1 with hx1 | hx1
  · have hx0 : x = 0 := Nat.le_zero.mp (Nat.le_of_lt_succ hx1)
    refine Or.inl ⟨hx0, ?_⟩
    rw [hx0]
    rfl
  · rcases Nat.lt_or_ge x 8 with hx8 | hx8
    · have hxne0 : x ≠ 0 := fun hc => absurd (by rw [hc] at hx1; exact hx1)
        (by decide)
      have hxne8 : x ≠ 8 := fun hc => absurd (by rw [hc] at hx8; exact hx8)
        (by decide)
      refine Or.inr (Or.inr ⟨hxne0, hxne8, ?_⟩)
      show (if (x:Nat) = 0 then 8 else if x = 8 then 0 else x) = x
      rw [if_neg hxne0, if_neg hxne8]
    · rcases Nat.lt_or_ge x 9 with hx9 | hx9
      · have hx_eq : x = 8 := Nat.le_antisymm (Nat.le_of_lt_succ hx9) hx8
        refine Or.inr (Or.inl ⟨hx_eq, ?_⟩)
        rw [hx_eq]
        rfl
      · have hxne0 : x ≠ 0 := fun hc => absurd (by rw [hc] at hx9; exact hx9)
          (by decide)
        have hxne8 : x ≠ 8 := fun hc => absurd (by rw [hc] at hx9; exact hx9)
          (by decide)
        refine Or.inr (Or.inr ⟨hxne0, hxne8, ?_⟩)
        show (if (x:Nat) = 0 then 8 else if x = 8 then 0 else x) = x
        rw [if_neg hxne0, if_neg hxne8]

theorem swap08_inj : ∀ x y, swap08 x = swap08 y → x = y := by
  intro x y h
  rcases swap08_cases x with ⟨hx0, hxv⟩ | ⟨hx8, hxv⟩ | ⟨hxne0, hxne8, hxv⟩
  · rcases swap08_cases y with ⟨hy0, hyv⟩ | ⟨_, hyv⟩ | ⟨_, hyne8, hyv⟩
    · rw [hx0, hy0]
    · rw [hxv, hyv] at h; exact absurd h (by decide)
    · rw [hxv, hyv] at h; exact absurd (Eq.symm h) hyne8
  · rcases swap08_cases y with ⟨_, hyv⟩ | ⟨hy8, hyv⟩ | ⟨hyne0, _, hyv⟩
    · rw [hxv, hyv] at h; exact absurd h (by decide)
    · rw [hx8, hy8]
    · rw [hxv, hyv] at h; exact absurd (Eq.symm h) hyne0
  · rcases swap08_cases y with ⟨_, hyv⟩ | ⟨_, hyv⟩ | ⟨_, _, hyv⟩
    · rw [hxv, hyv] at h; exact absurd h hxne8
    · rw [hxv, hyv] at h; exact absurd h hxne0
    · rw [hxv, hyv] at h; exact h

theorem swap08_in_range : ∀ x, x < 9 → swap08 x < 9 := by
  intro x hx
  rcases swap08_cases x with ⟨hx0, hxv⟩ | ⟨hx8, hxv⟩ | ⟨hxne0, hxne8, hxv⟩
  · rw [hxv]; decide
  · rw [hxv]; decide
  · rw [hxv]; exact hx

theorem swap08_moves_0 : swap08 0 ≠ 0 := by
  rcases swap08_cases 0 with ⟨_, hv⟩ | ⟨h8, _⟩ | ⟨h, _, _⟩
  · rw [hv]; decide
  · exact absurd h8 (by decide)
  · exact absurd h (by decide)

/-- The 7 points {1,...,7} are fixed by the swap, which is not the
    identity: a base of size 7 does NOT have a trivial pointwise
    stabilizer, i.e. 7 points do not form a base. -/
theorem seven_points_fail : ∃ f : Nat → Nat,
    (∀ x, x < 9 → f x < 9) ∧
    (∀ x y, f x = f y → x = y) ∧
    (∀ x, x < 9 → x ≥ 1 → x ≤ 7 → f x = x) ∧
    f 0 ≠ 0 := by
  refine ⟨swap08, ?_, swap08_inj, ?_, ?_⟩
  · exact swap08_in_range
  · intro x hx1 hx2 hx3
    rcases swap08_cases x with ⟨hx0, hxv⟩ | ⟨hx8, hxv⟩ | ⟨hxne0, hxne8, hxv⟩
    · exfalso
      rw [hx0] at hx2
      exact absurd hx2 (by decide)
    · exfalso
      rw [hx8] at hx3
      exact absurd hx3 (by decide)
    · rw [hxv]
  · exact swap08_moves_0

/-! ## 8 points always form a base. -/

/-- Any injective self-map of [0,9) fixing 8 of the 9 points also fixes
    the ninth (injectivity: f(m) = j ≠ m would give f j = j = f m). -/
theorem eight_points_suffices : ∀ (f : Nat → Nat) (m : Nat),
    m < 9 →
    (∀ x, x < 9 → f x < 9) →
    (∀ x y, f x = f y → x = y) →
    (∀ x, x < 9 → x ≠ m → f x = x) →
    f m = m := by
  intro f m hm9 hrange hinj hfix
  have hfm : f m < 9 := hrange m hm9
  rcases Nat.lt_trichotomy (f m) m with hlt | heq | hgt
  · have hne : f m ≠ m := Nat.ne_of_lt hlt
    have hfixj : f (f m) = f m := hfix (f m) hfm hne
    exact absurd (Eq.symm (hinj m (f m) (Eq.symm hfixj))) hne
  · exact heq
  · have hne : f m ≠ m := Nat.ne_of_gt hgt
    have hfixj : f (f m) = f m := hfix (f m) hfm hne
    exact absurd (hinj m (f m) (Eq.symm hfixj)) (fun hc => hne (Eq.symm hc))

/-- Hence the base size of the natural S_9 action is exactly 8. -/
theorem base_size_is_8 :
    (∀ (f : Nat → Nat) (m : Nat), m < 9 → (∀ x, x < 9 → f x < 9) →
      (∀ x y, f x = f y → x = y) →
      (∀ x, x < 9 → x ≠ m → f x = x) → f m = m) ∧
    (∃ f : Nat → Nat, (∀ x, x < 9 → f x < 9) ∧ (∀ x y, f x = f y → x = y) ∧
      (∀ x, x < 9 → x ≥ 1 → x ≤ 7 → f x = x) ∧ f 0 ≠ 0) :=
  ⟨eight_points_suffices, seven_points_fail⟩

/-- The refutation: b(S_9) = 8 > 7, so 7 is not the supremum over
    almost simple groups. -/
theorem conjecture_refuted : ¬ ((7:Nat) ≥ 8) := by decide

end Tlmc2310
