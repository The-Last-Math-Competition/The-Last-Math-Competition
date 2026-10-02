/-
  Disproof of TLMC conjecture 00000001543.

  Conjecture: "Any n points on an irreducible real algebraic curve
  determine at least c * n^(4/3) distinct distances (the curve distance
  exponent)" -- for some absolute constant c > 0.

  Refutation: a LINE is an irreducible real algebraic curve, and n
  equally spaced points on a line determine exactly n - 1 distinct
  distances (positions 1, ..., n give distances 1, ..., n-1 --
  classical).  So the claimed constant would have to satisfy
      n - 1 >= c * n^(4/3)   for EVERY n,
  i.e. (with c = 1/C, C a positive integer) C^3 * (n-1)^3 >= n^4 for
  every n.  Kernel-certified below:

    * the ratio fact: (n-1)^3 < n^3 < n^4 for every n >= 2 (fully
      general in n);
    * THE REFUTATION, fully general in the constant: for every C >= 1
      there is n >= 2 -- namely n = 2*C^3 -- with
          C^3 * (n-1)^3 < n^4,
      so the claimed lower bound fails at n = 2*C^3 for every
      reciprocal-integer constant 1/C, hence (taking C with 1/C <= c,
      standard) for every real c > 0.

  (The core strict-monotonicity lemmas for multiplication carry
  `Classical.choice` upstream, so the needed strict product lemmas are
  rebuilt here by induction, axiom-free.)
-/

namespace Tlmc1543

/-! ## Strict multiplication monotonicity, rebuilt. -/

/-- Right strict product monotonicity, by induction on the upper end. -/
theorem mul_lt_mul_right_self {k : Nat} (hk : 0 < k) :
    ∀ n m, n < m → n * k < m * k := by
  intro n m
  induction m with
  | zero => intro h; exact absurd h (Nat.not_lt_zero n)
  | succ m' ih =>
      intro h
      rw [Nat.succ_mul]
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
      · -- n < m' < m'+1
        have h1 : n * k < m' * k := ih h'
        have h2 : m' * k < m' * k + k := Nat.lt_add_of_pos_right (n := m' * k) hk
        exact Nat.lt_trans h1 h2
      · -- n = m'
        rw [h']
        exact Nat.lt_add_of_pos_right (n := m' * k) hk

/-- Left strict product monotonicity. -/
theorem mul_lt_mul_left_self {k : Nat} (hk : 0 < k) :
    ∀ n m, n < m → k * n < k * m := by
  intro n m
  induction m with
  | zero => intro h; exact absurd h (Nat.not_lt_zero n)
  | succ m' ih =>
      intro h
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
      · have h1 : k * n < k * m' := ih h'
        have h2 : k * m' < k * m' + k :=
          Nat.lt_add_of_pos_right (n := k * m') hk
        exact Nat.lt_trans h1 h2
      · rw [h']
        exact Nat.lt_add_of_pos_right (n := k * m') hk

/-- 1 * a = a, by induction (needed before pow_two). -/
theorem one_mul_self (a : Nat) : 1 * a = a := by
  induction a with
  | zero => rfl
  | succ a ih => show (1 * a) + 1 = a + 1; rw [ih]

/-- a^2 = a * a, by induction. -/
theorem pow_two_self (a : Nat) : a ^ 2 = a * a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    show (1 * (Nat.succ a)) * (Nat.succ a) = Nat.succ a * Nat.succ a
    rw [one_mul_self]

/-! ## Cubic monotonicity. -/

/-- a^3 < b^3 for 1 <= a < b. -/
theorem pow3_lt {a b : Nat} (ha : 1 ≤ a) (h : a < b) : a ^ 3 < b ^ 3 := by
  have hapos : 0 < a := by
    cases a with
    | zero => exact absurd ha (by decide)
    | succ _ => exact Nat.succ_pos _
  have hab : a ≤ b := Nat.le_of_lt h
  have h1 : a ^ 3 = a ^ 2 * a := rfl
  have h2 : a ^ 2 * a < a ^ 2 * b := by
    rw [pow_two_self a]
    exact mul_lt_mul_left_self (Nat.mul_pos hapos hapos) a b h
  have h3 : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hab 2
  have h4 : a ^ 2 * b ≤ b ^ 2 * b := Nat.mul_le_mul_right b h3
  show a ^ 2 * a < b ^ 2 * b
  exact Nat.lt_of_lt_of_le h2 h4

/-! ## The ratio fact and THE REFUTATION. -/

/-- For every n >= 2: (n-1)^3 < n^3 < n^4. -/
theorem ratio_lt : ∀ n : Nat, 2 ≤ n → (n - 1) ^ 3 < n ^ 4 := by
  intro n hn
  have hnm1 : (1:Nat) ≤ n - 1 := by
    cases n with
    | zero => exact absurd hn (by decide)
    | succ n' => cases n' with
      | zero => exact absurd hn (by decide)
      | succ _ => exact Nat.le_of_succ_le_succ hn
  have h1 : (n - 1) ^ 3 < n ^ 3 := pow3_lt hnm1 (Nat.sub_lt (Nat.lt_of_lt_of_le (by decide) hn) (by decide))
  refine Nat.lt_trans h1 ?_
  have h2 : n ^ 3 * 1 < n ^ 3 * n :=
    mul_lt_mul_left_self (Nat.pow_pos (Nat.lt_of_lt_of_le (by decide) hn))
      1 n (Nat.lt_of_lt_of_le (by decide) hn)
  rw [Nat.mul_one] at h2
  show n ^ 3 < n ^ 3 * n
  exact h2

/-- THE REFUTATION: for every candidate constant 1/C (C >= 1) there is
    n >= 2 -- take n = 2*C^3 -- with C^3 * (n-1)^3 < n^4, i.e. the
    collinear configuration's n-1 distances fall below
    (1/C) * n^(4/3) at that n. -/
theorem no_constant : ∀ C : Nat, 1 ≤ C →
    ∃ n, 2 ≤ n ∧ C ^ 3 * (n - 1) ^ 3 < n ^ 4 := by
  intro C hC
  have hCpos : (0:Nat) < C := by
    cases C with
    | zero => exact absurd hC (by decide)
    | succ _ => exact Nat.succ_pos _
  refine ⟨2 * C ^ 3, Nat.le_mul_of_pos_right 2 (Nat.pow_pos hCpos), ?_⟩
  -- n = 2*C^3 >= 2, so n - 1 >= 1 and (n-1)^3 < n^3
  have hn1 : (1:Nat) ≤ 2 * C ^ 3 - 1 :=
    Nat.sub_le_sub_right
      (Nat.le_mul_of_pos_right 2 (Nat.pow_pos hCpos)) 1
  have hlt1 : (2 * C ^ 3 - 1) ^ 3 < (2 * C ^ 3) ^ 3 :=
    pow3_lt hn1 (Nat.sub_lt (n := 2 * C ^ 3) (m := 1) (Nat.mul_pos (by decide) (Nat.pow_pos hCpos)) (by decide))
  have hlt2 : C ^ 3 * (2 * C ^ 3 - 1) ^ 3 < C ^ 3 * (2 * C ^ 3) ^ 3 :=
    mul_lt_mul_left_self (Nat.pow_pos hCpos) ((2 * C ^ 3 - 1) ^ 3) ((2 * C ^ 3) ^ 3) hlt1
  -- C^3 < 2*C^3 = n:
  have h2le : (2:Nat) ≤ 2 * C ^ 3 :=
    Nat.le_mul_of_pos_right 2 (Nat.pow_pos hCpos)
  have honestep : (1:Nat) * C ^ 3 < 2 * C ^ 3 :=
    mul_lt_mul_right_self (Nat.pow_pos hCpos) 1 2 (by decide)
  have hC3n : C ^ 3 < 2 * C ^ 3 := by
    rw [Nat.one_mul] at honestep
    exact honestep
  have hlt3 : (2 * C ^ 3) ^ 3 * C ^ 3 < (2 * C ^ 3) ^ 3 * (2 * C ^ 3) :=
    mul_lt_mul_left_self
      (Nat.pow_pos (Nat.mul_pos (by decide) (Nat.pow_pos hCpos))) (C ^ 3)
      (2 * C ^ 3) hC3n
  rw [Nat.mul_comm (C ^ 3) ((2 * C ^ 3) ^ 3)] at hlt2
  exact Nat.lt_trans hlt2 hlt3

end Tlmc1543
