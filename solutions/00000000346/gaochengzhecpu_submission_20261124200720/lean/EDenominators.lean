import Std

namespace C346

/-- The partial quotients in Euler's continued fraction for `e`, starting at index zero. -/
def partialQuotient : Nat → Nat
  | 0 => 2
  | n + 1 => if n % 3 = 1 then 2 * ((n + 2) / 3) else 1

theorem partialQuotient_block (k : Nat) :
    partialQuotient (3 * k + 1) = 1 ∧
    partialQuotient (3 * k + 2) = 2 * (k + 1) ∧
    partialQuotient (3 * k + 3) = 1 := by
  change (if (3 * k) % 3 = 1 then 2 * ((3 * k + 2) / 3) else 1) = 1 ∧
    (if (3 * k + 1) % 3 = 1 then 2 * ((3 * k + 3) / 3) else 1) = 2 * (k + 1) ∧
    (if (3 * k + 2) % 3 = 1 then 2 * ((3 * k + 4) / 3) else 1) = 1
  constructor
  · rw [if_neg (by omega)]
  constructor
  · rw [if_pos (by omega)]
    omega
  · rw [if_neg (by omega)]

private theorem partialQuotient_pos (n : Nat) : 0 < partialQuotient (n + 1) := by
  change 0 < (if n % 3 = 1 then 2 * ((n + 2) / 3) else 1)
  split <;> omega

private theorem partialQuotient_le (n : Nat) : partialQuotient (n + 1) ≤ n + 1 := by
  change (if n % 3 = 1 then 2 * ((n + 2) / 3) else 1) ≤ n + 1
  split <;> omega

/-- The two components at index `n` are `q_n` and `q_(n-1)`. -/
def denominatorPair : Nat → Nat × Nat
  | 0 => (1, 0)
  | n + 1 =>
    let last := denominatorPair n
    (partialQuotient (n + 1) * last.1 + last.2, last.1)

def denominator (n : Nat) : Nat := (denominatorPair n).1

private theorem denominator_step (n : Nat) :
    denominator (n + 1) =
      partialQuotient (n + 1) * denominator n + (denominatorPair n).2 := rfl

private theorem denominator_previous (n : Nat) :
    (denominatorPair (n + 1)).2 = denominator n := rfl

private theorem denominator_le_succ (n : Nat) : denominator n ≤ denominator (n + 1) := by
  rw [denominator_step]
  have h : 1 ≤ partialQuotient (n + 1) := partialQuotient_pos n
  have hmul : denominator n ≤ partialQuotient (n + 1) * denominator n := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (denominator n) h
  exact Nat.le_trans hmul (Nat.le_add_right _ _)

private theorem denominator_mono {i j : Nat} (h : i ≤ j) : denominator i ≤ denominator j := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step j _ ih => exact Nat.le_trans ih (denominator_le_succ j)

private theorem denominator_pos (n : Nat) : 0 < denominator n :=
  denominator_mono (Nat.zero_le n)

private theorem denominator_succ_le (n : Nat) :
    denominator (n + 1) ≤ (n + 2) * denominator n := by
  have hprev : (denominatorPair n).2 ≤ denominator n := by
    cases n with
    | zero => decide
    | succ n =>
      rw [denominator_previous]
      exact denominator_le_succ n
  change denominator (n + 1) ≤ (n + 1 + 1) * denominator n
  rw [denominator_step, Nat.add_mul (n + 1) 1, Nat.one_mul]
  exact Nat.add_le_add (Nat.mul_le_mul_right _ (partialQuotient_le n)) hprev

private theorem denominator_two_step (n : Nat) : 2 * denominator n ≤ denominator (n + 2) := by
  change 2 * denominator n ≤ denominator (n + 1 + 1)
  rw [denominator_step (n + 1), denominator_previous n]
  have h : 1 ≤ partialQuotient (n + 1 + 1) := partialQuotient_pos (n + 1)
  have hmul : denominator (n + 1) ≤ partialQuotient (n + 1 + 1) * denominator (n + 1) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (denominator (n + 1)) h
  have hlo := Nat.le_trans (denominator_le_succ n) hmul
  omega

private theorem denominator_even_lower (s : Nat) : 2 ^ s ≤ denominator (2 * s) := by
  induction s with
  | zero => decide
  | succ s ih =>
    calc
      2 ^ (s + 1) = 2 * 2 ^ s := by rw [Nat.pow_succ, Nat.mul_comm]
      _ ≤ 2 * denominator (2 * s) := Nat.mul_le_mul_left 2 ih
      _ ≤ denominator (2 * (s + 1)) := by
        rw [Nat.mul_succ]
        exact denominator_two_step (2 * s)

private theorem succ_le_two_pow (s : Nat) : s + 1 ≤ 2 ^ s := by
  induction s with
  | zero => decide
  | succ s ih =>
    rw [Nat.pow_succ]
    omega

/-- After raising to the positive integer power `r`, the comparison
`q_(n+1) / q_n^(1+1/r) < 1/B` is exactly this integer inequality. -/
theorem eventual_rational_bounds (r B : Nat) (hr : 0 < r) :
    ∃ N, ∀ n, N ≤ n → (B * denominator (n + 1)) ^ r < denominator n ^ (r + 1) := by
  let d := 4 * r
  let threshold := B * (d + 2)
  refine ⟨threshold * d, ?_⟩
  intro n hn
  let s := n / d
  have hd : 0 < d := by dsimp [d]; omega
  have hs : threshold ≤ s := (Nat.le_div_iff_mul_le hd).mpr hn
  have hlo : s * d ≤ n := Nat.div_mul_le_self n d
  have hhi : n < (s + 1) * d := (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self s)
  have hlinear : n + 2 ≤ (d + 2) * (s + 1) := by
    rw [Nat.add_mul, Nat.mul_comm d]
    have hsmall : 2 ≤ 2 * (s + 1) := by omega
    omega
  have hfactor : B * (n + 2) < (s + 1) ^ 2 := by
    calc
      B * (n + 2) ≤ B * ((d + 2) * (s + 1)) := Nat.mul_le_mul_left B hlinear
      _ = threshold * (s + 1) := by rw [← Nat.mul_assoc]
      _ < (s + 1) * (s + 1) :=
        Nat.mul_lt_mul_of_pos_right (by omega) (Nat.succ_pos s)
      _ = (s + 1) ^ 2 := by rw [Nat.pow_succ, Nat.pow_one]
  have hindex : 2 * (s * 2 * r) ≤ n := by
    calc
      2 * (s * 2 * r) = s * d := by
        change 2 * (s * 2 * r) = s * ((2 * 2) * r)
        ac_rfl
      _ ≤ n := hlo
  have hexp : ((2 ^ s) ^ 2) ^ r ≤ denominator n := by
    rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.mul_assoc]
    exact Nat.le_trans (denominator_even_lower (s * 2 * r)) (denominator_mono hindex)
  have hfactor_pow : (B * (n + 2)) ^ r < denominator n := by
    calc
      (B * (n + 2)) ^ r < ((s + 1) ^ 2) ^ r := Nat.pow_lt_pow_left hfactor (by omega)
      _ ≤ ((2 ^ s) ^ 2) ^ r := Nat.pow_le_pow_left (Nat.pow_le_pow_left (succ_le_two_pow s) 2) r
      _ ≤ denominator n := hexp
  calc
    (B * denominator (n + 1)) ^ r ≤ (B * ((n + 2) * denominator n)) ^ r :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_left B (denominator_succ_le n)) r
    _ = (B * (n + 2)) ^ r * denominator n ^ r := by rw [← Nat.mul_assoc, Nat.mul_pow]
    _ < denominator n * denominator n ^ r :=
      Nat.mul_lt_mul_of_pos_right hfactor_pow (Nat.pow_pos (denominator_pos n))
    _ = denominator n ^ (r + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

#print axioms eventual_rational_bounds

end C346
