import Std

/-! Literal degree obstruction for TLMC 4374, independent of the actual
homotopy groups. No assertion about a corrected shifted-period conjecture. -/
namespace TLMC4374

def OddDegree (d : Nat) : Prop := ∃ k, d = 2 * k + 1

def MultipleOf (m d : Nat) : Prop := ∃ k, d = m * k

/-- The usual elementary definition of a prime natural number. -/
def Prime (p : Nat) : Prop := 2 ≤ p ∧ ∀ a b, a * b = p → a = 1 ∨ b = 1

theorem three_prime : Prime 3 := by
  constructor
  · decide
  · intro a b h
    by_cases ha : a = 1
    · exact Or.inl ha
    by_cases hb : b = 1
    · exact Or.inr hb
    have ha0 : a ≠ 0 := by intro hz; simp [hz] at h
    have hb0 : b ≠ 0 := by intro hz; simp [hz] at h
    have hbound := Nat.mul_le_mul (show 2 ≤ a by omega) (show 2 ≤ b by omega)
    omega

theorem three_odd : OddDegree 3 := ⟨1, rfl⟩

theorem period_three : 3 ^ 2 - 1 = (8 : Nat) := rfl

theorem eight_multiple_not_odd (d : Nat) (hm : MultipleOf 8 d) :
    ¬ OddDegree d := by
  rcases hm with ⟨j, hj⟩
  rintro ⟨k, hk⟩
  omega

/-- Even allowing the occurrence to depend on the prime cannot work at p=3. -/
theorem no_next_at_three (nonzero : Nat → Prop) (cutoff : Nat) :
    ¬ ∃ d, cutoff < d ∧ nonzero d ∧ OddDegree d ∧ MultipleOf (3^2-1) d := by
  rintro ⟨d, _, _, ho, hm⟩
  exact eight_multiple_not_odd d hm ho

/-- The weakest necessary existence-and-degree clause of the printed claim. -/
def PrintedDegreeClaim (nonzero : Nat → Prop) (cutoff : Nat) : Prop :=
  ∀ p, Prime p → OddDegree p →
    ∃ d, cutoff < d ∧ nonzero d ∧ OddDegree d ∧ MultipleOf (p^2-1) d

theorem printed_degree_claim_false (nonzero : Nat → Prop) (cutoff : Nat) :
    ¬ PrintedDegreeClaim nonzero cutoff := by
  intro h
  exact no_next_at_three nonzero cutoff (h 3 three_prime three_odd)

/-- No minimum or actual K-group computation is assumed to obtain the contradiction. -/
theorem any_stronger_claim_false (claim : Prop) (nonzero : Nat → Prop)
    (cutoff : Nat) (necessary : claim → PrintedDegreeClaim nonzero cutoff) : ¬ claim := by
  intro h
  exact printed_degree_claim_false nonzero cutoff (necessary h)

/-- A shifted-period statement would be different and has odd examples. -/
theorem shifted_period_can_be_odd (k : Nat) : OddDegree (1 + 8*k) := by
  refine ⟨4*k, ?_⟩
  omega

end TLMC4374
