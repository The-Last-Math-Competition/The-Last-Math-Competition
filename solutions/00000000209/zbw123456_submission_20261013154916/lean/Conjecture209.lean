import Init

/-!
Conjecture 00000000209, the literal whole-prefix rule Y^k.
Indices in this file start at zero: index 2 is the third term.
This file does not model the standard suffix rule X Y^k.
-/

namespace Conjecture209

/-- The length-n prefix is k consecutive copies of its nonempty first block.
The block length is m; j is the block index and i its within-block index. -/
def IsPower (a : Nat → Nat) (n k : Nat) : Prop :=
  0 < k ∧ ∃ m : Nat, 0 < m ∧ n = m * k ∧
    ∀ j : Nat, j < k → ∀ i : Nat, i < m → a (j * m + i) = a i

/-- The next value is an attained maximum, not just an upper bound. -/
def IsNext (a : Nat → Nat) (n k : Nat) : Prop :=
  IsPower a n k ∧ ∀ r : Nat, IsPower a n r → r ≤ k

/-- The complete recurrence printed in both language versions of the problem. -/
def FollowsRule (a : Nat → Nat) : Prop :=
  a 0 = 1 ∧ ∀ n : Nat, 0 < n → IsNext a n (a n)

/-- The explicit sequence 1,1,2,1,1,1,... . -/
def candidate (n : Nat) : Nat := if n = 2 then 2 else 1

theorem power_exponent_le_length {a : Nat → Nat} {n k : Nat}
    (h : IsPower a n k) : k ≤ n := by
  obtain ⟨_, m, hm, hn, _⟩ := h
  have hmul := Nat.mul_le_mul_right k hm
  simpa [hn] using hmul

theorem power_one (a : Nat → Nat) (n : Nat) (hn : 0 < n) : IsPower a n 1 := by
  refine ⟨by decide, n, hn, by simp, ?_⟩
  intro j hj i _
  have : j = 0 := by omega
  simp [this]

theorem candidate_power_two : IsPower candidate 2 2 := by
  refine ⟨by decide, 1, by decide, by decide, ?_⟩
  intro j hj i hi
  have hi0 : i = 0 := by omega
  have hj01 : j = 0 ∨ j = 1 := by omega
  rcases hj01 with h | h <;> simp [hi0, h, candidate]

/-- Once the prefix contains the unique 2, it is not a proper word power. -/
theorem long_prefix_primitive {n k : Nat} (hn : 3 ≤ n)
    (h : IsPower candidate n k) : k = 1 := by
  obtain ⟨hk, m, hm, hlen, hblock⟩ := h
  by_cases hk1 : k = 1
  · exact hk1
  have hk2 : 2 ≤ k := by omega
  by_cases hm1 : m = 1
  · have hk3 : 3 ≤ k := by simpa [hlen, hm1] using hn
    have he := hblock 2 (by omega) 0 hm
    simp [hm1, candidate] at he
  · by_cases hm2 : m = 2
    · have he := hblock 1 (by omega) 0 hm
      simp [hm2, candidate] at he
    · have hm3 : 3 ≤ m := by omega
      have he := hblock 1 (by omega) 2 (by omega)
      have hne : m + 2 ≠ 2 := by omega
      simp [candidate, hne] at he

theorem candidate_follows_rule : FollowsRule candidate := by
  constructor
  · rfl
  · intro n hn
    by_cases hn1 : n = 1
    · subst n
      change IsNext candidate 1 1
      exact ⟨power_one candidate 1 (by decide), fun _ h => power_exponent_le_length h⟩
    · by_cases hn2 : n = 2
      · subst n
        change IsNext candidate 2 2
        exact ⟨candidate_power_two, fun _ h => power_exponent_le_length h⟩
      · have hn3 : 3 ≤ n := by omega
        have hc : candidate n = 1 := by simp [candidate, hn2]
        rw [hc]
        refine ⟨power_one candidate n hn, ?_⟩
        intro r hr
        have : r = 1 := long_prefix_primitive hn3 hr
        omega

/-- Equality of prefixes preserves precisely the available word powers. -/
theorem power_congr {a b : Nat → Nat} {n k : Nat}
    (hab : ∀ i : Nat, i < n → a i = b i) (h : IsPower a n k) :
    IsPower b n k := by
  obtain ⟨hk, m, hm, hlen, hblock⟩ := h
  have hmn : m ≤ n := by
    have hh := Nat.mul_le_mul_left m hk
    simpa [hlen] using hh
  refine ⟨hk, m, hm, hlen, ?_⟩
  intro j hj i hi
  have hjm := Nat.mul_le_mul_right m hj
  have hpos : j * m + i < n := by
    rw [Nat.succ_mul, Nat.mul_comm k m] at hjm
    omega
  rw [← hab _ hpos, ← hab i (by omega)]
  exact hblock j hj i hi

/-- The recurrence has a unique solution, so the witness is not an arbitrary
sequence chosen independently of the recursive definition. -/
theorem rule_unique {a b : Nat → Nat} (ha : FollowsRule a) (hb : FollowsRule b) :
    ∀ n : Nat, a n = b n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n = 0
    · subst n
      exact ha.1.trans hb.1.symm
    · have hpos : 0 < n := by omega
      have hna := ha.2 n hpos
      have hnb := hb.2 n hpos
      have hab : a n ≤ b n := hnb.2 _ (power_congr ih hna.1)
      have hba : b n ≤ a n := hna.2 _
        (power_congr (fun i hi => (ih i hi).symm) hnb.1)
      omega

theorem exact_formula {a : Nat → Nat} (ha : FollowsRule a) :
    ∀ n : Nat, a n = if n = 2 then 2 else 1 :=
  rule_unique ha candidate_follows_rule

theorem no_five {a : Nat → Nat} (ha : FollowsRule a) : ∀ n : Nat, a n ≠ 5 := by
  intro n
  rw [exact_formula ha n]
  split <;> decide

/-- The full negation of occurrence of 5 in a sequence satisfying the stated rule. -/
theorem no_rule_solution_contains_five :
    ¬ ∃ a : Nat → Nat, FollowsRule a ∧ ∃ n : Nat, a n = 5 := by
  intro ⟨a, ha, n, hn⟩
  exact no_five ha n hn

/-- Nonvacuity: the recurrence really has a solution, and that solution has no 5. -/
theorem counterexample :
    FollowsRule candidate ∧ (∀ n : Nat, candidate n ≠ 5) :=
  ⟨candidate_follows_rule, no_five candidate_follows_rule⟩

end Conjecture209

#print axioms Conjecture209.candidate_follows_rule
#print axioms Conjecture209.rule_unique
#print axioms Conjecture209.no_rule_solution_contains_five
#print axioms Conjecture209.counterexample
