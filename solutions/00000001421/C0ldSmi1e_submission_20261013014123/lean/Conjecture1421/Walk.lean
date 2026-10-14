import Conjecture1421.Basic

/-! Structural properties of the actual unweighted Cayley random walk. -/
noncomputable section
open scoped BigOperators
namespace Conjecture1421

lemma mem_support_iff (n : ℕ) (g : State n) :
    g ∈ support n ↔ (g.1 = 0 ∧ g.2 ≠ 0) ∨ (g.1 = 1 ∧ g.2 = 0) := by
  simp [support]

lemma zero_not_mem_support (n : ℕ) : (0 : State n) ∉ support n := by
  simp [mem_support_iff]

lemma support_symmetric (n : ℕ) (g : State n) : -g ∈ support n ↔ g ∈ support n := by
  rcases g with ⟨a, b⟩
  fin_cases a <;> simp [mem_support_iff]

lemma support_eq (n : ℕ) : support n =
    ({0} : Finset (ZMod 2)) ×ˢ (Finset.univ.erase (0 : Second n)) ∪ {(1, 0)} := by
  ext ⟨a, b⟩
  simp [mem_support_iff]
  aesop

lemma support_card (n : ℕ) : (support n).card = n + 4 := by
  rw [support_eq, Finset.card_union_of_disjoint (by simp)]
  simp

lemma support_generates (n : ℕ) : AddSubgroup.closure (support n : Set (State n)) = ⊤ := by
  apply top_unique
  rintro ⟨a, b⟩ _
  have h0b : (0, b) ∈ AddSubgroup.closure (support n : Set (State n)) := by
    by_cases hb : b = 0
    · subst b
      exact (AddSubgroup.closure _).zero_mem
    · exact AddSubgroup.subset_closure (by simp [mem_support_iff, hb])
  have ha0 : (a, 0) ∈ AddSubgroup.closure (support n : Set (State n)) := by
    fin_cases a
    · exact (AddSubgroup.closure _).zero_mem
    · exact AddSubgroup.subset_closure (by simp [mem_support_iff])
  simpa using (AddSubgroup.closure (support n : Set (State n))).add_mem ha0 h0b

lemma jumpLaw_uniform (n : ℕ) (g : State n) :
    jumpLaw n g = (if g = 0 then (1 / 2 : ℝ) else 0) +
      if g ∈ support n then 1 / (2 * ((support n).card : ℝ)) else 0 := by
  rcases g with ⟨a, b⟩
  fin_cases a <;> by_cases hb : b = 0 <;>
    simp [jumpLaw, mem_support_iff, hb, support_card, size, Prod.ext_iff]

lemma transition_uniform (n : ℕ) (x y : State n) :
    transition n x y = (if x = y then (1 / 2 : ℝ) else 0) +
      if y - x ∈ support n then 1 / (2 * ((support n).card : ℝ)) else 0 := by
  rw [transition, jumpLaw_uniform]
  simp [sub_eq_zero, eq_comm]

lemma transition_symmetric (n : ℕ) (x y : State n) : transition n x y = transition n y x := by
  simp [transition_apply, eq_comm]

lemma transition_diagonal (n : ℕ) (x : State n) : transition n x x = 1 / 2 := by
  simp [transition_apply]

lemma transition_nonneg (n : ℕ) (x y : State n) : 0 ≤ transition n x y := by
  have := size_pos n
  rw [transition_apply]
  split_ifs <;> positivity

lemma transition_decomposition (n : ℕ) (x y : State n) :
    transition n x y = s n * (if x = y then 1 else 0) +
      (1 / (2 * size n)) * (if x.1 = y.1 then 1 else 0) +
      (1 / (2 * size n)) * (if x.2 = y.2 then 1 else 0) := by
  rw [transition_apply]
  by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2
  all_goals simp [h1, h2, Prod.ext_iff, s]
  field_simp
  ring

lemma transition_row_sum (n : ℕ) (x : State n) : ∑ y, transition n x y = 1 := by
  have hfirst : (∑ y : State n, if x.1 = y.1 then (1 : ℝ) else 0) = size n := by
    rw [Fintype.sum_prod_type]
    simp [size, eq_comm]
  have hsecond : (∑ y : State n, if x.2 = y.2 then (1 : ℝ) else 0) = 2 := by
    rw [Fintype.sum_prod_type]
    simp [eq_comm]
  have hdiag : (∑ y : State n, if x = y then (1 : ℝ) else 0) = 1 := by simp [eq_comm]
  simp_rw [transition_decomposition]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hdiag, hfirst, hsecond]
  have hn := size_ne_zero n
  dsimp [s]
  field_simp
  ring

lemma transition_doublyStochastic (n : ℕ) : transition n ∈ doublyStochastic ℝ (State n) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨transition_nonneg n, transition_row_sum n, ?_⟩
  intro y
  simp_rw [transition_symmetric n _ y]
  exact transition_row_sum n y

lemma uniform_stationary (n : ℕ) (y : State n) :
    ∑ x, (1 / (2 * size n)) * transition n x y = 1 / (2 * size n) := by
  rw [← Finset.mul_sum, sum_col_of_mem_doublyStochastic (transition_doublyStochastic n), mul_one]

lemma transition_pow_doublyStochastic (n t : ℕ) :
    transition n ^ t ∈ doublyStochastic ℝ (State n) :=
  (doublyStochastic ℝ (State n)).pow_mem (transition_doublyStochastic n) t

lemma uniform_mass_one (n : ℕ) :
    (∑ _x : State n, (1 / (2 * size n) : ℝ)) = 1 := by
  simp only [Finset.sum_const, Finset.card_univ, state_card, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_ofNat]
  change (2 * size n) * (1 / (2 * size n)) = 1
  field_simp [size_ne_zero n]

lemma uniform_nonneg (n : ℕ) : (0 : ℝ) ≤ 1 / (2 * size n) := by
  have := size_pos n
  positivity

lemma transition_pos_same_first (n : ℕ) (x y : State n) (h : x.1 = y.1) :
    0 < transition n x y := by
  have := size_pos n
  rw [transition_apply, if_pos h]
  split_ifs <;> positivity

lemma transition_pos_same_second (n : ℕ) (x y : State n) (h : x.2 = y.2) :
    0 < transition n x y := by
  have := size_pos n
  rw [transition_apply]
  split_ifs <;> simp_all

lemma transition_sq_pos (n : ℕ) (x y : State n) : 0 < (transition n ^ 2) x y := by
  rw [pow_two, Matrix.mul_apply]
  let z : State n := (x.1, y.2)
  have hz : 0 < transition n x z * transition n z y :=
    mul_pos (transition_pos_same_first n x z rfl) (transition_pos_same_second n z y rfl)
  exact lt_of_lt_of_le hz (Finset.single_le_sum
    (fun b _ => mul_nonneg (transition_nonneg n x b) (transition_nonneg n b y))
    (Finset.mem_univ z))

end Conjecture1421
