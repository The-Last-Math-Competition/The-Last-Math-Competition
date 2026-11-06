import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace TLMC79

open Filter Topology

noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

theorem nthPrime_prime (n : ℕ) : (nthPrime n).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n

theorem nthPrime_strictMono : StrictMono nthPrime :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

theorem nthPrime_zero : nthPrime 0 = 2 := Nat.nth_prime_zero_eq_two

noncomputable def alpha : ℝ := Real.sqrt 2

theorem alpha_irrational : Irrational alpha := irrational_sqrt_two

noncomputable def primePoint (a : ℝ) (n : ℕ) : ℝ :=
  Int.fract (a * (nthPrime n : ℝ))

theorem primePoint_nonneg (a : ℝ) (n : ℕ) : 0 ≤ primePoint a n :=
  Int.fract_nonneg _

theorem primePoint_lt_one (a : ℝ) (n : ℕ) : primePoint a n < 1 :=
  Int.fract_lt_one _

theorem primePoint_mem_Ico (a : ℝ) (n : ℕ) : primePoint a n ∈ Set.Ico 0 1 :=
  ⟨primePoint_nonneg a n, primePoint_lt_one a n⟩

noncomputable def decimalDigit (x : ℝ) (j : ℕ) : Fin 10 :=
  ⟨⌊10 * Int.fract ((10 : ℝ)^j * x)⌋₊, by
    apply (Nat.floor_lt (mul_nonneg (by norm_num) (Int.fract_nonneg _))).mpr
    have h := Int.fract_lt_one ((10 : ℝ)^j * x)
    norm_num only [Nat.cast_ofNat]
    linarith⟩

theorem decimalDigit_formula (x : ℝ) (j : ℕ) :
    (decimalDigit x j : ℕ) = ⌊10 * Int.fract ((10 : ℝ)^j * x)⌋₊ := rfl

theorem decimalDigit_first_formula (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    (decimalDigit x 0 : ℕ) = ⌊10*x⌋₊ := by
  simp [decimalDigit, Int.fract_eq_self.mpr hx]

theorem first_digit_cylinder (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1)
    (d : Fin 10) : decimalDigit x 0 = d ↔
      (d:ℝ)/10 ≤ x ∧ x < ((d:ℝ)+1)/10 := by
  rw [← Fin.val_inj, decimalDigit_first_formula x hx,
    Nat.floor_eq_iff (mul_nonneg (by norm_num) hx.1)]
  constructor
  · rintro ⟨h₁,h₂⟩
    constructor <;> linarith
  · rintro ⟨h₁,h₂⟩
    constructor <;> linarith

def Matches {length : ℕ} (word : Fin length → Fin 10) (x : ℝ) : Prop :=
  ∀ j : Fin length, decimalDigit x j = word j

noncomputable def occurrences (points : ℕ → ℝ) {length : ℕ}
    (word : Fin length → Fin 10) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (fun n => Matches word (points n))

theorem mem_occurrences (points : ℕ → ℝ) {length : ℕ}
    (word : Fin length → Fin 10) (N n : ℕ) :
    n ∈ occurrences points word N ↔ n<N ∧ Matches word (points n) := by
  classical
  simp [occurrences]

noncomputable def blockCount (points : ℕ → ℝ) {length : ℕ}
    (word : Fin length → Fin 10) (N : ℕ) : ℕ :=
  (occurrences points word N).card

noncomputable def blockFrequency (points : ℕ → ℝ) {length : ℕ}
    (word : Fin length → Fin 10) (N : ℕ) : ℝ :=
  (blockCount points word N : ℝ) / N

def singletonWord (d : Fin 10) : Fin 1 → Fin 10 := fun _ => d

theorem matches_singleton (d : Fin 10) (x : ℝ) :
    Matches (singletonWord d) x ↔ decimalDigit x 0 = d := by
  constructor
  · intro h
    exact h 0
  · intro h j
    have hj : j=0 := Subsingleton.elim _ _
    simpa [hj, singletonWord] using h

theorem singleton_disjoint (points : ℕ → ℝ) (N : ℕ) (d e : Fin 10)
    (hne : d≠e) : Disjoint (occurrences points (singletonWord d) N)
      (occurrences points (singletonWord e) N) := by
  classical
  apply Finset.disjoint_left.mpr
  intro n hd he
  have hd' := (matches_singleton d (points n)).mp ((mem_occurrences _ _ _ _).mp hd).2
  have he' := (matches_singleton e (points n)).mp ((mem_occurrences _ _ _ _).mp he).2
  exact hne (hd'.symm.trans he')

theorem counts_le_length (points : ℕ → ℝ) (N : ℕ) (d e : Fin 10)
    (hne : d≠e) : blockCount points (singletonWord d) N +
      blockCount points (singletonWord e) N ≤ N := by
  classical
  have hd := singleton_disjoint points N d e hne
  have hsubset : occurrences points (singletonWord d) N ∪
      occurrences points (singletonWord e) N ⊆ Finset.range N := by
    intro n hn
    rcases Finset.mem_union.mp hn with hn | hn
    · exact Finset.mem_range.mpr ((mem_occurrences _ _ _ _).mp hn).1
    · exact Finset.mem_range.mpr ((mem_occurrences _ _ _ _).mp hn).1
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_union_of_disjoint hd, Finset.card_range] at hcard
  exact hcard

theorem frequencies_le_one (points : ℕ → ℝ) (N : ℕ) (d e : Fin 10)
    (hne : d≠e) : blockFrequency points (singletonWord d) N +
      blockFrequency points (singletonWord e) N ≤ 1 := by
  by_cases hN : N=0
  · simp [hN, blockFrequency]
  have hNpos : 0<(N:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hc : (blockCount points (singletonWord d) N : ℝ) +
      (blockCount points (singletonWord e) N : ℝ) ≤ N := by
    exact_mod_cast counts_le_length points N d e hne
  unfold blockFrequency
  rw [← add_div]
  exact (div_le_one hNpos).mpr hc

def PrintedInverseLengthRule (points : ℕ → ℝ) : Prop :=
  ∀ length : ℕ, 0<length → ∀ word : Fin length → Fin 10,
    Tendsto (blockFrequency points word) atTop (𝓝 ((length:ℝ)⁻¹))

theorem no_sequence_satisfies_printed_rule (points : ℕ → ℝ) :
    ¬PrintedInverseLengthRule points := by
  intro h
  have hzero : Tendsto (blockFrequency points (singletonWord 0)) atTop (𝓝 (1:ℝ)) := by
    simpa using h 1 (by decide) (singletonWord 0)
  have hone : Tendsto (blockFrequency points (singletonWord 1)) atTop (𝓝 (1:ℝ)) := by
    simpa using h 1 (by decide) (singletonWord 1)
  have hle : (1:ℝ)+1 ≤ 1 :=
    le_of_tendsto' (hzero.add hone) (fun N => frequencies_le_one points N 0 1 (by decide))
  norm_num at hle

def SlidingMatches (points : ℕ → ℝ) {length : ℕ}
    (word : Fin length → Fin 10) (start : ℕ) : Prop :=
  ∀ j : Fin length, decimalDigit (points (start+j)) 0 = word j

noncomputable def slidingOccurrences (points : ℕ → ℝ) {length : ℕ}
    (word : Fin length → Fin 10) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (SlidingMatches points word)

noncomputable def slidingFrequency (points : ℕ → ℝ) {length : ℕ}
    (word : Fin length → Fin 10) (N : ℕ) : ℝ :=
  ((slidingOccurrences points word N).card : ℝ) / N

theorem sliding_singleton_matches (points : ℕ → ℝ) (d : Fin 10) (n : ℕ) :
    SlidingMatches points (singletonWord d) n ↔ Matches (singletonWord d) (points n) := by
  rw [matches_singleton]
  constructor
  · intro h
    simpa [singletonWord] using h 0
  · intro h j
    have hj : j=0 := Subsingleton.elim _ _
    simpa [hj, singletonWord] using h

theorem sliding_singleton_frequency (points : ℕ → ℝ) (d : Fin 10) (N : ℕ) :
    slidingFrequency points (singletonWord d) N =
      blockFrequency points (singletonWord d) N := by
  classical
  simp only [slidingFrequency, blockFrequency, blockCount, slidingOccurrences, occurrences,
    sliding_singleton_matches]

theorem sliding_singleton_frequency_function (points : ℕ → ℝ) (d : Fin 10) :
    slidingFrequency points (singletonWord d) = blockFrequency points (singletonWord d) := by
  funext N
  exact sliding_singleton_frequency points d N

def PrintedSlidingRule (points : ℕ → ℝ) : Prop :=
  ∀ length : ℕ, 0<length → ∀ word : Fin length → Fin 10,
    Tendsto (slidingFrequency points word) atTop (𝓝 ((length:ℝ)⁻¹))

theorem no_sequence_satisfies_printed_sliding_rule (points : ℕ → ℝ) :
    ¬PrintedSlidingRule points := by
  intro h
  have hzero : Tendsto (blockFrequency points (singletonWord 0)) atTop (𝓝 (1:ℝ)) := by
    simpa only [sliding_singleton_frequency_function, Nat.cast_one, inv_one] using
      h 1 (by decide) (singletonWord 0)
  have hone : Tendsto (blockFrequency points (singletonWord 1)) atTop (𝓝 (1:ℝ)) := by
    simpa only [sliding_singleton_frequency_function, Nat.cast_one, inv_one] using
      h 1 (by decide) (singletonWord 1)
  have hle : (1:ℝ)+1 ≤ 1 :=
    le_of_tendsto' (hzero.add hone) (fun N => frequencies_le_one points N 0 1 (by decide))
  norm_num at hle

theorem sqrt_two_prime_sequence_fails_printed_rule :
    ¬PrintedInverseLengthRule (primePoint alpha) :=
  no_sequence_satisfies_printed_rule _

theorem explicit_counterexample : ∃ a : ℝ, Irrational a ∧
    (∀ n, primePoint a n ∈ Set.Ico (0:ℝ) 1) ∧
    ¬PrintedInverseLengthRule (primePoint a) :=
  ⟨alpha, alpha_irrational, primePoint_mem_Ico alpha,
    sqrt_two_prime_sequence_fails_printed_rule⟩

theorem not_universal_printed_rule :
    ¬∀ a : ℝ, Irrational a → PrintedInverseLengthRule (primePoint a) := by
  intro h
  exact sqrt_two_prime_sequence_fails_printed_rule (h alpha alpha_irrational)

theorem explicit_counterexample_both_countings : ∃ a : ℝ, Irrational a ∧
    (∀ n, primePoint a n ∈ Set.Ico (0:ℝ) 1) ∧
    ¬PrintedInverseLengthRule (primePoint a) ∧ ¬PrintedSlidingRule (primePoint a) :=
  ⟨alpha, alpha_irrational, primePoint_mem_Ico alpha,
    sqrt_two_prime_sequence_fails_printed_rule, no_sequence_satisfies_printed_sliding_rule _⟩

end TLMC79
