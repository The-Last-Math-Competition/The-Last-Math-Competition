import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.NormNum

namespace TLMC2473

def largest {n : ℕ} (p : Nat.Partition n) : ℕ := p.parts.toFinset.sup id

def rank {n : ℕ} (p : Nat.Partition n) : ℤ :=
  (largest p : ℤ) - p.parts.card

def ones {n : ℕ} (p : Nat.Partition n) : ℕ := p.parts.count 1

/-- The Andrews--Garvan crank, defined from the actual parts. -/
def crank {n : ℕ} (p : Nat.Partition n) : ℤ :=
  if ones p = 0 then (largest p : ℤ)
  else ((p.parts.filter fun a => ones p < a).card : ℤ) - ones p

def two : Nat.Partition 2 where
  parts := {2}
  parts_pos := by simp
  parts_sum := by simp

def oneOne : Nat.Partition 2 where
  parts := {1, 1}
  parts_pos := by simp
  parts_sum := by simp

theorem two_ne_oneOne : two ≠ oneOne := by
  intro h
  have hc := congrArg (fun p : Nat.Partition 2 => p.parts.card) h
  norm_num [two, oneOne] at hc

theorem partition_two_classification (p : Nat.Partition 2) : p = two ∨ p = oneOne := by
  by_cases h2 : 2 ∈ p.parts
  · obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem h2
    have hsum : s.sum = 0 := by have h := p.parts_sum; rw [hs] at h; simpa using h
    have hzero : s = 0 := by
      apply Multiset.eq_zero_of_forall_notMem
      intro a ha
      have hpos : 0 < a := p.parts_pos (by rw [hs]; exact Multiset.mem_cons_of_mem ha)
      have hz : a = 0 := (Multiset.sum_eq_zero_iff.mp hsum) a ha
      omega
    left
    apply Nat.Partition.ext
    simp [hs, hzero, two]
  · have he : p.parts = Multiset.replicate p.parts.card 1 :=
      Multiset.eq_replicate_card.mpr fun a ha => by
        have hlo := p.parts_pos ha
        have hhi := p.le_of_mem_parts ha
        have hne : a ≠ 2 := by intro h; subst a; exact h2 ha
        omega
    have hc : p.parts.card = 2 := by
      have h := p.parts_sum
      rw [he] at h
      simpa using h
    right
    apply Nat.Partition.ext
    rw [he, hc]
    norm_num [oneOne, Multiset.replicate_succ]

theorem univ_partition_two : (Finset.univ : Finset (Nat.Partition 2)) = {two, oneOne} := by
  ext p
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact partition_two_classification p

theorem rank_two : rank two = 1 := by norm_num [rank, largest, two]
theorem rank_oneOne : rank oneOne = -1 := by norm_num [rank, largest, oneOne]
theorem crank_two : crank two = 2 := by norm_num [crank, ones, largest, two]
theorem crank_oneOne : crank oneOne = -2 := by norm_num [crank, ones, largest, oneOne]

def RamanujanExceptional (n : ℕ) : Prop :=
  n % 5 = 4 ∨ n % 7 = 5 ∨ n % 11 = 6

theorem two_nonexceptional : ¬ RamanujanExceptional 2 := by norm_num [RamanujanExceptional]

noncomputable def distribution (n : ℕ) (stat : Nat.Partition n → ℤ) (a : ℤ) : ℕ :=
  (Finset.univ.filter fun p => stat p = a).card

noncomputable def residueDistribution (n : ℕ) (stat : Nat.Partition n → ℤ)
    (modulus : ℕ) (residue : ℤ) : ℕ :=
  (Finset.univ.filter fun p => stat p % (modulus : ℤ) = residue).card

theorem rank_count_one : distribution 2 rank 1 = 1 := by
  rw [distribution, univ_partition_two]
  norm_num [Finset.filter_insert, Finset.filter_singleton, rank_two, rank_oneOne, two_ne_oneOne]

theorem crank_count_one : distribution 2 crank 1 = 0 := by
  rw [distribution, univ_partition_two]
  norm_num [Finset.filter_insert, Finset.filter_singleton, crank_two, crank_oneOne]

theorem mod_five_counts : residueDistribution 2 rank 5 1 = 1 ∧
    residueDistribution 2 crank 5 1 = 0 := by
  simp only [residueDistribution, univ_partition_two]
  norm_num [Finset.filter_insert, Finset.filter_singleton, rank_two, rank_oneOne, crank_two, crank_oneOne, two_ne_oneOne]

theorem mod_seven_counts : residueDistribution 2 rank 7 1 = 1 ∧
    residueDistribution 2 crank 7 1 = 0 := by
  simp only [residueDistribution, univ_partition_two]
  norm_num [Finset.filter_insert, Finset.filter_singleton, rank_two, rank_oneOne, crank_two, crank_oneOne, two_ne_oneOne]

theorem mod_eleven_counts : residueDistribution 2 rank 11 1 = 1 ∧
    residueDistribution 2 crank 11 1 = 0 := by
  simp only [residueDistribution, univ_partition_two]
  norm_num [Finset.filter_insert, Finset.filter_singleton, rank_two, rank_oneOne, crank_two, crank_oneOne, two_ne_oneOne]

theorem no_pointwise_agreement_outside :
    ¬ ∀ n, ¬ RamanujanExceptional n → ∀ p : Nat.Partition n, rank p = crank p := by
  intro h
  have he := h 2 two_nonexceptional two
  rw [rank_two, crank_two] at he
  norm_num at he

theorem no_distribution_agreement_outside :
    ¬ ∀ n, ¬ RamanujanExceptional n → distribution n rank = distribution n crank := by
  intro h
  have he := congrFun (h 2 two_nonexceptional) 1
  rw [rank_count_one, crank_count_one] at he
  norm_num at he

theorem no_residue_agreement_outside :
    ¬ ∀ n, ¬ RamanujanExceptional n → ∀ m ∈ ({5, 7, 11} : Finset ℕ),
      residueDistribution n rank m = residueDistribution n crank m := by
  intro h
  have he := congrFun (h 2 two_nonexceptional 5 (by simp)) 1
  rw [mod_five_counts.1, mod_five_counts.2] at he
  norm_num at he

end TLMC2473
