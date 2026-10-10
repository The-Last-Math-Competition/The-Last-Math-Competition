import Mathlib.Combinatorics.Enumerative.Partition
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace TLMC214

abbrev partitionCount (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

lemma parts_card_le {n : ℕ} (p : Nat.Partition n) : p.parts.card ≤ n := by
  have h := Multiset.card_nsmul_le_sum (s := p.parts) (a := 1) (fun x hx => p.parts_pos hx)
  simpa [p.parts_sum] using h

lemma part_le {n : ℕ} (p : Nat.Partition n) {a : ℕ} (ha : a ∈ p.parts) : a ≤ n := by
  simpa [p.parts_sum] using Multiset.le_sum_of_mem ha

def largeParts {n : ℕ} (p : Nat.Partition n) (k : ℕ) : Multiset ℕ :=
  p.parts.filter (fun a => ¬ a ≤ k)

lemma large_card_le {n k : ℕ} (hn : n ≤ k * k) (p : Nat.Partition n) :
    (largeParts p k).card ≤ k := by
  have hsum : (largeParts p k).sum ≤ n := by
    have h := congrArg Multiset.sum (Multiset.filter_add_not (fun a => a ≤ k) p.parts)
    simp only [Multiset.sum_add, p.parts_sum] at h
    unfold largeParts
    omega
  have hmul := Multiset.card_nsmul_le_sum (s := largeParts p k) (a := k + 1) (by
    intro x hx
    have := (Multiset.mem_filter.mp hx).2
    omega)
  simp only [smul_eq_mul] at hmul
  nlinarith

abbrev Code (n k : ℕ) := (Fin (k + 1) → Fin (n + 1)) × Fin (k + 1) × (Fin k → Fin (n + 1))

def encode {n k : ℕ} (hn : n ≤ k * k) (p : Nat.Partition n) : Code n k :=
  (fun i => ⟨p.parts.count i.val, Nat.lt_succ_of_le ((Multiset.count_le_card _ _).trans (parts_card_le p))⟩,
   ⟨(largeParts p k).card, Nat.lt_succ_of_le (large_card_le hn p)⟩,
   fun i => ⟨if h : i.val < ((largeParts p k).sort (· ≤ ·)).length then
       ((largeParts p k).sort (· ≤ ·))[i.val] else 0, by
     split_ifs with h
     · exact Nat.lt_succ_of_le (part_le p (Multiset.mem_of_mem_filter
         ((Multiset.mem_sort (· ≤ ·)).mp (List.getElem_mem h))))
     · exact Nat.zero_lt_succ _⟩)

lemma encode_injective {n k : ℕ} (hn : n ≤ k * k) : Function.Injective (encode hn) := by
  intro p q he
  have hc : (largeParts p k).card = (largeParts q k).card :=
    congrArg (fun z : Code n k => z.2.1.val) he
  have hl : (largeParts p k).sort (· ≤ ·) = (largeParts q k).sort (· ≤ ·) := by
    apply List.ext_getElem (by simpa using hc)
    intro i hi hj
    have hik : i < k := by
      have hp := large_card_le hn p
      simp only [Multiset.length_sort] at hi
      omega
    have he' := congrArg (fun z : Code n k => (z.2.2 ⟨i, hik⟩).val) he
    simpa only [encode, dif_pos hi, dif_pos hj] using he'
  have hm : largeParts p k = largeParts q k := by
    have h := congrArg (fun l : List ℕ => (l : Multiset ℕ)) hl
    simpa only [Multiset.sort_eq] using h
  apply Nat.Partition.ext
  apply Multiset.ext.mpr
  intro a
  by_cases ha : a ≤ k
  · exact congrArg (fun z : Code n k => (z.1 ⟨a, Nat.lt_succ_of_le ha⟩).val) he
  · have h := congrArg (Multiset.count a) hm
    simpa only [largeParts, Multiset.count_filter_of_pos (p := fun x => ¬ x ≤ k) ha] using h

lemma partition_count_bound {n k : ℕ} (hn : n ≤ k * k) :
    partitionCount n ≤ (n + 1) ^ (k + 1) * ((k + 1) * (n + 1) ^ k) := by
  have h := Fintype.card_le_of_injective (encode hn) (encode_injective hn)
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] using h


def hookPartition {n : ℕ} (i : Fin n) : Nat.Partition n where
  parts := (i.val + 1) ::ₘ Multiset.replicate (n - (i.val + 1)) 1
  parts_pos := by
    intro a ha
    simp only [Multiset.mem_cons, Multiset.mem_replicate] at ha
    rcases ha with rfl | ⟨_, rfl⟩ <;> omega
  parts_sum := by
    simp only [Multiset.sum_cons, Multiset.sum_replicate, smul_eq_mul, mul_one]
    omega

lemma hook_injective (n : ℕ) : Function.Injective (hookPartition (n := n)) := by
  intro i j hij
  have h := congrArg (fun p : Nat.Partition n => p.parts.card) hij
  simp only [hookPartition, Multiset.card_cons, Multiset.card_replicate] at h
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  omega

lemma nat_le_partitionCount (n : ℕ) : n ≤ partitionCount n := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ (hook_injective n)

lemma partitionCount_pos (n : ℕ) : 0 < partitionCount n := Fintype.card_pos

end TLMC214
