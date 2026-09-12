/-
  Disproof of conjecture 00000000159.

  The conjecture asserts that for every prime `p ≥ 11` the complete graph `K_p`
  can be decomposed into cycles whose lengths are pairwise distinct primes.

  We refute it at `p = 11` by an edge count.

  A cycle in a simple graph has length equal to its number of distinct vertices,
  hence its length lies in `[3, p]`.  For `K_11` the pairwise distinct prime
  lengths therefore all lie in `{3, 5, 7, 11}`.  Whatever the exact reading of
  "decomposed into a union of cycles" (edge-disjoint decomposition, or a mere
  cover of all edges), the total of the cycle lengths is at least the number of
  edges of `K_11`:

      C(11, 2) = 11 * 10 / 2 = 55.

  But the four available lengths sum to `3 + 5 + 7 + 11 = 26 < 55`.

  This file formalises the arithmetic core of that obstruction in pure Lean 4
  (only `Std`, no Mathlib): a list of pairwise distinct members of
  `validLengths = [3, 5, 7, 11]` has sum at most `26`, so it can never reach the
  required total `55`.
-/

import Std

namespace Tlmc159

/-- The distinct prime cycle lengths available for `K_11`: the primes in `[3, 11]`. -/
def validLengths : List Nat := [3, 5, 7, 11]

/-- The number of edges of `K_p`, i.e. `C(p, 2) = p * (p - 1) / 2`. -/
def edgeCount (p : Nat) : Nat := p * (p - 1) / 2

/-- A computable primality test: `n` is prime when `n ≥ 2` and no `m` with
`2 ≤ m < n` divides `n`.  (`Nat.Prime` lives in Mathlib, which we do not
import, so the test is written out explicitly; it agrees with the usual notion
on `[3, 11]`.) -/
def isPrime (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range n).all (fun m => decide (m < 2) || (n % m != 0))

/-- Every prime in the bounded range `[3, 11]` is one of the four available
cycle lengths.  This is a finite `List.all` check over `List.range 12`
(phrased as a Boolean `all` so that only decidable comparisons are needed). -/
theorem prime_mem_validLengths :
    (List.range 12).all
      (fun p => decide (3 ≤ p → isPrime p = true → p ∈ validLengths)) = true := by
  decide

/-- The sum of all available cycle lengths for `K_11` is `26`. -/
theorem validLengths_sum : validLengths.sum = 26 := by
  decide

/-! ### A small list-removal helper

`del a L` removes the first occurrence of `a` from `L`.  It is used to prove
the sublist-sum bound below without relying on Mathlib's `Finset` or `erase`
library. -/

/-- Remove the first occurrence of `a` from `L`. -/
def del (a : Nat) : List Nat → List Nat
  | [] => []
  | b :: t => if b = a then t else b :: del a t

/-- Anything left after deleting `a` was already in the list. -/
theorem del_mem_of_mem {a x : Nat} {L : List Nat} (hx : x ∈ del a L) : x ∈ L := by
  revert hx
  induction L with
  | nil => intro hx; simp [del] at hx
  | cons b t ih =>
      intro hx
      by_cases h : b = a
      · simp only [del, if_pos h] at hx
        exact List.mem_cons.mpr (Or.inr hx)
      · simp only [del, if_neg h] at hx
        rcases List.mem_cons.mp hx with h1 | h2
        · rw [h1]; simp
        · exact List.mem_cons.mpr (Or.inr (ih h2))

/-- Deleting from a duplicate-free list leaves a duplicate-free list. -/
theorem del_nodup {a : Nat} {L : List Nat} (hnd : L.Nodup) : (del a L).Nodup := by
  revert hnd
  induction L with
  | nil => intro hnd; exact List.nodup_nil
  | cons b t ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      obtain ⟨hb, hnd_t⟩ := hnd
      by_cases h : b = a
      · simp only [del, if_pos h]; exact hnd_t
      · simp only [del, if_neg h]
        rw [List.nodup_cons]
        exact ⟨fun hm => hb (del_mem_of_mem hm), ih hnd_t⟩

/-- If `a` occurs in a duplicate-free list, the sum splits off one copy of `a`. -/
theorem del_sum {a : Nat} {L : List Nat} (hnd : L.Nodup) (ha : a ∈ L) :
    L.sum = a + (del a L).sum := by
  revert hnd ha
  induction L with
  | nil => intro hnd ha; cases ha
  | cons b t ih =>
      intro hnd ha
      rw [List.nodup_cons] at hnd
      obtain ⟨hb, hnd_t⟩ := hnd
      by_cases h : b = a
      · rw [h]
        simp [del, List.sum_cons]
      · have ha_t : a ∈ t := by
          rcases List.mem_cons.mp ha with h1 | h2
          · exact absurd h1.symm h
          · exact h2
        rw [List.sum_cons, ih hnd_t ha_t]
        simp only [del, if_neg h, List.sum_cons]
        exact Nat.add_left_comm b a (del a t).sum

/-- In a duplicate-free list, deleting `a` really removes every occurrence of `a`. -/
theorem del_not_mem {a : Nat} {L : List Nat} (hnd : L.Nodup) (ha : a ∈ L) :
    a ∉ del a L := by
  revert hnd ha
  induction L with
  | nil => intro hnd ha; cases ha
  | cons b t ih =>
      intro hnd ha
      rw [List.nodup_cons] at hnd
      obtain ⟨hb, hnd_t⟩ := hnd
      by_cases h : b = a
      · simp only [del, if_pos h]
        intro hat
        rw [← h] at hat
        exact hb hat
      · have ha_t : a ∈ t := by
          rcases List.mem_cons.mp ha with h1 | h2
          · exact absurd h1.symm h
          · exact h2
        simp only [del, if_neg h]
        intro hmem
        rcases List.mem_cons.mp hmem with h1 | h2
        · exact h h1.symm
        · exact ih hnd_t ha_t h2

/-! ### The counting obstruction -/

/-- **Central counting lemma.**  A duplicate-free list whose elements are all
available cycle lengths has sum at most the sum of *all* available lengths,
namely `26`. -/
theorem sublist_sum_le : ∀ (A L : List Nat), A.Nodup → (∀ x ∈ L, x ∈ A) → L.Nodup →
    L.sum ≤ A.sum
  | [], L, _, hmem, _ => by
      have hL : L = [] := by
        cases L with
        | nil => rfl
        | cons b t => exact absurd (hmem b (by simp)) (by simp)
      simp [hL]
  | a :: t, L, hndA, hmem, hndL => by
      rw [List.nodup_cons] at hndA
      obtain ⟨ha_notin, hnd_t⟩ := hndA
      by_cases ha : a ∈ L
      · have hsum := del_sum hndL ha
        have hmem' : ∀ x ∈ del a L, x ∈ t := by
          intro x hx
          have hxL : x ∈ L := del_mem_of_mem hx
          have hxA : x ∈ a :: t := hmem x hxL
          rcases List.mem_cons.mp hxA with h1 | h2
          · have hnot : a ∉ del a L := del_not_mem hndL ha
            exact absurd (h1 ▸ hx) hnot
          · exact h2
        have ih' := sublist_sum_le t (del a L) hnd_t hmem' (del_nodup hndL)
        rw [hsum, List.sum_cons]
        exact Nat.add_le_add (Nat.le_refl a) ih'
      · have hmem' : ∀ x ∈ L, x ∈ t := by
          intro x hx
          have hxA : x ∈ a :: t := hmem x hx
          rcases List.mem_cons.mp hxA with h1 | h2
          · exact absurd (h1 ▸ hx) ha
          · exact h2
        have ih' := sublist_sum_le t L hnd_t hmem' hndL
        rw [List.sum_cons]
        exact Nat.le_trans ih' (Nat.le_add_left t.sum a)

/-- Every list of pairwise distinct available cycle lengths has sum at most `26`. -/
theorem sum_validLengths_le (L : List Nat) (hnd : L.Nodup)
    (hmem : ∀ l ∈ L, l ∈ validLengths) : L.sum ≤ 26 := by
  have h := sublist_sum_le validLengths L (by decide) hmem hnd
  rw [validLengths_sum] at h
  exact h

/-- No such list can have sum `55`. -/
theorem no_sum_55 (L : List Nat) (hnd : L.Nodup)
    (hmem : ∀ l ∈ L, l ∈ validLengths) : L.sum ≠ 55 := by
  intro h55
  have hle := sum_validLengths_le L hnd hmem
  rw [h55] at hle
  exact absurd hle (by decide)

/-- **Main disproof.**  A cycle decomposition of `K_11` into cycles of pairwise
distinct prime lengths would give a list `L` of distinct members of
`validLengths` whose sum is the number of edges `C(11, 2) = 11 * 10 / 2 = 55`.
No such list exists. -/
theorem conjecture_00000000159_false
    (L : List Nat) (hnd : L.Nodup) (hmem : ∀ l ∈ L, l ∈ validLengths)
    (hcover : L.sum = 11 * 10 / 2) : False := by
  exact no_sum_55 L hnd hmem hcover

/-- The same obstruction in the weaker reading, where the cycles merely *cover*
all edges: the total length is then at least `11 * 10 / 2 = 55`, but it is at
most `26`. -/
theorem conjecture_00000000159_false_cover
    (L : List Nat) (hnd : L.Nodup) (hmem : ∀ l ∈ L, l ∈ validLengths)
    (hcover : 11 * 10 / 2 ≤ L.sum) : False :=
  absurd (Nat.le_trans hcover (sum_validLengths_le L hnd hmem)) (by decide)

end Tlmc159
