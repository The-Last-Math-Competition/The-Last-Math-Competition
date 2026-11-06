import Std
set_option autoImplicit false
namespace PIR

-- This is a finite coupling construction, not an assumption that different
-- desired-index protocols use the same private coins.
theorem reorder_seed_list {Seed Q : Type} (query : Seed → Q)
    (queries : List Q) (seeds : List Seed)
    (h : (seeds.map query).Perm queries) :
    ∃ reordered : List Seed, reordered.Perm seeds ∧ reordered.map query = queries := by
  induction queries generalizing seeds with
  | nil =>
    have hn : seeds = [] := by
      have hh := h.length_eq
      simp at hh
      exact hh
    subst seeds
    exact ⟨[], .rfl, rfl⟩
  | cons q qs ih =>
    have hm : q ∈ seeds.map query := h.symm.subset (by simp)
    obtain ⟨a, ha, hqa⟩ := List.mem_map.mp hm
    obtain ⟨left, right, hs⟩ := List.append_of_mem ha
    subst seeds
    have pm : (left ++ a :: right).Perm (a :: (left ++ right)) := List.perm_middle
    have hp : (query a :: (left ++ right).map query).Perm (q :: qs) := by
      simpa only [List.map_cons] using (pm.map query).symm.trans h
    rw [hqa] at hp
    have ht : ((left ++ right).map query).Perm qs := hp.cons_inv
    obtain ⟨tail, htail, he⟩ := ih (left ++ right) ht
    refine ⟨a :: tail, (htail.cons a).trans pm.symm, ?_⟩
    simp only [List.map_cons, hqa, he]

def natSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + natSum xs

theorem natSum_perm {a b : List Nat} (h : a.Perm b) : natSum a = natSum b := by
  induction h with
  | nil => rfl
  | cons x h ih => simp only [natSum, ih]
  | swap x y xs => simp only [natSum]; omega
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem reorder_preserves_all_costs {Seed : Type} {a b : List Seed}
    (h : a.Perm b) (cost : Seed → Nat) :
    natSum (a.map cost) = natSum (b.map cost) := natSum_perm (h.map cost)

-- Exact privacy for uniform finite random tapes means that every query has
-- equal multiplicity. The library's theorem turns this into a permutation.
theorem coupling_from_equal_query_counts {Seed Q : Type} [DecidableEq Q]
    (query : Seed → Q) (queries : List Q) (seeds : List Seed)
    (privacy : ∀ q, (seeds.map query).count q = queries.count q) :
    ∃ reordered : List Seed, reordered.Perm seeds ∧ reordered.map query = queries ∧
      ∀ cost : Seed → Nat, natSum (reordered.map cost) = natSum (seeds.map cost) := by
  have hp : (seeds.map query).Perm queries := List.perm_iff_count.mpr privacy
  obtain ⟨reordered, hr, hq⟩ := reorder_seed_list query queries seeds hp
  exact ⟨reordered, hr, hq, fun cost => reorder_preserves_all_costs hr cost⟩

#print axioms coupling_from_equal_query_counts
end PIR
