import Stabilization
import Sums

namespace TLMC8872

theorem all_attach {α : Type} (l : List α) (f : α → Bool) :
    l.attach.all (fun x => f x.val) = l.all f := by
  rw [List.all_subtype (g := f) (by intros; rfl), List.unattach_attach]

theorem outcome_zero_heap_aux (s : Nat) :
    ∀ g : Game, sizeOf g = s →
      outcome g 0 = (!(le g zero), !(le zero g)) := by
  induction s using Nat.strongRecOn with
  | ind s ih =>
    intro g hg
    cases g with
    | node l r =>
      rw [outcome_node]
      simp only [List.range_zero, List.any_nil, Bool.or_false]
      unfold zero
      rw [le, le]
      simp only [List.attach_nil, List.all_nil, Bool.and_true, Bool.true_and]
      rw [all_attach l (fun x => !(le (.node [] []) x)),
          all_attach r (fun x => !(le x (.node [] [])))]
      simp only [List.not_all_eq_any_not, Bool.not_not]
      apply Prod.ext
      · apply any_congr_mem l
        intro x hx
        have hsmall := List.sizeOf_lt_of_mem hx
        have hxs : sizeOf x < s := by simp_all; omega
        have eqx := ih (sizeOf x) hxs x rfl
        simp only [eqx, Bool.not_not]
        rfl
      · apply any_congr_mem r
        intro x hx
        have hsmall := List.sizeOf_lt_of_mem hx
        have hxs : sizeOf x < s := by simp_all; omega
        have eqx := ih (sizeOf x) hxs x rfl
        simp only [eqx, Bool.not_not]
        rfl

theorem outcome_zero_heap (g : Game) :
    outcome g 0 = (!(le g zero), !(le zero g)) :=
  outcome_zero_heap_aux (sizeOf g) g rfl

/-- The canonical Nim heap: each player may reduce its size arbitrarily. -/
def nimHeap (n : Nat) : Game :=
  .node ((List.range n).attach.map fun m => nimHeap m.val)
        ((List.range n).attach.map fun m => nimHeap m.val)
termination_by n
decreasing_by
  all_goals exact List.mem_range.mp m.property

theorem map_attach {α β : Type} (l : List α) (f : α → β) :
    l.attach.map (fun x => f x.val) = l.map f := by
  rw [List.map_subtype (g := f) (by intros; rfl), List.unattach_attach]

theorem nimHeap_eq (n : Nat) :
    nimHeap n = .node ((List.range n).map nimHeap) ((List.range n).map nimHeap) := by
  rw [nimHeap, map_attach (List.range n) nimHeap]

theorem add_node (gl gr hl hr : List Game) :
    add (.node gl gr) (.node hl hr) = .node
      (gl.map (fun g => add g (.node hl hr)) ++ hl.map (add (.node gl gr)))
      (gr.map (fun g => add g (.node hl hr)) ++ hr.map (add (.node gl gr))) := by
  rw [add]
  rw [map_attach gl (fun g => add g (.node hl hr)),
      map_attach gr (fun g => add g (.node hl hr)),
      map_attach hl (add (.node gl gr)), map_attach hr (add (.node gl gr))]

theorem add_nimHeap_node (l r : List Game) (n : Nat) :
    add (.node l r) (nimHeap n) = .node
      (l.map (fun g => add g (nimHeap n)) ++
        (List.range n).map (fun m => add (.node l r) (nimHeap m)))
      (r.map (fun g => add g (nimHeap n)) ++
        (List.range n).map (fun m => add (.node l r) (nimHeap m))) := by
  rw [nimHeap_eq, add_node]
  simp only [List.map_map, Function.comp_def]

theorem outcome_sum_nim_aux (s : Nat) :
    ∀ (g : Game) (n : Nat), sizeOf g + n = s →
      outcome (add g (nimHeap n)) 0 = outcome g n := by
  induction s using Nat.strongRecOn with
  | ind s ih =>
    intro g n hs
    cases g with
    | node l r =>
      rw [add_nimHeap_node, outcome_node, outcome_node]
      simp only [List.range_zero, List.any_nil, Bool.or_false,
        List.any_append, List.any_map, Function.comp_def]
      have hl : ∀ x ∈ l,
          outcome (add x (nimHeap n)) 0 = outcome x n := by
        intro x hx
        have hsmall := List.sizeOf_lt_of_mem hx
        apply ih (sizeOf x + n) _ x n rfl
        simp_all
        omega
      have hr : ∀ x ∈ r,
          outcome (add x (nimHeap n)) 0 = outcome x n := by
        intro x hx
        have hsmall := List.sizeOf_lt_of_mem hx
        apply ih (sizeOf x + n) _ x n rfl
        simp_all
        omega
      have hm : ∀ m ∈ List.range n,
          outcome (add (.node l r) (nimHeap m)) 0 = outcome (.node l r) m := by
        intro m hm
        have hmn := List.mem_range.mp hm
        apply ih (sizeOf (Game.node l r) + m) _ (.node l r) m rfl
        omega
      apply Prod.ext
      · dsimp only
        congr 1
        · apply any_congr_mem l
          intro x hx
          rw [hl x hx]
        · apply any_congr_mem (List.range n)
          intro m hmn
          rw [hm m hmn]
      · dsimp only
        congr 1
        · apply any_congr_mem r
          intro x hx
          rw [hr x hx]
        · apply any_congr_mem (List.range n)
          intro m hmn
          rw [hm m hmn]

/-- The evaluator is exactly actual disjunctive-sum normal play. -/
theorem outcome_sum_nim (g : Game) (n : Nat) :
    outcome (add g (nimHeap n)) 0 = outcome g n :=
  outcome_sum_nim_aux (sizeOf g + n) g n rfl

/-- Explicit Conway-order semantics for the remote-heap evaluator. -/
theorem outcome_conway (g : Game) (n : Nat) :
    outcome g n =
      (!(le (add g (nimHeap n)) zero), !(le zero (add g (nimHeap n)))) := by
  rw [← outcome_sum_nim, outcome_zero_heap]

end TLMC8872
