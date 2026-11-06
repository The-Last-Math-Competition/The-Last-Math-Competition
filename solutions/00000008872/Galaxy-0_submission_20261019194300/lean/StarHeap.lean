import Toggle
import Stabilization
namespace TLMC8872

theorem heap_left_move (g : Game) (m n : Nat) (hm : m < n)
    (h : (outcome g m).2 = false) : (outcome g n).1 = true := by
  rw [outcome_eq]
  apply Bool.or_eq_true_iff.mpr
  right
  exact List.any_eq_true.mpr ⟨m, List.mem_range.mpr hm, by simp [h]⟩

theorem heap_right_move (g : Game) (m n : Nat) (hm : m < n)
    (h : (outcome g m).1 = false) : (outcome g n).2 = true := by
  rw [outcome_eq]
  apply Bool.or_eq_true_iff.mpr
  right
  exact List.any_eq_true.mpr ⟨m, List.mem_range.mpr hm, by simp [h]⟩

theorem left_absorb_next (g : Game) (n : Nat) :
    (!(outcome g (n+1)).2 || (outcome g n).1) = (outcome g n).1 := by
  cases h : (outcome g n).1
  · have hn := heap_right_move g n (n+1) (by omega) h
    simp [hn]
  · simp

theorem right_absorb_next (g : Game) (n : Nat) :
    (!(outcome g (n+1)).1 || (outcome g n).2) = (outcome g n).2 := by
  cases h : (outcome g n).2
  · have hn := heap_left_move g n (n+1) (by omega) h
    simp [hn]
  · simp

theorem bool_repeat (a b c : Bool) : ((a || b) || (c || a)) = (a || (b || c)) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- The exact Nim identity `* + *n = *(n xor 1)`, proved in every arbitrary
short-game context, directly from normal-play moves. -/
theorem star_heap (g : Game) (n : Nat) :
    outcome (add star g) n = outcome g (toggle n) := by
  cases g with
  | node l r =>
    rw [star_add_node, outcome_node]
    simp only [List.any_cons, List.any_map, Function.comp_def]
    have hl :
        (l.any fun h => !(outcome (add star h) n).2) =
        (l.any fun h => !(outcome h (toggle n)).2) := by
      apply any_congr_mem
      intro h hh
      rw [star_heap h n]
    have hr :
        (r.any fun h => !(outcome (add star h) n).1) =
        (r.any fun h => !(outcome h (toggle n)).1) := by
      apply any_congr_mem
      intro h hh
      rw [star_heap h n]
    have hnL :
        ((List.range n).any fun m => !(outcome (add star (.node l r)) m).2) =
        ((List.range n).any fun m => !(outcome (.node l r) (toggle m)).2) := by
      apply any_congr_mem
      intro m hm
      rw [star_heap (.node l r) m]
    have hnR :
        ((List.range n).any fun m => !(outcome (add star (.node l r)) m).1) =
        ((List.range n).any fun m => !(outcome (.node l r) (toggle m)).1) := by
      apply any_congr_mem
      intro m hm
      rw [star_heap (.node l r) m]
    rw [hl, hr]
    rw [← star_add_node l r, hnL, hnR]
    by_cases hp : n % 2 = 0
    · obtain ⟨k, rfl⟩ : ∃ k, n = 2*k := ⟨n/2, by omega⟩
      rw [toggle_even, toggle_range_any k (fun m => !(outcome (.node l r) m).2),
        toggle_range_any k (fun m => !(outcome (.node l r) m).1)]
      conv => rhs; rw [outcome_node]
      simp only [List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
      simp only [Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
    · obtain ⟨k, rfl⟩ : ∃ k, n = 2*k+1 := ⟨n/2, by omega⟩
      rw [toggle_odd, toggle_range_any_odd k (fun m => !(outcome (.node l r) m).2),
        toggle_range_any_odd k (fun m => !(outcome (.node l r) m).1)]
      have ht := outcome_node l r (2*k)
      have htl := congrArg Prod.fst ht
      have htr := congrArg Prod.snd ht
      dsimp only at htl htr
      apply Prod.ext
      · dsimp only
        rw [bool_repeat, ← htl]
        exact left_absorb_next (.node l r) (2*k)
      · dsimp only
        rw [bool_repeat, ← htr]
        exact right_absorb_next (.node l r) (2*k)
termination_by sizeOf g + n
decreasing_by
  all_goals
    first
    | have hs := List.sizeOf_lt_of_mem hh; simp_wf; omega
    | have hs := List.mem_range.mp hm; simp_wf; omega

end TLMC8872
