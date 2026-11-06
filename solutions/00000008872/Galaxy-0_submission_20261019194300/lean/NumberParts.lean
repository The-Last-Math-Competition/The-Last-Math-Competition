import Core
namespace TLMC8872

@[simp] theorem le_zero_zero : le zero zero = true := by simp [zero, le]
@[simp] theorem le_zero_star : le zero star = false := by simp [zero, star, le]
@[simp] theorem le_star_zero : le star zero = false := by simp [zero, star, le]

theorem zero_allSmall : AllSmall zero := by
  apply AllSmall.node <;> simp

theorem star_allSmall : AllSmall star := by
  apply AllSmall.node
  · simp
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst g
    exact zero_allSmall
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst g
    exact zero_allSmall

theorem zero_star_inequivalent : ¬ Equiv zero star := by
  simp [Equiv]

@[simp] theorem neg_zero : neg zero = zero := by simp [neg, zero]
@[simp] theorem neg_tiny_zero : neg (tiny 0) = .node [] [zero] := by
  simp [neg, tiny]
@[simp] theorem neg_tiny_succ (n : Nat) :
    neg (tiny (n+1)) = .node [neg (tiny n)] [zero] := by
  simp [neg, tiny]

@[simp] theorem tiny_not_le_zero (n : Nat) : le (tiny n) zero = false := by
  cases n <;> rw [tiny, le_node_zero] <;> simp

@[simp] theorem zero_le_tiny (n : Nat) : le zero (tiny n) = true := by
  cases n <;> rw [tiny, le_zero_node] <;> simp

@[simp] theorem tiny_not_le_star (n : Nat) : le (tiny n) star = false := by
  have ht := zero_le_tiny n
  cases n <;> simp only [tiny] at ht ⊢
  all_goals rw [star, le_node]
  all_goals simp only [List.all_cons, List.all_nil, Bool.and_true]
  all_goals change ((!le star zero) && (!le zero _)) = false
  all_goals simp only [le_star_zero, ht, Bool.not_false, Bool.not_true, Bool.true_and]

@[simp] theorem star_le_tiny (n : Nat) : le star (tiny n) = true := by
  cases n with
  | zero => simp [tiny, star, zero, le]
  | succ n =>
    rw [star, tiny, le_node]
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    change ((!le (tiny (n+1)) zero) && (!le (tiny n) star)) = true
    simp

@[simp] theorem zero_not_le_neg_tiny (n : Nat) : le zero (neg (tiny n)) = false := by
  cases n <;> simp only [neg_tiny_zero, neg_tiny_succ, le_zero_node] <;> simp

@[simp] theorem neg_tiny_le_zero (n : Nat) : le (neg (tiny n)) zero = true := by
  cases n <;> simp only [neg_tiny_zero, neg_tiny_succ, le_node_zero] <;> simp

@[simp] theorem star_not_le_neg_tiny (n : Nat) : le star (neg (tiny n)) = false := by
  have ht := neg_tiny_le_zero n
  cases n <;> simp only [neg_tiny_zero, neg_tiny_succ] at ht ⊢
  all_goals rw [star, le_node]
  all_goals simp only [List.all_cons, List.all_nil, Bool.and_true, ht,
    Bool.not_true, Bool.false_and]

@[simp] theorem neg_tiny_le_star (n : Nat) : le (neg (tiny n)) star = true := by
  cases n with
  | zero => simp [star, zero, le]
  | succ n =>
    rw [neg_tiny_succ, star, le_node]
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    rw [← neg_tiny_succ n]
    change ((!le star (neg (tiny n))) && (!le zero (neg (tiny (n+1))))) = true
    simp only [star_not_le_neg_tiny, zero_not_le_neg_tiny, Bool.not_false, Bool.and_self]

theorem zero_numericalPartZero : NumericalPartZero zero := by
  intro n
  simp [Lt]

theorem star_numericalPartZero : NumericalPartZero star := by
  intro n
  simp [Lt]

end TLMC8872
