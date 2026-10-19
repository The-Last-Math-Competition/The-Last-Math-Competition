import Core

namespace TLMC8872

/-- Normal play of a short game and a Nim heap. Each coordinate records whether
    the named player wins when that player has the first move. -/
def outcome (g : Game) (n : Nat) : Bool × Bool :=
  match g with
  | .node l r =>
    ((l.attach.any fun h => !(outcome h.val n).2) ||
      ((List.range n).attach.any fun m => !(outcome (.node l r) m.val).2),
     (r.attach.any fun h => !(outcome h.val n).1) ||
      ((List.range n).attach.any fun m => !(outcome (.node l r) m.val).1))
termination_by sizeOf g + n
decreasing_by
  · have := List.sizeOf_lt_of_mem h.property
    simp_wf
    omega
  · have := List.mem_range.mp m.property
    simp_wf
    omega
  · have := List.sizeOf_lt_of_mem h.property
    simp_wf
    omega
  · have := List.mem_range.mp m.property
    simp_wf
    omega

def base (g : Game) (n : Nat) : Bool × Bool :=
  match g with
  | .node l r => (l.any fun h => !(outcome h n).2,
                  r.any fun h => !(outcome h n).1)

def heapPrefix (g : Game) (n : Nat) : Bool × Bool :=
  ((List.range n).any fun m => !(outcome g m).2,
   (List.range n).any fun m => !(outcome g m).1)

def combine (a p : Bool × Bool) : Bool × Bool :=
  (a.1 || p.1, a.2 || p.2)

def step (a p : Bool × Bool) : Bool × Bool :=
  (p.1 || !(a.2 || p.2), p.2 || !(a.1 || p.1))

theorem any_attach {α : Type} (l : List α) (f : α → Bool) :
    l.attach.any (fun x => f x.val) = l.any f := by
  rw [List.any_subtype (g := f) (by intros; rfl), List.unattach_attach]

theorem any_congr_mem {α : Type} (l : List α) (f h : α → Bool)
    (eq : ∀ x ∈ l, f x = h x) : l.any f = l.any h := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons]
    rw [eq x (by simp), ih (by intro y hy; exact eq y (by simp [hy]))]

theorem outcome_eq (g : Game) (n : Nat) :
    outcome g n = combine (base g n) (heapPrefix g n) := by
  cases g with
  | node l r =>
    rw [outcome]
    rw [any_attach l (fun h => !(outcome h n).2),
      any_attach r (fun h => !(outcome h n).1),
      any_attach (List.range n) (fun m => !(outcome (.node l r) m).2),
      any_attach (List.range n) (fun m => !(outcome (.node l r) m).1)]
    rfl

theorem outcome_node (l r : List Game) (n : Nat) :
    outcome (.node l r) n =
      ((l.any fun h => !(outcome h n).2) ||
        (List.range n).any (fun m => !(outcome (.node l r) m).2),
       (r.any fun h => !(outcome h n).1) ||
        (List.range n).any (fun m => !(outcome (.node l r) m).1)) := by
  exact outcome_eq (.node l r) n

theorem prefix_succ (g : Game) (n : Nat) :
    heapPrefix g (n + 1) = step (base g n) (heapPrefix g n) := by
  simp only [heapPrefix, List.range_succ, List.any_append, List.any_cons,
    List.any_nil, Bool.or_false]
  rw [outcome_eq]
  rfl

theorem step_idempotent (a p : Bool × Bool) :
    step a (step a p) = step a p := by
  rcases a with ⟨a,b⟩
  rcases p with ⟨p,q⟩
  cases a <;> cases b <;> cases p <;> cases q <;> rfl


theorem stable_of_base (g : Game) (B : Nat)
    (hb : ∀ n, B ≤ n → base g n = base g B) :
    ∀ n, B + 1 ≤ n → outcome g n = outcome g (B + 1) := by
  have hp : ∀ k, heapPrefix g (B + 1 + k) = heapPrefix g (B + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show B + 1 + (k + 1) = (B + 1 + k) + 1 by omega,
        prefix_succ, hb _ (by omega), ih, prefix_succ, step_idempotent]
  intro n hn
  rw [outcome_eq, outcome_eq, hb n (by omega), hb (B + 1) (by omega)]
  rw [show n = B + 1 + (n - (B + 1)) by omega, hp]

theorem outcome_stable_aux (s : Nat) :
    ∀ g : Game, sizeOf g = s → ∀ n, s + 1 ≤ n →
      outcome g n = outcome g (s + 1) := by
  induction s using Nat.strongRecOn with
  | ind s ih =>
    intro g hsize
    apply stable_of_base g s
    intro n hn
    cases g with
    | node l r =>
      apply Prod.ext
      · apply any_congr_mem l
        intro x hx
        have hsmall := List.sizeOf_lt_of_mem hx
        have hxs : sizeOf x < s := by simp_all; omega
        have eqn := ih (sizeOf x) hxs x rfl n (by omega)
        have eqs := ih (sizeOf x) hxs x rfl s (by omega)
        simp only [eqn, eqs]
      · apply any_congr_mem r
        intro x hx
        have hsmall := List.sizeOf_lt_of_mem hx
        have hxs : sizeOf x < s := by simp_all; omega
        have eqn := ih (sizeOf x) hxs x rfl n (by omega)
        have eqs := ih (sizeOf x) hxs x rfl s (by omega)
        simp only [eqn, eqs]

theorem outcome_stable (g : Game) (n : Nat) (hn : sizeOf g + 1 ≤ n) :
    outcome g n = outcome g (sizeOf g + 1) :=
  outcome_stable_aux (sizeOf g) g rfl n hn

theorem outcome_stable_between (g : Game) (m n : Nat)
    (hm : sizeOf g + 1 ≤ m) (hn : sizeOf g + 1 ≤ n) :
    outcome g m = outcome g n := by
  rw [outcome_stable g m hm, outcome_stable g n hn]

theorem outcome_eventually_constant (g : Game) :
    ∃ B, ∀ m n, B ≤ m → B ≤ n → outcome g m = outcome g n := by
  exact ⟨sizeOf g + 1, fun m n hm hn => outcome_stable_between g m n hm hn⟩

end TLMC8872
