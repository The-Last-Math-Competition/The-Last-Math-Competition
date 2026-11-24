import Std

namespace C2075

/-- Models of the usual group signature and its equations. -/
structure GroupModel (A : Type) where
  one : A
  mul : A → A → A
  inv : A → A
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  inv_mul : ∀ a, mul (inv a) a = one
  mul_inv : ∀ a, mul a (inv a) = one

def integerGroup : GroupModel Int where
  one := 0
  mul := Int.add
  inv := Int.neg
  mul_assoc := Int.add_assoc
  one_mul := Int.zero_add
  mul_one := Int.add_zero
  inv_mul := fun a => by
    change -a + a = 0
    omega
  mul_inv := fun a => by
    change a + -a = 0
    omega

inductive Term where
  | generator
  | identity
  | inverse (t : Term)
  | product (left right : Term)

def evaluate {A : Type} (group : GroupModel A) (x : A) : Term → A
  | .generator => x
  | .identity => group.one
  | .inverse t => group.inv (evaluate group x t)
  | .product s t => group.mul (evaluate group x s) (evaluate group x t)

def occurrences : Term → Nat
  | .generator => 1
  | .identity => 0
  | .inverse t => occurrences t
  | .product s t => occurrences s + occurrences t

/-- Equal unary morphisms have equal values in every group on every input. -/
def SameUnaryMorphism (s t : Term) : Prop :=
  ∀ (A : Type) (group : GroupModel A) (x : A), evaluate group x s = evaluate group x t

def SameTupleMorphism {d : Nat} (s t : Fin d → Term) : Prop :=
  ∀ i, SameUnaryMorphism (s i) (t i)

private theorem evaluation_bounds (t : Term) :
    -(occurrences t : Int) ≤ evaluate integerGroup 1 t ∧
      evaluate integerGroup 1 t ≤ (occurrences t : Int) := by
  induction t with
  | generator => decide
  | identity => decide
  | inverse t ih =>
    obtain ⟨lower, upper⟩ := ih
    change -(occurrences t : Int) ≤ -evaluate integerGroup 1 t ∧
      -evaluate integerGroup 1 t ≤ (occurrences t : Int)
    constructor <;> omega
  | product s t ihs iht =>
    obtain ⟨lowerS, upperS⟩ := ihs
    obtain ⟨lowerT, upperT⟩ := iht
    change -((occurrences s + occurrences t : Nat) : Int) ≤
        evaluate integerGroup 1 s + evaluate integerGroup 1 t ∧
      evaluate integerGroup 1 s + evaluate integerGroup 1 t ≤
        ((occurrences s + occurrences t : Nat) : Int)
    constructor <;> omega

inductive Letter where
  | positive
  | negative

abbrev Word := List Letter

def wordTerm : Word → Term
  | [] => .identity
  | .positive :: w => .product .generator (wordTerm w)
  | .negative :: w => .product (.inverse .generator) (wordTerm w)

theorem word_occurrences (w : Word) : occurrences (wordTerm w) = w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a <;> simp [wordTerm, occurrences, ih, Nat.add_comm]

def powerWord (n : Nat) : Word := List.replicate n .positive

theorem powerWord_evaluation (n : Nat) : evaluate integerGroup 1 (wordTerm (powerWord n)) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 1 + evaluate integerGroup 1 (wordTerm (powerWord n)) = ((n + 1 : Nat) : Int)
    rw [ih]
    omega

def tupleCost {A : Type} (cost : A → Nat) : {d : Nat} → (Fin d → A) → Nat
  | 0, _ => 0
  | d + 1, terms => cost (terms 0) + tupleCost cost (fun i : Fin d => terms i.succ)

def powerWordTuple (d n : Nat) : Fin (d + 1) → Word :=
  Fin.cases (powerWord n) (fun _ => [])

def powerTermTuple (d n : Nat) (i : Fin (d + 1)) : Term :=
  wordTerm (powerWordTuple d n i)

theorem powerTuple_distinct {d m n : Nat}
    (same : SameTupleMorphism (powerTermTuple d m) (powerTermTuple d n)) : m = n := by
  have h := same 0 Int integerGroup 1
  change evaluate integerGroup 1 (wordTerm (powerWord m)) =
    evaluate integerGroup 1 (wordTerm (powerWord n)) at h
  rw [powerWord_evaluation, powerWord_evaluation] at h
  omega

theorem termTuple_cost_lower {d n : Nat} (terms : Fin (d + 1) → Term)
    (same : SameTupleMorphism terms (powerTermTuple d n)) :
    n ≤ tupleCost occurrences terms := by
  have evaluation := same 0 Int integerGroup 1
  change evaluate integerGroup 1 (terms 0) =
    evaluate integerGroup 1 (wordTerm (powerWord n)) at evaluation
  rw [powerWord_evaluation] at evaluation
  have upper := (evaluation_bounds (terms 0)).2
  have first_output : n ≤ occurrences (terms 0) := by omega
  exact Nat.le_trans first_output (Nat.le_add_right _ _)

private theorem termCosts_eq_wordCosts {d : Nat} (words : Fin d → Word) :
    tupleCost occurrences (fun i => wordTerm (words i)) = tupleCost List.length words := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [tupleCost, word_occurrences, ih]

theorem wordTuple_length_lower {d n : Nat} (words : Fin (d + 1) → Word)
    (same : SameTupleMorphism (fun i => wordTerm (words i)) (powerTermTuple d n)) :
    n ≤ tupleCost List.length words := by
  rw [← termCosts_eq_wordCosts]
  exact termTuple_cost_lower (fun i => wordTerm (words i)) same

private theorem emptyTuple_length (d : Nat) :
    tupleCost List.length (fun _ : Fin d => ([] : Word)) = 0 := by
  induction d with
  | zero => rfl
  | succ d ih => simp [tupleCost, ih]

theorem powerWordTuple_length (d n : Nat) :
    tupleCost List.length (powerWordTuple d n) = n := by
  simp [tupleCost, powerWordTuple, powerWord, emptyTuple_length]

theorem unbounded_at_each_positive_target (d bound : Nat) :
    ∃ target : Fin (d + 1) → Term, ∀ representative,
      SameTupleMorphism representative target → bound < tupleCost occurrences representative := by
  refine ⟨powerTermTuple d (bound + 1), ?_⟩
  intro representative same
  exact termTuple_cost_lower representative same

/-- There is no target-only eventual bound even for source arity one. -/
theorem no_eventual_target_bound :
    ¬ ∃ bound : Nat → Nat, ∃ d₀ : Nat,
      ∀ d, d₀ ≤ d → ∀ target : Fin d → Term, ∃ representative,
        SameTupleMorphism representative target ∧ tupleCost occurrences representative ≤ bound d := by
  rintro ⟨bound, d₀, claim⟩
  obtain ⟨target, unbounded⟩ := unbounded_at_each_positive_target d₀ (bound (d₀ + 1))
  obtain ⟨representative, same, short⟩ := claim (d₀ + 1) (Nat.le_succ d₀) target
  exact (Nat.not_lt_of_ge short) (unbounded representative same)

#print axioms no_eventual_target_bound

end C2075
