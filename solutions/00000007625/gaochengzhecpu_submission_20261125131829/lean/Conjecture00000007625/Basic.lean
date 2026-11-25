/-
  Conjecture 00000007625 — Core Ring-Theoretic Foundations (Lean 4.19.0 Core)

  Defines unital associative rings, commutative rings, integral domains, fields,
  idempotents, orthogonal and primitive idempotent decompositions, central
  idempotents, left/right/two-sided ideals, minimal ideals, square-zero ideals,
  ring isomorphisms, finite matrix rings M_n(R), and exact finite cardinalities
  with constructive Pigeonhole uniqueness.
-/

namespace Conjecture00000007625

/-! ## 1. Bundled Algebraic Structures -/

structure UnitalRing (α : Type u) where
  zero : α
  one : α
  add : α → α → α
  neg : α → α
  mul : α → α → α
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  add_left_neg : ∀ a, add (neg a) a = zero
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)
  one_ne_zero : one ≠ zero

structure CommUnitalRing (α : Type u) extends UnitalRing α where
  mul_comm : ∀ a b, mul a b = mul b a

structure DomainRing (α : Type u) extends CommUnitalRing α where
  eq_zero_or_eq_zero_of_mul_eq_zero :
    ∀ a b, mul a b = zero → a = zero ∨ b = zero

structure FieldRing (α : Type u) extends CommUnitalRing α where
  inv : α → α
  mul_inv_cancel : ∀ a, a ≠ zero → mul a (inv a) = one

namespace UnitalRing

variable {α : Type u} (R : UnitalRing α)

def sub (a b : α) : α := R.add a (R.neg b)

theorem add_zero (a : α) : R.add a R.zero = a := by
  rw [R.add_comm, R.zero_add]

theorem add_right_neg (a : α) : R.add a (R.neg a) = R.zero := by
  rw [R.add_comm, R.add_left_neg]

theorem add_left_cancel {a b c : α} (h : R.add a b = R.add a c) : b = c := by
  have h1 : R.add (R.neg a) (R.add a b) = R.add (R.neg a) (R.add a c) :=
    congrArg (R.add (R.neg a)) h
  rw [← R.add_assoc, ← R.add_assoc, R.add_left_neg, R.zero_add, R.zero_add] at h1
  exact h1

theorem add_right_cancel {a b c : α} (h : R.add a c = R.add b c) : a = b := by
  apply R.add_left_cancel (a := c)
  rw [R.add_comm c a, h, R.add_comm b c]

theorem zero_mul (a : α) : R.mul R.zero a = R.zero := by
  apply R.add_left_cancel (a := R.mul R.zero a)
  rw [← R.right_distrib, R.zero_add, R.add_zero]

theorem mul_zero (a : α) : R.mul a R.zero = R.zero := by
  apply R.add_left_cancel (a := R.mul a R.zero)
  rw [← R.left_distrib, R.zero_add, R.add_zero]

theorem neg_eq_of_add_eq_zero {a b : α} (h : R.add a b = R.zero) : R.neg a = b := by
  apply R.add_left_cancel (a := a)
  rw [R.add_right_neg, h]

theorem neg_zero : R.neg R.zero = R.zero :=
  R.neg_eq_of_add_eq_zero (R.zero_add R.zero)

theorem neg_neg (a : α) : R.neg (R.neg a) = a :=
  R.neg_eq_of_add_eq_zero (R.add_left_neg a)

theorem neg_add (a b : α) : R.neg (R.add a b) = R.add (R.neg a) (R.neg b) := by
  apply R.neg_eq_of_add_eq_zero
  calc
    R.add (R.add a b) (R.add (R.neg a) (R.neg b))
      = R.add a (R.add b (R.add (R.neg b) (R.neg a))) := by
          rw [R.add_comm (R.neg a) (R.neg b), R.add_assoc]
    _ = R.add a (R.add (R.add b (R.neg b)) (R.neg a)) := by
          rw [R.add_assoc b (R.neg b) (R.neg a)]
    _ = R.zero := by
          rw [R.add_right_neg, R.zero_add, R.add_right_neg]

theorem neg_mul (a b : α) : R.mul (R.neg a) b = R.neg (R.mul a b) := by
  symm
  apply R.neg_eq_of_add_eq_zero
  rw [← R.right_distrib, R.add_right_neg, R.zero_mul]

theorem mul_neg (a b : α) : R.mul a (R.neg b) = R.neg (R.mul a b) := by
  symm
  apply R.neg_eq_of_add_eq_zero
  rw [← R.left_distrib, R.add_right_neg, R.mul_zero]

theorem sub_self (a : α) : R.sub a a = R.zero :=
  R.add_right_neg a

theorem sub_eq_zero {a b : α} : R.sub a b = R.zero ↔ a = b := by
  constructor
  · intro h
    apply R.add_right_cancel (c := R.neg b)
    calc
      R.add a (R.neg b) = R.zero := h
      _ = R.add b (R.neg b) := (R.add_right_neg b).symm
  · intro h
    subst h
    exact R.sub_self a

theorem add_sub_cancel_left (a b : α) : R.add a (R.sub b a) = b := by
  calc
    R.add a (R.add b (R.neg a)) = R.add b (R.add a (R.neg a)) := by
      rw [← R.add_assoc, R.add_comm a b, R.add_assoc]
    _ = b := by rw [R.add_right_neg, R.add_zero]

theorem sub_add_cancel (a b : α) : R.add (R.sub a b) b = a := by
  rw [R.add_comm, R.add_sub_cancel_left]

theorem mul_sub (a b c : α) : R.mul a (R.sub b c) = R.sub (R.mul a b) (R.mul a c) := by
  unfold sub
  rw [R.left_distrib, R.mul_neg]

theorem sub_mul (a b c : α) : R.mul (R.sub a b) c = R.sub (R.mul a c) (R.mul b c) := by
  unfold sub
  rw [R.right_distrib, R.neg_mul]

end UnitalRing

namespace FieldRing

def toDomainRing {α : Type u} (K : FieldRing α) : DomainRing α :=
  { K.toCommUnitalRing with
    eq_zero_or_eq_zero_of_mul_eq_zero := by
      intro a b hab
      by_cases ha : a = K.zero
      · exact Or.inl ha
      · right
        have h1 : K.mul (K.inv a) (K.mul a b) = K.mul (K.inv a) K.zero :=
          congrArg (K.mul (K.inv a)) hab
        rw [← K.mul_assoc, K.mul_comm (K.inv a) a, K.mul_inv_cancel a ha,
            K.one_mul, K.toUnitalRing.mul_zero] at h1
        exact h1 }

end FieldRing

/-! ## 2. Finite Sums in a Unital Ring -/

def finSum {α : Type u} (R : UnitalRing α) : (n : Nat) → (Fin n → α) → α
  | 0, _ => R.zero
  | n + 1, f => R.add (f ⟨0, Nat.zero_lt_succ n⟩) (finSum R n (fun i => f i.succ))

theorem finSum_congr {α : Type u} (R : UnitalRing α) {n : Nat}
    {f g : Fin n → α} (h : ∀ i, f i = g i) : finSum R n f = finSum R n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSum]
    rw [h ⟨0, Nat.zero_lt_succ n⟩, ih (fun i => h i.succ)]

theorem finSum_zero_const {α : Type u} (R : UnitalRing α) (n : Nat) :
    finSum R n (fun _ => R.zero) = R.zero := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSum]
    rw [ih, R.zero_add]

theorem finSum_add {α : Type u} (R : UnitalRing α) (n : Nat) (f g : Fin n → α) :
    finSum R n (fun i => R.add (f i) (g i)) = R.add (finSum R n f) (finSum R n g) := by
  induction n with
  | zero => symm; exact R.zero_add R.zero
  | succ n ih =>
    simp only [finSum]
    rw [ih]
    calc
      R.add (R.add (f ⟨0, Nat.zero_lt_succ n⟩) (g ⟨0, Nat.zero_lt_succ n⟩))
            (R.add (finSum R n (fun i => f i.succ)) (finSum R n (fun i => g i.succ)))
        = R.add (f ⟨0, Nat.zero_lt_succ n⟩)
            (R.add (g ⟨0, Nat.zero_lt_succ n⟩)
              (R.add (finSum R n (fun i => f i.succ)) (finSum R n (fun i => g i.succ)))) := by
            rw [R.add_assoc]
      _ = R.add (f ⟨0, Nat.zero_lt_succ n⟩)
            (R.add (finSum R n (fun i => f i.succ))
              (R.add (g ⟨0, Nat.zero_lt_succ n⟩) (finSum R n (fun i => g i.succ)))) := by
            rw [← R.add_assoc (g _), R.add_comm (g _), R.add_assoc]
      _ = R.add (R.add (f ⟨0, Nat.zero_lt_succ n⟩) (finSum R n (fun i => f i.succ)))
            (R.add (g ⟨0, Nat.zero_lt_succ n⟩) (finSum R n (fun i => g i.succ))) := by
            rw [← R.add_assoc]

theorem mul_finSum {α : Type u} (R : UnitalRing α) (a : α) (n : Nat) (f : Fin n → α) :
    R.mul a (finSum R n f) = finSum R n (fun i => R.mul a (f i)) := by
  induction n with
  | zero => exact R.mul_zero a
  | succ n ih =>
    simp only [finSum]
    rw [R.left_distrib, ih]

theorem finSum_mul {α : Type u} (R : UnitalRing α) (n : Nat) (f : Fin n → α) (a : α) :
    R.mul (finSum R n f) a = finSum R n (fun i => R.mul (f i) a) := by
  induction n with
  | zero => exact R.zero_mul a
  | succ n ih =>
    simp only [finSum]
    rw [R.right_distrib, ih]

theorem finSum_comm {α : Type u} (R : UnitalRing α) (m n : Nat) (f : Fin m → Fin n → α) :
    finSum R m (fun i => finSum R n (fun j => f i j)) =
    finSum R n (fun j => finSum R m (fun i => f i j)) := by
  induction m with
  | zero =>
    symm
    exact finSum_zero_const R n
  | succ m ih =>
    simp only [finSum]
    rw [ih, ← finSum_add]

theorem finSum_single {α : Type u} (R : UnitalRing α) :
    ∀ {n : Nat} (k : Fin n) (f : Fin n → α),
      (∀ i : Fin n, i ≠ k → f i = R.zero) → finSum R n f = f k
  | 0, k, _, _ => Fin.elim0 k
  | n + 1, ⟨0, h0⟩, f, hz => by
    simp only [finSum]
    have htail : finSum R n (fun i => f i.succ) = R.zero := by
      calc
        finSum R n (fun i => f i.succ) = finSum R n (fun _ => R.zero) := by
          apply finSum_congr
          intro i
          apply hz i.succ
          intro heq
          exact Nat.succ_ne_zero i.val (congrArg Fin.val heq)
        _ = R.zero := finSum_zero_const R n
    rw [htail, R.add_zero]
  | n + 1, ⟨k + 1, hk⟩, f, hz => by
    simp only [finSum]
    have hhead : f ⟨0, Nat.zero_lt_succ n⟩ = R.zero := by
      apply hz ⟨0, Nat.zero_lt_succ n⟩
      intro heq
      exact Nat.zero_ne_add_one k (congrArg Fin.val heq)
    have htail : finSum R n (fun i => f i.succ) = f ⟨k + 1, hk⟩ := by
      apply finSum_single R ⟨k, Nat.lt_of_succ_lt_succ hk⟩ (fun i => f i.succ)
      intro i hne
      apply hz i.succ
      intro heq
      apply hne
      exact Fin.ext (Nat.succ.inj (congrArg Fin.val heq))
    rw [hhead, R.zero_add, htail]

theorem exists_nonzero_of_finSum_ne_zero {α : Type u} (R : UnitalRing α) :
    ∀ {n : Nat} {f : Fin n → α}, finSum R n f ≠ R.zero → ∃ i : Fin n, f i ≠ R.zero
  | 0, _, h => absurd rfl h
  | n + 1, f, h => by
    simp only [finSum] at h
    by_cases h0 : f ⟨0, Nat.zero_lt_succ n⟩ = R.zero
    · rw [h0, R.zero_add] at h
      obtain ⟨i, hi⟩ := exists_nonzero_of_finSum_ne_zero R h
      exact ⟨i.succ, hi⟩
    · exact ⟨⟨0, Nat.zero_lt_succ n⟩, h0⟩

/-! ## 3. Idempotents, Decompositions, Center, and Ideals -/

def IsIdempotent {α : Type u} (R : UnitalRing α) (e : α) : Prop :=
  R.mul e e = e

def IsNonzeroIdempotent {α : Type u} (R : UnitalRing α) (e : α) : Prop :=
  IsIdempotent R e ∧ e ≠ R.zero

def AreOrthogonal {α : Type u} (R : UnitalRing α) (e f : α) : Prop :=
  R.mul e f = R.zero ∧ R.mul f e = R.zero

instance instDecidableIsIdempotent {α : Type u} [DecidableEq α]
    (R : UnitalRing α) (e : α) : Decidable (IsIdempotent R e) :=
  inferInstanceAs (Decidable (R.mul e e = e))

instance instDecidableAreOrthogonal {α : Type u} [DecidableEq α]
    (R : UnitalRing α) (e f : α) : Decidable (AreOrthogonal R e f) :=
  inferInstanceAs (Decidable (R.mul e f = R.zero ∧ R.mul f e = R.zero))

def decExistsFin : ∀ (n : Nat) (P : Fin n → Prop) [∀ i, Decidable (P i)],
    Decidable (∃ i : Fin n, P i)
  | 0, _, _ => isFalse (fun ⟨i, _⟩ => Fin.elim0 i)
  | n + 1, P, _ =>
    if h0 : P ⟨0, Nat.zero_lt_succ n⟩ then
      isTrue ⟨⟨0, Nat.zero_lt_succ n⟩, h0⟩
    else
      match decExistsFin n (fun i => P i.succ) with
      | isTrue hex => isTrue (let ⟨i, hi⟩ := hex; ⟨i.succ, hi⟩)
      | isFalse hno => isFalse (fun ⟨⟨k, hk⟩, hP⟩ =>
          match k with
          | 0 => h0 hP
          | m + 1 => hno ⟨⟨m, Nat.lt_of_succ_lt_succ hk⟩, hP⟩)

instance instDecidableExistsFin {n : Nat} (P : Fin n → Prop) [∀ i, Decidable (P i)] :
    Decidable (∃ i : Fin n, P i) :=
  decExistsFin n P

def IsCentral {α : Type u} (R : UnitalRing α) (z : α) : Prop :=
  ∀ x : α, R.mul z x = R.mul x z

def IsCentralIdempotent {α : Type u} (R : UnitalRing α) (z : α) : Prop :=
  IsIdempotent R z ∧ IsCentral R z

def IsPrimitiveIdempotent {α : Type u} (R : UnitalRing α) (e : α) : Prop :=
  IsNonzeroIdempotent R e ∧
    ¬ ∃ f g : α,
        IsNonzeroIdempotent R f ∧
        IsNonzeroIdempotent R g ∧
        AreOrthogonal R f g ∧
        R.add f g = e

def IsCentralPrimitiveIdempotent {α : Type u} (R : UnitalRing α) (c : α) : Prop :=
  IsCentralIdempotent R c ∧ c ≠ R.zero ∧
    ¬ ∃ f g : α,
        IsCentralIdempotent R f ∧ f ≠ R.zero ∧
        IsCentralIdempotent R g ∧ g ≠ R.zero ∧
        AreOrthogonal R f g ∧
        R.add f g = c

def IsOrthIdempDecomp {α : Type u} (R : UnitalRing α) (n : Nat) (e : Fin n → α) : Prop :=
  (∀ i : Fin n, IsNonzeroIdempotent R (e i)) ∧
  (∀ i j : Fin n, i ≠ j → AreOrthogonal R (e i) (e j)) ∧
  finSum R n e = R.one

def IsPrimOrthDecomp {α : Type u} (R : UnitalRing α) (n : Nat) (e : Fin n → α) : Prop :=
  IsOrthIdempDecomp R n e ∧ ∀ i : Fin n, IsPrimitiveIdempotent R (e i)

def IsCentralPrimDecomp {α : Type u} (R : UnitalRing α) (n : Nat) (c : Fin n → α) : Prop :=
  IsOrthIdempDecomp R n c ∧ ∀ i : Fin n, IsCentralPrimitiveIdempotent R (c i)

def IsUnordPrimOrthDecomp {α : Type u} (R : UnitalRing α) (S : α → Prop) : Prop :=
  ∃ (n : Nat) (e : Fin n → α),
    IsPrimOrthDecomp R n e ∧ S = (fun x => ∃ i : Fin n, x = e i)

def IsUnordCentralPrimDecomp {α : Type u} (R : UnitalRing α) (S : α → Prop) : Prop :=
  ∃ (n : Nat) (c : Fin n → α),
    IsCentralPrimDecomp R n c ∧ S = (fun x => ∃ i : Fin n, x = c i)

def IsAddSubgroup {α : Type u} (R : UnitalRing α) (I : α → Prop) : Prop :=
  I R.zero ∧
  (∀ a b : α, I a → I b → I (R.add a b)) ∧
  (∀ a : α, I a → I (R.neg a))

def IsLeftIdeal {α : Type u} (R : UnitalRing α) (L : α → Prop) : Prop :=
  IsAddSubgroup R L ∧ ∀ r x : α, L x → L (R.mul r x)

def IsRightIdeal {α : Type u} (R : UnitalRing α) (M : α → Prop) : Prop :=
  IsAddSubgroup R M ∧ ∀ x r : α, M x → M (R.mul x r)

def IsTwoSidedIdeal {α : Type u} (R : UnitalRing α) (I : α → Prop) : Prop :=
  IsLeftIdeal R I ∧ IsRightIdeal R I

def IsNonzeroPred {α : Type u} (R : UnitalRing α) (I : α → Prop) : Prop :=
  ∃ x : α, I x ∧ x ≠ R.zero

def IsMinimalTwoSidedIdeal {α : Type u} (R : UnitalRing α) (I : α → Prop) : Prop :=
  IsTwoSidedIdeal R I ∧ IsNonzeroPred R I ∧
    ∀ J : α → Prop,
      IsTwoSidedIdeal R J → IsNonzeroPred R J →
      (∀ x : α, J x → I x) → (∀ x : α, I x → J x)

def IsMinimalLeftIdeal {α : Type u} (R : UnitalRing α) (L : α → Prop) : Prop :=
  IsLeftIdeal R L ∧ IsNonzeroPred R L ∧
    ∀ M : α → Prop,
      IsLeftIdeal R M → IsNonzeroPred R M →
      (∀ x : α, M x → L x) → (∀ x : α, L x → M x)

def IsSquareZeroIdeal {α : Type u} (R : UnitalRing α) (I : α → Prop) : Prop :=
  ∀ x y : α, I x → I y → R.mul x y = R.zero

def IsSimpleRing {α : Type u} (R : UnitalRing α) : Prop :=
  ∀ I : α → Prop, IsTwoSidedIdeal R I → IsNonzeroPred R I → ∀ x : α, I x

structure RingIso {α : Type u} {β : Type v} (R : UnitalRing α) (S : UnitalRing β) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a : α, invFun (toFun a) = a
  right_inv : ∀ b : β, toFun (invFun b) = b
  map_zero : toFun R.zero = S.zero
  map_one : toFun R.one = S.one
  map_add : ∀ a b : α, toFun (R.add a b) = S.add (toFun a) (toFun b)
  map_mul : ∀ a b : α, toFun (R.mul a b) = S.mul (toFun a) (toFun b)

/-! ## 4. General Matrix Ring M_{n+1}(R) -/

def MatN (n : Nat) (α : Type u) : Type u :=
  Fin n → Fin n → α

def MatNRing {α : Type u} (n : Nat) [NeZero n] (R : UnitalRing α) : UnitalRing (MatN n α) where
  zero := fun _ _ => R.zero
  one := fun i j => if i = j then R.one else R.zero
  add := fun A B i j => R.add (A i j) (B i j)
  neg := fun A i j => R.neg (A i j)
  mul := fun A B i j => finSum R n (fun k => R.mul (A i k) (B k j))
  add_assoc := fun A B C => by
    funext i j; exact R.add_assoc (A i j) (B i j) (C i j)
  add_comm := fun A B => by
    funext i j; exact R.add_comm (A i j) (B i j)
  zero_add := fun A => by
    funext i j; exact R.zero_add (A i j)
  add_left_neg := fun A => by
    funext i j; exact R.add_left_neg (A i j)
  mul_assoc := fun A B C => by
    funext i j
    calc
      finSum R n (fun l => R.mul (finSum R n (fun k => R.mul (A i k) (B k l))) (C l j))
        = finSum R n (fun l => finSum R n (fun k => R.mul (R.mul (A i k) (B k l)) (C l j))) := by
            apply finSum_congr
            intro l
            exact finSum_mul R n (fun k => R.mul (A i k) (B k l)) (C l j)
      _ = finSum R n (fun k => finSum R n (fun l => R.mul (A i k) (R.mul (B k l) (C l j)))) := by
            rw [finSum_comm]
            apply finSum_congr; intro k
            apply finSum_congr; intro l
            exact R.mul_assoc (A i k) (B k l) (C l j)
      _ = finSum R n (fun k => R.mul (A i k) (finSum R n (fun l => R.mul (B k l) (C l j)))) := by
            apply finSum_congr; intro k
            symm
            exact mul_finSum R (A i k) n (fun l => R.mul (B k l) (C l j))
  one_mul := fun A => by
    funext i j
    rw [finSum_single R i]
    · simp [R.one_mul]
    · intro k hk
      have hik : i ≠ k := fun h => hk h.symm
      simp [hik, R.zero_mul]
  mul_one := fun A => by
    funext i j
    rw [finSum_single R j]
    · simp [R.mul_one]
    · intro k hk
      simp [hk, R.mul_zero]
  left_distrib := fun A B C => by
    funext i j
    rw [← finSum_add]
    apply finSum_congr; intro k
    exact R.left_distrib (A i k) (B k j) (C k j)
  right_distrib := fun A B C => by
    funext i j
    rw [← finSum_add]
    apply finSum_congr; intro k
    exact R.right_distrib (A i k) (B i k) (C k j)
  one_ne_zero := by
    intro h
    have i0 : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
    have h00 : (if i0 = i0 then R.one else R.zero) = R.zero :=
      congrFun (congrFun h i0) i0
    simp at h00
    exact R.one_ne_zero h00

/-! ## 5. Exact Finite Cardinality & Constructive Pigeonhole Uniqueness -/

def ExactCard {α : Type u} (P : α → Prop) (k : Nat) : Prop :=
  ∃ f : Fin k → α,
    (∀ i : Fin k, P (f i)) ∧
    (∀ i j : Fin k, f i = f j → i = j) ∧
    (∀ x : α, P x → ∃ i : Fin k, f i = x)

theorem fin_inj_le : ∀ {m n : Nat} (g : Fin m → Fin n),
    (∀ i j : Fin m, g i = g j → i = j) → m ≤ n
  | 0, n, _, _ => Nat.zero_le n
  | m + 1, 0, g, _ => Fin.elim0 (g ⟨0, Nat.zero_lt_succ m⟩)
  | m + 1, n + 1, g, hinj => by
    let i0 : Fin (m + 1) := ⟨0, Nat.zero_lt_succ m⟩
    let top : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
    have h_not_both : ∀ i : Fin m, g i.succ = top → (g i0).val < n := by
      intro i hi
      have hne : g i0 ≠ top := by
        intro h0
        have heq : i0 = i.succ := hinj i0 i.succ (h0.trans hi.symm)
        exact Nat.zero_ne_add_one i.val (congrArg Fin.val heq)
      exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (g i0).isLt)
        (fun hv => hne (Fin.ext hv))
    let g' : Fin m → Fin n := fun i =>
      if h : g i.succ = top then
        ⟨(g i0).val, h_not_both i h⟩
      else
        ⟨(g i.succ).val,
          Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (g i.succ).isLt)
            (fun hv => h (Fin.ext hv))⟩
    have hinj' : ∀ i j : Fin m, g' i = g' j → i = j := by
      intro i j hij
      dsimp [g'] at hij
      split at hij <;> rename_i hi <;> split at hij <;> rename_i hj
      · have hsucc : i.succ = j.succ := hinj i.succ j.succ (hi.trans hj.symm)
        exact Fin.ext (Nat.succ.inj (congrArg Fin.val hsucc))
      · have hval : (g i0).val = (g j.succ).val := congrArg (Fin.val : Fin n → Nat) hij
        have heq : i0 = j.succ := hinj i0 j.succ (Fin.ext hval)
        exact absurd (congrArg Fin.val heq) (Nat.zero_ne_add_one j.val)
      · have hval : (g i.succ).val = (g i0).val := congrArg (Fin.val : Fin n → Nat) hij
        have heq : i.succ = i0 := hinj i.succ i0 (Fin.ext hval)
        exact absurd (congrArg Fin.val heq).symm (Nat.zero_ne_add_one i.val)
      · have hval : (g i.succ).val = (g j.succ).val := congrArg (Fin.val : Fin n → Nat) hij
        have hsucc : i.succ = j.succ := hinj i.succ j.succ (Fin.ext hval)
        exact Fin.ext (Nat.succ.inj (congrArg Fin.val hsucc))
    exact Nat.succ_le_succ (fin_inj_le g' hinj')

theorem exactCard_le_of_subset {α : Type u} {P Q : α → Prop} {m n : Nat}
    (hP : ExactCard P m) (hQ : ExactCard Q n) (hsub : ∀ x, P x → Q x) : m ≤ n := by
  obtain ⟨f, hfP, hfinj, _⟩ := hP
  obtain ⟨g, _, _, hgsurj⟩ := hQ
  have hex : ∀ i : Fin m, ∃ j : Fin n, g j = f i :=
    fun i => hgsurj (f i) (hsub (f i) (hfP i))
  let φ : Fin m → Fin n := fun i => Classical.choose (hex i)
  have hφ : ∀ i : Fin m, g (φ i) = f i := fun i => Classical.choose_spec (hex i)
  apply fin_inj_le φ
  intro i j hij
  apply hfinj
  rw [← hφ i, ← hφ j, hij]

theorem exactCard_unique {α : Type u} {P : α → Prop} {m n : Nat}
    (hm : ExactCard P m) (hn : ExactCard P n) : m = n :=
  Nat.le_antisymm
    (exactCard_le_of_subset hm hn (fun _ h => h))
    (exactCard_le_of_subset hn hm (fun _ h => h))

theorem exactCard_disjoint_counts {α : Type u} {β : Type v}
    {P : α → Prop} {Q : β → Prop} {m n : Nat}
    (hP : ExactCard P m) (hQ : ExactCard Q n) (hne : m ≠ n) :
    ¬ ∃ k : Nat, ExactCard P k ∧ ExactCard Q k := by
  intro ⟨k, hkP, hkQ⟩
  exact hne ((exactCard_unique hP hkP).trans (exactCard_unique hkQ hQ))

/-! ## 6. General Helper Lemmas for Ideals and Simple Rings -/

theorem simpleRing_minimal_two_sided_iff {α : Type u} (R : UnitalRing α)
    (hS : IsSimpleRing R) (I : α → Prop) :
    IsMinimalTwoSidedIdeal R I ↔ I = (fun _ => True) := by
  constructor
  · intro ⟨hId, hNz, _⟩
    funext x
    exact propext ⟨fun _ => True.intro, fun _ => hS I hId hNz x⟩
  · intro hEq
    subst hEq
    refine ⟨?_, ⟨R.one, True.intro, R.one_ne_zero⟩, ?_⟩
    · exact ⟨⟨⟨True.intro, fun _ _ _ _ => True.intro, fun _ _ => True.intro⟩,
              fun _ _ _ => True.intro⟩,
             ⟨⟨True.intro, fun _ _ _ _ => True.intro, fun _ _ => True.intro⟩,
              fun _ _ _ => True.intro⟩⟩
    · intro J hJ hJnz _ x _
      exact hS J hJ hJnz x

theorem simpleRing_exactCard_minimal_two_sided_one {α : Type u} (R : UnitalRing α)
    (hS : IsSimpleRing R) :
    ExactCard (IsMinimalTwoSidedIdeal R) 1 := by
  refine ⟨fun _ => (fun _ => True), ?_, ?_, ?_⟩
  · intro _
    exact (simpleRing_minimal_two_sided_iff R hS (fun _ => True)).mpr rfl
  · intro i j _
    exact Fin.ext (by omega)
  · intro I hI
    exact ⟨⟨0, Nat.zero_lt_one⟩, ((simpleRing_minimal_two_sided_iff R hS I).mp hI).symm⟩

theorem ringIso_preserves_comm {α : Type u} {β : Type v}
    {R : UnitalRing α} {S : UnitalRing β} (φ : RingIso R S)
    (hcomm : ∀ x y : β, S.mul x y = S.mul y x) :
    ∀ a b : α, R.mul a b = R.mul b a := by
  intro a b
  have h1 : φ.toFun (R.mul a b) = φ.toFun (R.mul b a) := by
    rw [φ.map_mul, φ.map_mul, hcomm]
  have h2 := congrArg φ.invFun h1
  rw [φ.left_inv, φ.left_inv] at h2
  exact h2

theorem ringIso_preserves_no_zero_divisors {α : Type u} {β : Type v}
    {R : UnitalRing α} {S : UnitalRing β} (φ : RingIso R S)
    (hdom : ∀ a b : α, R.mul a b = R.zero → a = R.zero ∨ b = R.zero) :
    ∀ x y : β, S.mul x y = S.zero → x = S.zero ∨ y = S.zero := by
  intro x y hxy
  have hinv_zero : φ.invFun S.zero = R.zero := by
    rw [← φ.map_zero, φ.left_inv]
  have hmul : R.mul (φ.invFun x) (φ.invFun y) = R.zero := by
    have h1 : φ.toFun (R.mul (φ.invFun x) (φ.invFun y)) = S.zero := by
      rw [φ.map_mul, φ.right_inv, φ.right_inv, hxy]
    have h2 := congrArg φ.invFun h1
    rw [φ.left_inv, hinv_zero] at h2
    exact h2
  cases hdom (φ.invFun x) (φ.invFun y) hmul with
  | inl hx =>
    left
    rw [← φ.right_inv x, hx, φ.map_zero]
  | inr hy =>
    right
    rw [← φ.right_inv y, hy, φ.map_zero]

theorem matN_has_nonzero_nilpotent {α : Type u} (m : Nat) (R : UnitalRing α) :
    let M := MatNRing (m + 2) R
    ∃ A : MatN (m + 2) α, A ≠ M.zero ∧ M.mul A A = M.zero := by
  intro M
  let i0 : Fin (m + 2) := ⟨0, by omega⟩
  let i1 : Fin (m + 2) := ⟨1, by omega⟩
  let E01 : MatN (m + 2) α := fun i j => if i = i0 ∧ j = i1 then R.one else R.zero
  refine ⟨E01, ?_, ?_⟩
  · intro hzero
    have h01 : E01 i0 i1 = R.zero := congrFun (congrFun hzero i0) i1
    dsimp [E01] at h01
    exact R.one_ne_zero h01
  · funext i j
    dsimp [M, MatNRing]
    calc
      finSum R (m + 2) (fun k => R.mul (E01 i k) (E01 k j))
        = finSum R (m + 2) (fun _ => R.zero) := by
          apply finSum_congr
          intro k
          dsimp [E01]
          by_cases h1 : i = i0 ∧ k = i1
          · have hi10 : i1 ≠ i0 := fun heq => Nat.one_ne_zero (congrArg Fin.val heq)
            simp [h1.1, h1.2, hi10, R.mul_zero]
          · simp [h1, R.zero_mul]
      _ = R.zero := finSum_zero_const R (m + 2)

end Conjecture00000007625
