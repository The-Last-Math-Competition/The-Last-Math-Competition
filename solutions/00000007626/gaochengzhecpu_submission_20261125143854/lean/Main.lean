/-
Copyright (c) 2026. All rights reserved.
Conjecture 00000007626:
  "Definition: The connected-family structure of idempotent formulas.
   Conjecture: The connected-family spectrum of idempotents is finite;
   the bound of finiteness is the matrix-block count; and the bound of
   the matrix-block count is the isomorphism-class counting.
   (matrix-block-finite idempotent families)"

Complete Core Lean 4.19.0 formalization (zero external dependencies, zero sorry).
-/

namespace Conjecture00000007626

/-! ## Section 1: Core Algebraic Hierarchy & Concrete Witnesses -/

class AssocRing (R : Type u) extends Add R, Sub R, Neg R, Mul R where
  zero : R
  one : R
  sub_eq_add_neg : ∀ a b : R, a - b = a + -b
  add_assoc : ∀ a b c : R, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : R, a + b = b + a
  zero_add : ∀ a : R, zero + a = a
  add_zero : ∀ a : R, a + zero = a
  add_left_neg : ∀ a : R, -a + a = zero
  mul_assoc : ∀ a b c : R, (a * b) * c = a * (b * c)
  one_mul : ∀ a : R, one * a = a
  mul_one : ∀ a : R, a * one = a
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

instance (priority := low) instOfNatZeroAssocRing {R : Type u} [inst : AssocRing R] : OfNat R 0 where
  ofNat := inst.zero

instance (priority := low) instOfNatOneAssocRing {R : Type u} [inst : AssocRing R] : OfNat R 1 where
  ofNat := inst.one

class CommRing (R : Type u) extends AssocRing R where
  mul_comm : ∀ a b : R, a * b = b * a

class IntegralDomain (R : Type u) extends CommRing R where
  one_ne_zero : (1 : R) ≠ 0
  eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : R}, a * b = 0 → a = 0 ∨ b = 0

class Field (K : Type u) extends IntegralDomain K where
  inv : K → K
  mul_inv_cancel : ∀ {a : K}, a ≠ 0 → a * inv a = 1

namespace AssocRing

section Lemmas
variable {R : Type u} [AssocRing R]

theorem zero_add' (a : R) : (0 : R) + a = a := AssocRing.zero_add a
theorem add_zero' (a : R) : a + (0 : R) = a := AssocRing.add_zero a
theorem one_mul' (a : R) : (1 : R) * a = a := AssocRing.one_mul a
theorem mul_one' (a : R) : a * (1 : R) = a := AssocRing.mul_one a
theorem add_left_neg' (a : R) : -a + a = 0 := AssocRing.add_left_neg a

theorem add_right_neg (a : R) : a + -a = 0 := by
  rw [AssocRing.add_comm, add_left_neg']

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  have h1 : -a + (a + b) = -a + (a + c) := congrArg (fun x => -a + x) h
  rw [← AssocRing.add_assoc, ← AssocRing.add_assoc, add_left_neg', zero_add', zero_add'] at h1
  exact h1

theorem add_right_cancel {a b c : R} (h : a + c = b + c) : a = b := by
  apply add_left_cancel (a := c)
  rw [AssocRing.add_comm c a, AssocRing.add_comm c b]
  exact h

theorem eq_zero_of_add_self {a : R} (h : a + a = a) : a = 0 := by
  apply add_left_cancel (a := a)
  rw [h, add_zero']

theorem zero_mul (a : R) : (0 : R) * a = 0 := by
  apply eq_zero_of_add_self
  rw [← AssocRing.right_distrib, zero_add']

theorem mul_zero (a : R) : a * (0 : R) = 0 := by
  apply eq_zero_of_add_self
  rw [← AssocRing.left_distrib, zero_add']

theorem neg_zero : -(0 : R) = 0 := by
  apply add_right_cancel (c := (0 : R))
  rw [add_left_neg', zero_add']

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  apply add_left_cancel (a := a)
  rw [add_right_neg, h]

theorem neg_neg (a : R) : -(-a) = a := by
  symm
  apply add_left_cancel (a := -a)
  rw [add_left_neg', add_right_neg]

theorem neg_add (a b : R) : -(a + b) = -a + -b := by
  apply neg_eq_of_add_eq_zero
  calc
    (a + b) + (-a + -b) = a + (b + (-b + -a)) := by
      rw [AssocRing.add_comm (-a) (-b), AssocRing.add_assoc a b]
    _ = a + ((b + -b) + -a) := by rw [AssocRing.add_assoc b (-b) (-a)]
    _ = a + (0 + -a) := by rw [add_right_neg]
    _ = 0 := by rw [zero_add', add_right_neg]

theorem neg_mul (a b : R) : (-a) * b = -(a * b) := by
  symm
  apply neg_eq_of_add_eq_zero
  rw [← AssocRing.right_distrib, add_right_neg, zero_mul]

theorem mul_neg (a b : R) : a * (-b) = -(a * b) := by
  symm
  apply neg_eq_of_add_eq_zero
  rw [← AssocRing.left_distrib, add_right_neg, mul_zero]

theorem neg_mul_neg (a b : R) : (-a) * (-b) = a * b := by
  rw [neg_mul, mul_neg, neg_neg]

theorem sub_self (a : R) : a - a = 0 := by
  rw [AssocRing.sub_eq_add_neg, add_right_neg]

theorem sub_zero (a : R) : a - 0 = a := by
  rw [AssocRing.sub_eq_add_neg, neg_zero, add_zero']

theorem zero_sub (a : R) : (0 : R) - a = -a := by
  rw [AssocRing.sub_eq_add_neg, zero_add']

theorem sub_eq_zero {a b : R} : a - b = 0 ↔ a = b := by
  constructor
  · intro h
    apply add_right_cancel (c := -b)
    rw [← AssocRing.sub_eq_add_neg, h, add_right_neg]
  · intro h
    subst h
    exact sub_self a

theorem mul_sub (a b c : R) : a * (b - c) = a * b - a * c := by
  rw [AssocRing.sub_eq_add_neg, AssocRing.left_distrib, mul_neg, ← AssocRing.sub_eq_add_neg]

theorem sub_mul (a b c : R) : (a - b) * c = a * c - b * c := by
  rw [AssocRing.sub_eq_add_neg, AssocRing.right_distrib, neg_mul, ← AssocRing.sub_eq_add_neg]

def pow (a : R) : Nat → R
  | 0 => 1
  | n + 1 => pow a n * a

theorem pow_zero (a : R) : pow a 0 = 1 := rfl
theorem pow_succ (a : R) (n : Nat) : pow a (n + 1) = pow a n * a := rfl

theorem pow_comm_self (a : R) (n : Nat) : a * pow a n = pow a n * a := by
  induction n with
  | zero => rw [pow_zero, mul_one', one_mul']
  | succ k ih => rw [pow_succ, ← AssocRing.mul_assoc, ih]

theorem pow_neg_eq_zero_of_pow_eq_zero {a : R} {N : Nat} (h : pow a N = 0) :
    pow (-a) N = 0 := by
  suffices ∀ n : Nat, pow (-a) n = pow a n ∨ pow (-a) n = -(pow a n) by
    rcases this N with hp | hn
    · rw [hp, h]
    · rw [hn, h, neg_zero]
  intro n
  induction n with
  | zero => left; rfl
  | succ k ih =>
    rcases ih with hp | hn
    · right
      rw [pow_succ, pow_succ, hp, mul_neg]
    · left
      rw [pow_succ, pow_succ, hn, neg_mul_neg]

def natCast : Nat → R
  | 0 => 0
  | n + 1 => natCast n + 1

theorem natCast_zero : (natCast 0 : R) = 0 := rfl
theorem natCast_one : (natCast 1 : R) = 1 := by simp [natCast, zero_add']

theorem natCast_add (m n : Nat) : (natCast (m + n) : R) = natCast m + natCast n := by
  induction n with
  | zero => simp [natCast_zero, add_zero']
  | succ k ih =>
    change natCast (m + k) + 1 = natCast m + (natCast k + 1)
    rw [ih, AssocRing.add_assoc]

theorem natCast_comm (n : Nat) (x : R) : natCast n * x = x * natCast n := by
  induction n with
  | zero => rw [natCast_zero, zero_mul, mul_zero]
  | succ k ih =>
    change (natCast k + 1) * x = x * (natCast k + 1)
    rw [AssocRing.right_distrib, AssocRing.left_distrib, ih, one_mul', mul_one']

end Lemmas
end AssocRing

class TorsionFreeRing (R : Type u) extends CommRing R where
  one_ne_zero : (1 : R) ≠ 0
  eq_zero_of_natCast_mul_eq_zero :
    ∀ {k : Nat} {x : R}, 0 < k → AssocRing.natCast k * x = 0 → x = 0

theorem Field.inv_mul_cancel {K : Type u} [Field K] {a : K} (ha : a ≠ 0) :
    Field.inv a * a = 1 := by
  rw [CommRing.mul_comm, Field.mul_inv_cancel ha]

/-! ### Concrete Ring & Field Witnesses: `Int`, `F2` (char 2), and `QField` (char 0) -/

instance : IntegralDomain Int where
  zero := (0 : Int)
  one := (1 : Int)
  sub_eq_add_neg := fun a b => Int.sub_eq_add_neg
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  add_left_neg := Int.add_left_neg
  mul_assoc := Int.mul_assoc
  one_mul := Int.one_mul
  mul_one := Int.mul_one
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  mul_comm := Int.mul_comm
  one_ne_zero := by decide
  eq_zero_or_eq_zero_of_mul_eq_zero := fun {_ _} h => Int.mul_eq_zero.mp h

theorem int_natCast_eq (n : Nat) : (AssocRing.natCast n : Int) = Int.ofNat n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change (AssocRing.natCast k : Int) + 1 = Int.ofNat (k + 1)
    rw [ih]
    rfl

instance : TorsionFreeRing Int where
  one_ne_zero := by decide
  eq_zero_of_natCast_mul_eq_zero := by
    intro k x hk hmul
    rw [int_natCast_eq] at hmul
    have hk' : Int.ofNat k ≠ (0 : Int) := by
      intro hc
      cases k with
      | zero => omega
      | succ _ => cases hc
    rcases Int.mul_eq_zero.mp hmul with h1 | h2
    · exact False.elim (hk' h1)
    · exact h2

inductive F2 where
  | zero : F2
  | one : F2
  deriving DecidableEq

namespace F2

def add : F2 → F2 → F2
  | zero, x => x
  | x, zero => x
  | one, one => zero

def mul : F2 → F2 → F2
  | one, one => one
  | _, _ => zero

instance : Field F2 where
  add := add
  sub := add
  neg := id
  mul := mul
  zero := zero
  one := one
  inv := id
  sub_eq_add_neg := fun _ _ => rfl
  add_assoc := fun a b c => by cases a <;> cases b <;> cases c <;> rfl
  add_comm := fun a b => by cases a <;> cases b <;> rfl
  zero_add := fun a => by cases a <;> rfl
  add_zero := fun a => by cases a <;> rfl
  add_left_neg := fun a => by cases a <;> rfl
  mul_assoc := fun a b c => by cases a <;> cases b <;> cases c <;> rfl
  one_mul := fun a => by cases a <;> rfl
  mul_one := fun a => by cases a <;> rfl
  left_distrib := fun a b c => by cases a <;> cases b <;> cases c <;> rfl
  right_distrib := fun a b c => by cases a <;> cases b <;> cases c <;> rfl
  mul_comm := fun a b => by cases a <;> cases b <;> rfl
  one_ne_zero := by decide
  eq_zero_or_eq_zero_of_mul_eq_zero := fun {a b} h => by
    cases a <;> cases b
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · cases h
  mul_inv_cancel := fun {a} ha => by
    cases a
    · exact False.elim (ha rfl)
    · rfl

end F2

structure RatRep where
  num : Int
  den : Int
  den_pos : 0 < den

def RatRel (a b : RatRep) : Prop := a.num * b.den = b.num * a.den

theorem ratRel_refl (a : RatRep) : RatRel a a := rfl
theorem ratRel_symm {a b : RatRep} (h : RatRel a b) : RatRel b a := h.symm

theorem ratRel_trans {a b c : RatRep} (hab : RatRel a b) (hbc : RatRel b c) : RatRel a c := by
  unfold RatRel at *
  have hb_ne : b.den ≠ 0 := by have := b.den_pos; omega
  have h1 : (a.num * c.den) * b.den = (c.num * a.den) * b.den := by
    calc
      (a.num * c.den) * b.den = (a.num * b.den) * c.den := by
        rw [Int.mul_assoc, Int.mul_comm c.den b.den, ← Int.mul_assoc]
      _ = (b.num * a.den) * c.den := by rw [hab]
      _ = (b.num * c.den) * a.den := by
        rw [Int.mul_assoc, Int.mul_comm a.den c.den, ← Int.mul_assoc]
      _ = (c.num * b.den) * a.den := by rw [hbc]
      _ = (c.num * a.den) * b.den := by
        rw [Int.mul_assoc, Int.mul_comm b.den a.den, ← Int.mul_assoc]
  have hsub : (a.num * c.den - c.num * a.den) * b.den = 0 := by
    rw [Int.sub_mul, h1, Int.sub_self]
  rcases Int.mul_eq_zero.mp hsub with hdiff | hbd
  · omega
  · exact False.elim (hb_ne hbd)

instance ratSetoid : Setoid RatRep where
  r := RatRel
  iseqv := ⟨ratRel_refl, ratRel_symm, ratRel_trans⟩

abbrev QField : Type := Quotient ratSetoid

namespace QField

def mkQ (n d : Int) (hd : 0 < d) : QField := Quotient.mk ratSetoid ⟨n, d, hd⟩

def addRep (a b : RatRep) : RatRep :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den, Int.mul_pos a.den_pos b.den_pos⟩

def negRep (a : RatRep) : RatRep := ⟨-a.num, a.den, a.den_pos⟩

def mulRep (a b : RatRep) : RatRep :=
  ⟨a.num * b.num, a.den * b.den, Int.mul_pos a.den_pos b.den_pos⟩

def invRep (a : RatRep) : RatRep :=
  if hpos : 0 < a.num then ⟨a.den, a.num, hpos⟩
  else if hneg : a.num < 0 then ⟨-a.den, -a.num, by omega⟩
  else ⟨0, 1, by decide⟩

private theorem int_ring_add_rel {a₁ a₂ b₁ b₂ : RatRep} (ha : RatRel a₁ a₂) (hb : RatRel b₁ b₂) :
    RatRel (addRep a₁ b₁) (addRep a₂ b₂) := by
  unfold RatRel addRep at *
  dsimp only
  calc
    (a₁.num * b₁.den + b₁.num * a₁.den) * (a₂.den * b₂.den)
      = (a₁.num * a₂.den) * (b₁.den * b₂.den) + (b₁.num * b₂.den) * (a₁.den * a₂.den) := by
        rw [Int.add_mul]
        have l1 : (a₁.num * b₁.den) * (a₂.den * b₂.den) = (a₁.num * a₂.den) * (b₁.den * b₂.den) := by
          rw [Int.mul_assoc, ← Int.mul_assoc b₁.den, Int.mul_comm b₁.den a₂.den, Int.mul_assoc a₂.den, ← Int.mul_assoc]
        have l2 : (b₁.num * a₁.den) * (a₂.den * b₂.den) = (b₁.num * b₂.den) * (a₁.den * a₂.den) := by
          rw [Int.mul_assoc b₁.num, Int.mul_assoc b₁.num]
          apply congrArg (fun u => b₁.num * u)
          rw [Int.mul_comm a₂.den b₂.den, ← Int.mul_assoc a₁.den b₂.den a₂.den,
              Int.mul_comm a₁.den b₂.den, Int.mul_assoc b₂.den a₁.den a₂.den]
        rw [l1, l2]
    _ = (a₂.num * a₁.den) * (b₁.den * b₂.den) + (b₂.num * b₁.den) * (a₁.den * a₂.den) := by
        rw [ha, hb]
    _ = (a₂.num * b₂.den + b₂.num * a₂.den) * (a₁.den * b₁.den) := by
        rw [Int.add_mul]
        have r1 : (a₂.num * a₁.den) * (b₁.den * b₂.den) = (a₂.num * b₂.den) * (a₁.den * b₁.den) := by
          rw [Int.mul_assoc, Int.mul_comm b₁.den b₂.den, ← Int.mul_assoc a₁.den b₂.den, Int.mul_comm a₁.den b₂.den, Int.mul_assoc b₂.den, ← Int.mul_assoc]
        have r2 : (b₂.num * b₁.den) * (a₁.den * a₂.den) = (b₂.num * a₂.den) * (a₁.den * b₁.den) := by
          rw [Int.mul_assoc, ← Int.mul_assoc b₁.den, Int.mul_comm b₁.den a₁.den, Int.mul_assoc a₁.den, Int.mul_comm b₁.den a₂.den, ← Int.mul_assoc a₁.den a₂.den, Int.mul_comm a₁.den a₂.den, Int.mul_assoc a₂.den, ← Int.mul_assoc]
        rw [r1, r2]

private theorem int_ring_mul_rel {a₁ a₂ b₁ b₂ : RatRep} (ha : RatRel a₁ a₂) (hb : RatRel b₁ b₂) :
    RatRel (mulRep a₁ b₁) (mulRep a₂ b₂) := by
  unfold RatRel mulRep at *
  dsimp only
  calc
    (a₁.num * b₁.num) * (a₂.den * b₂.den)
      = (a₁.num * a₂.den) * (b₁.num * b₂.den) := by
        rw [Int.mul_assoc, ← Int.mul_assoc b₁.num, Int.mul_comm b₁.num a₂.den, Int.mul_assoc a₂.den, ← Int.mul_assoc]
    _ = (a₂.num * a₁.den) * (b₂.num * b₁.den) := by rw [ha, hb]
    _ = (a₂.num * b₂.num) * (a₁.den * b₁.den) := by
        rw [Int.mul_assoc, ← Int.mul_assoc a₁.den, Int.mul_comm a₁.den b₂.num, Int.mul_assoc b₂.num, ← Int.mul_assoc]

private theorem int_ring_neg_rel {a₁ a₂ : RatRep} (ha : RatRel a₁ a₂) :
    RatRel (negRep a₁) (negRep a₂) := by
  unfold RatRel negRep at *
  dsimp only
  rw [Int.neg_mul, Int.neg_mul, ha]

private theorem int_ring_inv_rel {a₁ a₂ : RatRep} (ha : RatRel a₁ a₂) :
    RatRel (invRep a₁) (invRep a₂) := by
  unfold RatRel invRep at *
  have hd1 : 0 < a₁.den := a₁.den_pos
  have hd2 : 0 < a₂.den := a₂.den_pos
  by_cases hp1 : 0 < a₁.num
  · have hp2 : 0 < a₂.num := by
      have hpos : 0 < a₁.num * a₂.den := Int.mul_pos hp1 hd2
      rw [ha] at hpos
      by_cases hc : 0 < a₂.num
      · exact hc
      · have hle : a₂.num ≤ 0 := by omega
        have hnp : a₂.num * a₁.den ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg hle (by omega)
        omega
    rw [dif_pos hp1, dif_pos hp2]
    dsimp only
    rw [Int.mul_comm a₁.den a₂.num, ← ha, Int.mul_comm]
  · by_cases hn1 : a₁.num < 0
    · have hn2 : a₂.num < 0 := by
        have hneg : a₁.num * a₂.den < 0 := Int.mul_neg_of_neg_of_pos hn1 hd2
        rw [ha] at hneg
        by_cases hc : a₂.num < 0
        · exact hc
        · have hge : 0 ≤ a₂.num := by omega
          have hnn : 0 ≤ a₂.num * a₁.den := Int.mul_nonneg hge (by omega)
          omega
      have hp2 : ¬ (0 < a₂.num) := by omega
      rw [dif_neg hp1, dif_pos hn1, dif_neg hp2, dif_pos hn2]
      dsimp only
      rw [Int.neg_mul_neg, Int.neg_mul_neg, Int.mul_comm a₁.den a₂.num, ← ha, Int.mul_comm]
    · have hz1 : a₁.num = 0 := by omega
      have hz2 : a₂.num = 0 := by
        rw [hz1, Int.zero_mul] at ha
        rcases Int.mul_eq_zero.mp ha.symm with h | h
        · exact h
        · omega
      have hp2 : ¬ (0 < a₂.num) := by omega
      have hn2 : ¬ (a₂.num < 0) := by omega
      rw [dif_neg hp1, dif_neg hn1, dif_neg hp2, dif_neg hn2]

def qAdd : QField → QField → QField :=
  Quotient.lift₂ (fun a b => Quotient.mk ratSetoid (addRep a b))
    (fun _ _ _ _ ha hb => Quotient.sound (int_ring_add_rel ha hb))

def qNeg : QField → QField :=
  Quotient.lift (fun a => Quotient.mk ratSetoid (negRep a))
    (fun _ _ ha => Quotient.sound (int_ring_neg_rel ha))

def qMul : QField → QField → QField :=
  Quotient.lift₂ (fun a b => Quotient.mk ratSetoid (mulRep a b))
    (fun _ _ _ _ ha hb => Quotient.sound (int_ring_mul_rel ha hb))

def qInv : QField → QField :=
  Quotient.lift (fun a => Quotient.mk ratSetoid (invRep a))
    (fun _ _ ha => Quotient.sound (int_ring_inv_rel ha))

theorem qMul_comm (x y : QField) : qMul x y = qMul y x := by
  refine Quotient.inductionOn₂ x y (fun a b => Quotient.sound ?_)
  change RatRel (mulRep a b) (mulRep b a)
  unfold RatRel mulRep
  dsimp only
  rw [Int.mul_comm a.num b.num, Int.mul_comm a.den b.den]

theorem qLeft_distrib (x y z : QField) : qMul x (qAdd y z) = qAdd (qMul x y) (qMul x z) := by
  refine Quotient.inductionOn₃ x y z (fun a b c => Quotient.sound ?_)
  change RatRel (mulRep a (addRep b c)) (addRep (mulRep a b) (mulRep a c))
  unfold RatRel mulRep addRep
  dsimp only
  rw [Int.mul_add, Int.add_mul, Int.add_mul]
  have t1 : (a.num * (b.num * c.den)) * ((a.den * b.den) * (a.den * c.den)) =
      ((a.num * b.num) * (a.den * c.den)) * (a.den * (b.den * c.den)) := by
    rw [← Int.mul_assoc a.num b.num c.den]
    rw [Int.mul_assoc (a.num * b.num), Int.mul_assoc (a.num * b.num)]
    apply congrArg (fun u => (a.num * b.num) * u)
    calc
      c.den * ((a.den * b.den) * (a.den * c.den))
        = c.den * ((a.den * c.den) * (a.den * b.den)) := by
          rw [Int.mul_comm (a.den * b.den) (a.den * c.den)]
      _ = (a.den * c.den) * (c.den * (a.den * b.den)) := by
          rw [← Int.mul_assoc c.den, Int.mul_comm c.den (a.den * c.den), Int.mul_assoc]
      _ = (a.den * c.den) * (a.den * (b.den * c.den)) := by
          rw [← Int.mul_assoc c.den a.den b.den, Int.mul_comm c.den a.den,
              Int.mul_assoc a.den c.den b.den, Int.mul_comm c.den b.den]
  have t2 : (a.num * (c.num * b.den)) * ((a.den * b.den) * (a.den * c.den)) =
      ((a.num * c.num) * (a.den * b.den)) * (a.den * (b.den * c.den)) := by
    rw [← Int.mul_assoc a.num c.num b.den]
    rw [Int.mul_assoc (a.num * c.num), Int.mul_assoc (a.num * c.num)]
    apply congrArg (fun u => (a.num * c.num) * u)
    calc
      b.den * ((a.den * b.den) * (a.den * c.den))
        = (a.den * b.den) * (b.den * (a.den * c.den)) := by
          rw [← Int.mul_assoc b.den, Int.mul_comm b.den (a.den * b.den), Int.mul_assoc]
      _ = (a.den * b.den) * (a.den * (b.den * c.den)) := by
          rw [← Int.mul_assoc b.den a.den c.den, Int.mul_comm b.den a.den, Int.mul_assoc a.den b.den c.den]
  rw [t1, t2]

instance : Field QField where
  add := qAdd
  sub := fun a b => qAdd a (qNeg b)
  neg := qNeg
  mul := qMul
  zero := mkQ 0 1 (by decide)
  one := mkQ 1 1 (by decide)
  inv := qInv
  sub_eq_add_neg := fun _ _ => rfl
  add_assoc := fun x y z => by
    refine Quotient.inductionOn₃ x y z (fun a b c => Quotient.sound ?_)
    change RatRel (addRep (addRep a b) c) (addRep a (addRep b c))
    unfold RatRel addRep
    dsimp only
    have num_eq :
        (a.num * b.den + b.num * a.den) * c.den + c.num * (a.den * b.den) =
        a.num * (b.den * c.den) + (b.num * c.den + c.num * b.den) * a.den := by
      rw [Int.add_mul (a.num * b.den) (b.num * a.den) c.den,
          Int.add_mul (b.num * c.den) (c.num * b.den) a.den, Int.add_assoc]
      have e1 : (a.num * b.den) * c.den = a.num * (b.den * c.den) := Int.mul_assoc _ _ _
      have e2 : (b.num * a.den) * c.den = (b.num * c.den) * a.den := by
        rw [Int.mul_assoc, Int.mul_comm a.den c.den, ← Int.mul_assoc]
      have e3 : c.num * (a.den * b.den) = (c.num * b.den) * a.den := by
        rw [Int.mul_comm a.den b.den, ← Int.mul_assoc]
      rw [e1, e2, e3]
    rw [num_eq, Int.mul_assoc a.den b.den c.den]
  add_comm := fun x y => by
    refine Quotient.inductionOn₂ x y (fun a b => Quotient.sound ?_)
    change RatRel (addRep a b) (addRep b a)
    unfold RatRel addRep
    dsimp only
    rw [Int.add_comm (a.num * b.den), Int.mul_comm a.den b.den]
  zero_add := fun x => by
    refine Quotient.inductionOn x (fun a => Quotient.sound ?_)
    change RatRel (addRep ⟨0, 1, by decide⟩ a) a
    unfold RatRel addRep
    dsimp only
    simp [Int.zero_mul, Int.one_mul, Int.zero_add]
  add_zero := fun x => by
    refine Quotient.inductionOn x (fun a => Quotient.sound ?_)
    change RatRel (addRep a ⟨0, 1, by decide⟩) a
    unfold RatRel addRep
    dsimp only
    simp [Int.zero_mul, Int.mul_one, Int.add_zero]
  add_left_neg := fun x => by
    refine Quotient.inductionOn x (fun a => Quotient.sound ?_)
    change RatRel (addRep (negRep a) a) ⟨0, 1, by decide⟩
    unfold RatRel addRep negRep
    dsimp only
    rw [Int.neg_mul, Int.add_left_neg, Int.zero_mul, Int.zero_mul]
  mul_assoc := fun x y z => by
    refine Quotient.inductionOn₃ x y z (fun a b c => Quotient.sound ?_)
    change RatRel (mulRep (mulRep a b) c) (mulRep a (mulRep b c))
    unfold RatRel mulRep
    dsimp only
    rw [Int.mul_assoc a.num, Int.mul_assoc a.den]
  one_mul := fun x => by
    refine Quotient.inductionOn x (fun a => Quotient.sound ?_)
    change RatRel (mulRep ⟨1, 1, by decide⟩ a) a
    unfold RatRel mulRep
    dsimp only
    rw [Int.one_mul, Int.one_mul]
  mul_one := fun x => by
    refine Quotient.inductionOn x (fun a => Quotient.sound ?_)
    change RatRel (mulRep a ⟨1, 1, by decide⟩) a
    unfold RatRel mulRep
    dsimp only
    rw [Int.mul_one, Int.mul_one]
  left_distrib := qLeft_distrib
  right_distrib := fun x y z => by
    change qMul (qAdd x y) z = qAdd (qMul x z) (qMul y z)
    rw [qMul_comm, qLeft_distrib, qMul_comm z x, qMul_comm z y]
  mul_comm := qMul_comm
  one_ne_zero := by
    intro h
    have hr : RatRel ⟨1, 1, by decide⟩ ⟨0, 1, by decide⟩ := Quotient.exact h
    unfold RatRel at hr
    dsimp only at hr
    omega
  eq_zero_or_eq_zero_of_mul_eq_zero := fun {x y} h => by
    refine Quotient.inductionOn₂ x y (fun a b => ?_) h
    intro hm
    have hr : RatRel (mulRep a b) ⟨0, 1, by decide⟩ := Quotient.exact hm
    unfold RatRel mulRep at hr
    dsimp only at hr
    rw [Int.mul_one, Int.zero_mul] at hr
    rcases Int.mul_eq_zero.mp hr with ha | hb
    · left
      apply Quotient.sound
      change RatRel a ⟨0, 1, by decide⟩
      unfold RatRel
      dsimp only
      rw [ha, Int.zero_mul, Int.zero_mul]
    · right
      apply Quotient.sound
      change RatRel b ⟨0, 1, by decide⟩
      unfold RatRel
      dsimp only
      rw [hb, Int.zero_mul, Int.zero_mul]
  mul_inv_cancel := fun {x} hx => by
    refine Quotient.inductionOn x (fun a => ?_) hx
    intro hne
    apply Quotient.sound
    change RatRel (mulRep a (invRep a)) ⟨1, 1, by decide⟩
    unfold RatRel mulRep invRep
    by_cases hp : 0 < a.num
    · rw [dif_pos hp]
      dsimp only
      rw [Int.mul_one, Int.one_mul, Int.mul_comm]
    · by_cases hn : a.num < 0
      · rw [dif_neg hp, dif_pos hn]
        dsimp only
        rw [Int.mul_neg, Int.mul_neg, Int.mul_one, Int.one_mul, Int.mul_comm a.num a.den]
      · exfalso
        apply hne
        apply Quotient.sound
        change RatRel a ⟨0, 1, by decide⟩
        unfold RatRel
        dsimp only
        have hz : a.num = 0 := by omega
        rw [hz, Int.zero_mul, Int.zero_mul]

theorem qNatCast_eq (n : Nat) : (AssocRing.natCast n : QField) = mkQ (Int.ofNat n) 1 (by decide) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change qAdd (AssocRing.natCast k) (mkQ 1 1 (by decide)) = mkQ (Int.ofNat (k + 1)) 1 (by decide)
    rw [ih]
    apply Quotient.sound
    change RatRel (addRep ⟨Int.ofNat k, 1, by decide⟩ ⟨1, 1, by decide⟩) ⟨Int.ofNat (k + 1), 1, by decide⟩
    unfold RatRel addRep
    dsimp only
    simp [Int.mul_one]

instance : TorsionFreeRing QField where
  one_ne_zero := IntegralDomain.one_ne_zero
  eq_zero_of_natCast_mul_eq_zero := by
    intro k x hk hmul
    rcases IntegralDomain.eq_zero_or_eq_zero_of_mul_eq_zero hmul with hcast | hx
    · exfalso
      rw [qNatCast_eq] at hcast
      have hr : RatRel ⟨Int.ofNat k, 1, by decide⟩ ⟨0, 1, by decide⟩ := Quotient.exact hcast
      unfold RatRel at hr
      dsimp only at hr
      cases k with
      | zero => omega
      | succ _ => cases hr
    · exact hx

end QField

/-! ## Section 2: Finite Sums & Polynomial Rings `Poly R` (`R[t]`) -/

def finSum {R : Type u} [AssocRing R] : Nat → (Nat → R) → R
  | 0, _ => 0
  | n + 1, f => finSum n f + f n

section FinSumLemmas
variable {R : Type u} [AssocRing R]

theorem finSum_zero_len (f : Nat → R) : finSum 0 f = 0 := rfl
theorem finSum_succ (n : Nat) (f : Nat → R) : finSum (n + 1) f = finSum n f + f n := rfl

theorem finSum_congr {n : Nat} {f g : Nat → R} (h : ∀ i, i < n → f i = g i) :
    finSum n f = finSum n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [finSum_succ, finSum_succ, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h k (Nat.lt_succ_self k)]

theorem finSum_eq_zero {n : Nat} {f : Nat → R} (h : ∀ i, i < n → f i = 0) :
    finSum n f = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [finSum_succ, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h k (Nat.lt_succ_self k), AssocRing.add_zero']

theorem finSum_add (n : Nat) (f g : Nat → R) :
    finSum n (fun i => f i + g i) = finSum n f + finSum n g := by
  induction n with
  | zero => simp [finSum_zero_len, AssocRing.add_zero']
  | succ k ih =>
    rw [finSum_succ, finSum_succ, finSum_succ, ih]
    rw [AssocRing.add_assoc (finSum k f) (finSum k g) (f k + g k)]
    rw [← AssocRing.add_assoc (finSum k g) (f k) (g k)]
    rw [AssocRing.add_comm (finSum k g) (f k)]
    rw [AssocRing.add_assoc (f k) (finSum k g) (g k)]
    rw [← AssocRing.add_assoc (finSum k f) (f k) (finSum k g + g k)]

theorem finSum_neg (n : Nat) (f : Nat → R) :
    finSum n (fun i => -(f i)) = -(finSum n f) := by
  induction n with
  | zero => simp [finSum_zero_len, AssocRing.neg_zero]
  | succ k ih =>
    rw [finSum_succ, finSum_succ, ih, AssocRing.neg_add]

theorem finSum_mul_left (a : R) (n : Nat) (f : Nat → R) :
    a * finSum n f = finSum n (fun i => a * f i) := by
  induction n with
  | zero => simp [finSum_zero_len, AssocRing.mul_zero]
  | succ k ih => rw [finSum_succ, finSum_succ, AssocRing.left_distrib, ih]

theorem finSum_mul_right (a : R) (n : Nat) (f : Nat → R) :
    finSum n f * a = finSum n (fun i => f i * a) := by
  induction n with
  | zero => simp [finSum_zero_len, AssocRing.zero_mul]
  | succ k ih => rw [finSum_succ, finSum_succ, AssocRing.right_distrib, ih]

theorem finSum_comm (m n : Nat) (h : Nat → Nat → R) :
    finSum m (fun i => finSum n (fun j => h i j)) =
    finSum n (fun j => finSum m (fun i => h i j)) := by
  induction m with
  | zero =>
    rw [finSum_zero_len]
    symm
    exact finSum_eq_zero (fun _ _ => rfl)
  | succ k ih =>
    rw [finSum_succ, ih, ← finSum_add]
    rfl

theorem finSum_extend {N M : Nat} {f : Nat → R} (hle : N ≤ M)
    (hz : ∀ i, N ≤ i → i < M → f i = 0) : finSum M f = finSum N f := by
  induction M with
  | zero =>
    have hN : N = 0 := by omega
    subst hN
    rfl
  | succ k ih =>
    by_cases hk : N = k + 1
    · subst hk
      rfl
    · have hle' : N ≤ k := by omega
      rw [finSum_succ, hz k hle' (Nat.lt_succ_self k), AssocRing.add_zero']
      exact ih hle' (fun i hi1 hi2 => hz i hi1 (Nat.lt_succ_of_lt hi2))

theorem finSum_single {n k : Nat} (hk : k < n) (f : Nat → R)
    (hz : ∀ i, i < n → i ≠ k → f i = 0) : finSum n f = f k := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [finSum_succ]
    by_cases hkm : k = m
    · subst hkm
      rw [finSum_eq_zero (fun i hi => hz i (Nat.lt_succ_of_lt hi) (by omega)), AssocRing.zero_add']
    · have hlt : k < m := by omega
      rw [ih hlt (fun i hi hne => hz i (Nat.lt_succ_of_lt hi) hne),
          hz m (Nat.lt_succ_self m) (fun h => hkm h.symm), AssocRing.add_zero']

theorem finSum_shift (i n : Nat) (h : Nat → R) :
    finSum (i + n) (fun m => if i ≤ m then h (m - i) else 0) = finSum n h := by
  induction n with
  | zero =>
    rw [Nat.add_zero, finSum_zero_len]
    exact finSum_eq_zero (fun m hm => if_neg (by omega))
  | succ k ih =>
    rw [Nat.add_succ, finSum_succ, finSum_succ, ← ih]
    have hle : i ≤ i + k := by omega
    have hsub : (i + k) - i = k := by omega
    rw [if_pos hle, hsub]

theorem finSum_shift_one (n : Nat) (g : Nat → R) :
    finSum (n + 1) g = g 0 + finSum n (fun i => g (i + 1)) := by
  induction n with
  | zero => simp [finSum_succ, finSum_zero_len, AssocRing.zero_add', AssocRing.add_zero']
  | succ k ih =>
    rw [finSum_succ (k + 1) g, ih, finSum_succ k (fun i => g (i + 1)), AssocRing.add_assoc]

theorem finSum_rev (n : Nat) (g : Nat → R) :
    finSum n g = finSum n (fun i => g (n - 1 - i)) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [finSum_succ, ih, finSum_shift_one k (fun i => g (k + 1 - 1 - i))]
    have h0 : k + 1 - 1 - 0 = k := by omega
    rw [h0, AssocRing.add_comm]
    apply congrArg (fun u => g k + u)
    apply finSum_congr
    intro i _
    have hi : k + 1 - 1 - (i + 1) = k - 1 - i := by omega
    rw [hi]

end FinSumLemmas

/-- Univariate polynomial ring `R[t]` over any unital associative ring `R`. -/
structure Poly (R : Type u) [AssocRing R] where
  coeff : Nat → R
  isBounded : ∃ N : Nat, ∀ k : Nat, N ≤ k → coeff k = 0

namespace Poly

section RingStructure
variable {R : Type u} [AssocRing R]

theorem ext {p q : Poly R} (h : ∀ k : Nat, p.coeff k = q.coeff k) : p = q := by
  cases p with
  | mk cp hp =>
    cases q with
    | mk cq hq =>
      have hc : cp = cq := funext h
      subst hc
      rfl

def zeroPoly : Poly R where
  coeff := fun _ => 0
  isBounded := ⟨0, fun _ _ => rfl⟩

def onePoly : Poly R where
  coeff := fun k => if k = 0 then 1 else 0
  isBounded := ⟨1, fun k hk => if_neg (by omega)⟩

def const (c : R) : Poly R where
  coeff := fun k => if k = 0 then c else 0
  isBounded := ⟨1, fun k hk => if_neg (by omega)⟩

def varT : Poly R where
  coeff := fun k => if k = 1 then 1 else 0
  isBounded := ⟨2, fun k hk => if_neg (by omega)⟩

def addPoly (p q : Poly R) : Poly R where
  coeff := fun k => p.coeff k + q.coeff k
  isBounded := by
    rcases p.isBounded with ⟨N₁, h₁⟩
    rcases q.isBounded with ⟨N₂, h₂⟩
    refine ⟨N₁ + N₂, fun k hk => ?_⟩
    rw [h₁ k (by omega), h₂ k (by omega), AssocRing.add_zero']

def negPoly (p : Poly R) : Poly R where
  coeff := fun k => -(p.coeff k)
  isBounded := by
    rcases p.isBounded with ⟨N, hN⟩
    refine ⟨N, fun k hk => ?_⟩
    rw [hN k hk, AssocRing.neg_zero]

def mulPoly (p q : Poly R) : Poly R where
  coeff := fun k => finSum (k + 1) (fun i => p.coeff i * q.coeff (k - i))
  isBounded := by
    rcases p.isBounded with ⟨N₁, h₁⟩
    rcases q.isBounded with ⟨N₂, h₂⟩
    refine ⟨N₁ + N₂, fun k hk => ?_⟩
    apply finSum_eq_zero
    intro i hi
    by_cases hi1 : N₁ ≤ i
    · rw [h₁ i hi1, AssocRing.zero_mul]
    · have hi2 : N₂ ≤ k - i := by omega
      rw [h₂ (k - i) hi2, AssocRing.mul_zero]

instance : AssocRing (Poly R) where
  add := addPoly
  sub := fun p q => addPoly p (negPoly q)
  neg := negPoly
  mul := mulPoly
  zero := zeroPoly
  one := onePoly
  sub_eq_add_neg := fun _ _ => rfl
  add_assoc := fun p q r => ext (fun k => AssocRing.add_assoc _ _ _)
  add_comm := fun p q => ext (fun k => AssocRing.add_comm _ _)
  zero_add := fun p => ext (fun k => AssocRing.zero_add' _)
  add_zero := fun p => ext (fun k => AssocRing.add_zero' _)
  add_left_neg := fun p => ext (fun k => AssocRing.add_left_neg' _)
  mul_assoc := fun p q r => by
    apply ext
    intro k
    change finSum (k + 1) (fun m => finSum (m + 1) (fun i => p.coeff i * q.coeff (m - i)) * r.coeff (k - m)) =
           finSum (k + 1) (fun i => p.coeff i * finSum (k - i + 1) (fun j => q.coeff j * r.coeff (k - i - j)))
    have step1 :
        finSum (k + 1) (fun m => finSum (m + 1) (fun i => p.coeff i * q.coeff (m - i)) * r.coeff (k - m)) =
        finSum (k + 1) (fun m => finSum (k + 1) (fun i =>
          if i ≤ m then p.coeff i * (q.coeff (m - i) * r.coeff (k - m)) else 0)) := by
      apply finSum_congr
      intro m hm
      rw [finSum_mul_right]
      symm
      rw [finSum_extend (N := m + 1) (by omega) (fun i hi1 _ => if_neg (by omega))]
      apply finSum_congr
      intro i hi
      rw [if_pos (by omega), AssocRing.mul_assoc]
    rw [step1, finSum_comm]
    apply finSum_congr
    intro i hi
    rw [finSum_mul_left]
    have hlen : k + 1 = i + (k - i + 1) := by omega
    rw [hlen]
    have step2 :
        finSum (i + (k - i + 1)) (fun m =>
          if i ≤ m then p.coeff i * (q.coeff (m - i) * r.coeff (k - m)) else 0) =
        finSum (i + (k - i + 1)) (fun m =>
          if i ≤ m then p.coeff i * (q.coeff (m - i) * r.coeff (k - i - (m - i))) else 0) := by
      apply finSum_congr
      intro m _
      by_cases him : i ≤ m
      · have hsub : k - m = k - i - (m - i) := by omega
        rw [if_pos him, if_pos him, hsub]
      · rw [if_neg him, if_neg him]
    rw [step2, finSum_shift i (k - i + 1) (fun j => p.coeff i * (q.coeff j * r.coeff (k - i - j)))]
  one_mul := fun p => by
    apply ext
    intro k
    change finSum (k + 1) (fun i => (if i = 0 then (1 : R) else 0) * p.coeff (k - i)) = p.coeff k
    rw [finSum_single (k := 0) (by omega)]
    · simp [AssocRing.one_mul']
    · intro i _ hne
      rw [if_neg hne, AssocRing.zero_mul]
  mul_one := fun p => by
    apply ext
    intro k
    change finSum (k + 1) (fun i => p.coeff i * (if k - i = 0 then (1 : R) else 0)) = p.coeff k
    rw [finSum_single (k := k) (by omega)]
    · simp [Nat.sub_self, AssocRing.mul_one']
    · intro i hi hne
      have hnz : k - i ≠ 0 := by omega
      rw [if_neg hnz, AssocRing.mul_zero]
  left_distrib := fun p q r => by
    apply ext
    intro k
    change finSum (k + 1) (fun i => p.coeff i * (q.coeff (k - i) + r.coeff (k - i))) =
           finSum (k + 1) (fun i => p.coeff i * q.coeff (k - i)) +
           finSum (k + 1) (fun i => p.coeff i * r.coeff (k - i))
    rw [← finSum_add]
    apply finSum_congr
    intro i _
    exact AssocRing.left_distrib _ _ _
  right_distrib := fun p q r => by
    apply ext
    intro k
    change finSum (k + 1) (fun i => (p.coeff i + q.coeff i) * r.coeff (k - i)) =
           finSum (k + 1) (fun i => p.coeff i * r.coeff (k - i)) +
           finSum (k + 1) (fun i => q.coeff i * r.coeff (k - i))
    rw [← finSum_add]
    apply finSum_congr
    intro i _
    exact AssocRing.right_distrib _ _ _

theorem coeff_zero (k : Nat) : (0 : Poly R).coeff k = 0 := rfl
theorem coeff_one (k : Nat) : (1 : Poly R).coeff k = if k = 0 then 1 else 0 := rfl
theorem coeff_const (c : R) (k : Nat) : (const c).coeff k = if k = 0 then c else 0 := rfl
theorem coeff_varT (k : Nat) : (varT : Poly R).coeff k = if k = 1 then 1 else 0 := rfl
theorem coeff_add (p q : Poly R) (k : Nat) : (p + q).coeff k = p.coeff k + q.coeff k := rfl
theorem coeff_neg (p : Poly R) (k : Nat) : (-p).coeff k = -(p.coeff k) := rfl
theorem coeff_sub (p q : Poly R) (k : Nat) : (p - q).coeff k = p.coeff k - q.coeff k := by
  change p.coeff k + -(q.coeff k) = p.coeff k - q.coeff k
  rw [AssocRing.sub_eq_add_neg]
theorem coeff_mul (p q : Poly R) (k : Nat) :
    (p * q).coeff k = finSum (k + 1) (fun i => p.coeff i * q.coeff (k - i)) := rfl

theorem const_zero : (const (0 : R)) = 0 := by
  apply ext; intro k; rw [coeff_const, coeff_zero]; split <;> rfl

theorem const_one : (const (1 : R)) = 1 := rfl

theorem const_add (a b : R) : const (a + b) = const a + const b := by
  apply ext; intro k; rw [coeff_const, coeff_add, coeff_const, coeff_const]
  by_cases hk : k = 0
  · subst hk; simp
  · rw [if_neg hk, if_neg hk, if_neg hk, AssocRing.add_zero']

theorem const_neg (a : R) : const (-a) = -(const a) := by
  apply ext; intro k; rw [coeff_const, coeff_neg, coeff_const]
  by_cases hk : k = 0
  · subst hk; simp
  · rw [if_neg hk, if_neg hk, AssocRing.neg_zero]

theorem const_mul_poly (a : R) (p : Poly R) (k : Nat) :
    (const a * p).coeff k = a * p.coeff k := by
  rw [coeff_mul, finSum_single (k := 0) (by omega)]
  · simp [coeff_const]
  · intro i _ hne
    rw [coeff_const, if_neg hne, AssocRing.zero_mul]

theorem poly_mul_const (p : Poly R) (a : R) (k : Nat) :
    (p * const a).coeff k = p.coeff k * a := by
  rw [coeff_mul, finSum_single (k := k) (by omega)]
  · simp [coeff_const, Nat.sub_self]
  · intro i hi hne
    have hnz : k - i ≠ 0 := by omega
    rw [coeff_const, if_neg hnz, AssocRing.mul_zero]

theorem const_mul (a b : R) : const (a * b) = const a * const b := by
  apply ext; intro k; rw [const_mul_poly, coeff_const, coeff_const]
  by_cases hk : k = 0
  · subst hk; simp
  · rw [if_neg hk, if_neg hk, AssocRing.mul_zero]

/-- Evaluation at `t = 0`: `eval0(∑ c_k t^k) = c_0`. -/
def eval0 (p : Poly R) : R := p.coeff 0

theorem eval0_zero : eval0 (0 : Poly R) = 0 := rfl
theorem eval0_one : eval0 (1 : Poly R) = 1 := rfl
theorem eval0_const (c : R) : eval0 (const c) = c := rfl
theorem eval0_varT : eval0 (varT : Poly R) = 0 := rfl
theorem eval0_add (p q : Poly R) : eval0 (p + q) = eval0 p + eval0 q := rfl
theorem eval0_neg (p : Poly R) : eval0 (-p) = -(eval0 p) := rfl

theorem eval0_mul (p q : Poly R) : eval0 (p * q) = eval0 p * eval0 q := by
  unfold eval0
  rw [coeff_mul, finSum_succ, finSum_zero_len, AssocRing.zero_add']

/-- Evaluation at `t = 1`: `eval1(∑ c_k t^k) = ∑ c_k` (well-defined over ANY `AssocRing R`). -/
noncomputable def eval1 (p : Poly R) : R :=
  finSum (Classical.choose p.isBounded) p.coeff

theorem eval1_eq_finSum (p : Poly R) {N : Nat} (hN : ∀ k, N ≤ k → p.coeff k = 0) :
    eval1 p = finSum N p.coeff := by
  unfold eval1
  let M := Classical.choose p.isBounded
  have hM : ∀ k, M ≤ k → p.coeff k = 0 := Classical.choose_spec p.isBounded
  change finSum M p.coeff = finSum N p.coeff
  by_cases hle : M ≤ N
  · symm
    exact finSum_extend hle (fun i hi _ => hM i hi)
  · exact finSum_extend (by omega) (fun i hi _ => hN i hi)

theorem eval1_zero : eval1 (0 : Poly R) = 0 := by
  rw [eval1_eq_finSum 0 (N := 0) (fun _ _ => rfl), finSum_zero_len]

theorem eval1_const (c : R) : eval1 (const c) = c := by
  rw [eval1_eq_finSum (const c) (N := 1) (fun k hk => if_neg (by omega))]
  rw [finSum_succ, finSum_zero_len, AssocRing.zero_add', coeff_const]
  simp

theorem eval1_one : eval1 (1 : Poly R) = 1 := eval1_const 1

theorem eval1_varT : eval1 (varT : Poly R) = 1 := by
  rw [eval1_eq_finSum varT (N := 2) (fun k hk => if_neg (by omega))]
  rw [finSum_succ, finSum_succ, finSum_zero_len, AssocRing.zero_add']
  rw [coeff_varT, if_neg (by decide), AssocRing.zero_add', coeff_varT]
  simp

theorem eval1_add (p q : Poly R) : eval1 (p + q) = eval1 p + eval1 q := by
  rcases p.isBounded with ⟨N₁, h₁⟩
  rcases q.isBounded with ⟨N₂, h₂⟩
  let N := N₁ + N₂
  have hp : ∀ k, N ≤ k → p.coeff k = 0 := fun k hk => h₁ k (by omega)
  have hq : ∀ k, N ≤ k → q.coeff k = 0 := fun k hk => h₂ k (by omega)
  have hpq : ∀ k, N ≤ k → (p + q).coeff k = 0 := by
    intro k hk; rw [coeff_add, hp k hk, hq k hk, AssocRing.add_zero']
  rw [eval1_eq_finSum (p + q) hpq, eval1_eq_finSum p hp, eval1_eq_finSum q hq, ← finSum_add]
  rfl

theorem eval1_neg (p : Poly R) : eval1 (-p) = -(eval1 p) := by
  rcases p.isBounded with ⟨N, hN⟩
  have hn : ∀ k, N ≤ k → (-p).coeff k = 0 := by
    intro k hk; rw [coeff_neg, hN k hk, AssocRing.neg_zero]
  rw [eval1_eq_finSum (-p) hn, eval1_eq_finSum p hN, ← finSum_neg]
  rfl

theorem eval1_mul (p q : Poly R) : eval1 (p * q) = eval1 p * eval1 q := by
  rcases p.isBounded with ⟨N₁, h₁⟩
  rcases q.isBounded with ⟨N₂, h₂⟩
  let M := N₁ + N₂
  have hp : ∀ k, M ≤ k → p.coeff k = 0 := fun k hk => h₁ k (by omega)
  have hq : ∀ k, M ≤ k → q.coeff k = 0 := fun k hk => h₂ k (by omega)
  have hpq : ∀ k, M ≤ k → (p * q).coeff k = 0 := by
    intro k hk
    rw [coeff_mul]
    apply finSum_eq_zero
    intro i hi
    by_cases hi1 : N₁ ≤ i
    · rw [h₁ i hi1, AssocRing.zero_mul]
    · rw [h₂ (k - i) (by omega), AssocRing.mul_zero]
  rw [eval1_eq_finSum (p * q) hpq, eval1_eq_finSum p hp, eval1_eq_finSum q hq]
  rw [finSum_mul_right, finSum_congr (fun i _ => finSum_mul_left (p.coeff i) M q.coeff)]
  have lhs_eq :
      finSum M (fun k => (p * q).coeff k) =
      finSum M (fun i => finSum M (fun j => if i + j < M then p.coeff i * q.coeff j else 0)) := by
    have s1 :
        finSum M (fun k => (p * q).coeff k) =
        finSum M (fun k => finSum M (fun i => if i ≤ k then p.coeff i * q.coeff (k - i) else 0)) := by
      apply finSum_congr
      intro k hk
      rw [coeff_mul]
      symm
      rw [finSum_extend (N := k + 1) (by omega) (fun i hi _ => if_neg (by omega))]
      exact finSum_congr (fun i hi => if_pos (by omega))
    rw [s1, finSum_comm]
    apply finSum_congr
    intro i hi
    have hM : M = i + (M - i) := by omega
    conv => lhs; rw [hM]
    rw [finSum_shift i (M - i) (fun j => p.coeff i * q.coeff j)]
    symm
    rw [finSum_extend (N := M - i) (by omega) (fun j hj _ => if_neg (by omega))]
    exact finSum_congr (fun j hj => if_pos (by omega))
  rw [lhs_eq]
  apply finSum_congr
  intro i _
  apply finSum_congr
  intro j _
  by_cases hij : i + j < M
  · rw [if_pos hij]
  · rw [if_neg hij]
    by_cases hi1 : N₁ ≤ i
    · rw [h₁ i hi1, AssocRing.zero_mul]
    · rw [h₂ j (by omega), AssocRing.mul_zero]

end RingStructure

section CommAndDomain
variable {K : Type u} [CommRing K]

instance : CommRing (Poly K) where
  mul_comm := fun p q => by
    apply ext
    intro k
    rw [coeff_mul, coeff_mul, finSum_rev (k + 1) (fun i => p.coeff i * q.coeff (k - i))]
    apply finSum_congr
    intro i hi
    have hsub1 : k + 1 - 1 - i = k - i := by omega
    have hsub2 : k - (k - i) = i := by omega
    rw [hsub1, hsub2, CommRing.mul_comm]

/-- Formal derivative `D(∑ c_k t^k) = ∑ (k+1) c_{k+1} t^k` on `K[t]`. -/
def deriv (p : Poly K) : Poly K where
  coeff := fun k => AssocRing.natCast (k + 1) * p.coeff (k + 1)
  isBounded := by
    rcases p.isBounded with ⟨N, hN⟩
    refine ⟨N, fun k hk => ?_⟩
    rw [hN (k + 1) (by omega), AssocRing.mul_zero]

theorem coeff_deriv (p : Poly K) (k : Nat) :
    (deriv p).coeff k = AssocRing.natCast (k + 1) * p.coeff (k + 1) := rfl

theorem deriv_zero : deriv (0 : Poly K) = 0 := by
  apply ext; intro k; rw [coeff_deriv, coeff_zero, AssocRing.mul_zero, coeff_zero]

theorem deriv_const (c : K) : deriv (const c) = 0 := by
  apply ext; intro k; rw [coeff_deriv, coeff_const, if_neg (by omega), AssocRing.mul_zero, coeff_zero]

theorem deriv_add (p q : Poly K) : deriv (p + q) = deriv p + deriv q := by
  apply ext; intro k
  rw [coeff_deriv, coeff_add, AssocRing.left_distrib, coeff_add, coeff_deriv, coeff_deriv]

/-- Leibniz rule `D(p * q) = D(p) * q + p * D(q)` on `K[t]`. -/
theorem deriv_mul (p q : Poly K) : deriv (p * q) = deriv p * q + p * deriv q := by
  apply ext
  intro k
  rw [coeff_deriv, coeff_mul, finSum_mul_left]
  have split_sum :
      finSum (k + 2) (fun i => AssocRing.natCast (k + 1) * (p.coeff i * q.coeff (k + 1 - i))) =
      finSum (k + 2) (fun i => (AssocRing.natCast i * p.coeff i) * q.coeff (k + 1 - i)) +
      finSum (k + 2) (fun i => p.coeff i * (AssocRing.natCast (k + 1 - i) * q.coeff (k + 1 - i))) := by
    rw [← finSum_add]
    apply finSum_congr
    intro i hi
    have hk_eq : AssocRing.natCast (k + 1) = (AssocRing.natCast i : K) + AssocRing.natCast (k + 1 - i) := by
      have hn : k + 1 = i + (k + 1 - i) := by omega
      conv => lhs; rw [hn]
      exact AssocRing.natCast_add i (k + 1 - i)
    rw [hk_eq, AssocRing.right_distrib]
    have s1 : AssocRing.natCast i * (p.coeff i * q.coeff (k + 1 - i)) =
        (AssocRing.natCast i * p.coeff i) * q.coeff (k + 1 - i) :=
      (AssocRing.mul_assoc _ _ _).symm
    have s2 : AssocRing.natCast (k + 1 - i) * (p.coeff i * q.coeff (k + 1 - i)) =
        p.coeff i * (AssocRing.natCast (k + 1 - i) * q.coeff (k + 1 - i)) := by
      rw [← AssocRing.mul_assoc, AssocRing.natCast_comm (k + 1 - i) (p.coeff i), AssocRing.mul_assoc]
    rw [s1, s2]
  rw [split_sum, coeff_add, coeff_mul, coeff_mul]
  have term1 :
      finSum (k + 2) (fun i => (AssocRing.natCast i * p.coeff i) * q.coeff (k + 1 - i)) =
      finSum (k + 1) (fun j => (deriv p).coeff j * q.coeff (k - j)) := by
    rw [finSum_shift_one (k + 1)]
    rw [AssocRing.natCast_zero, AssocRing.zero_mul, AssocRing.zero_mul, AssocRing.zero_add']
    apply finSum_congr
    intro j hj
    have hsub : k + 1 - (j + 1) = k - j := by omega
    rw [hsub, coeff_deriv]
  have term2 :
      finSum (k + 2) (fun i => p.coeff i * (AssocRing.natCast (k + 1 - i) * q.coeff (k + 1 - i))) =
      finSum (k + 1) (fun i => p.coeff i * (deriv q).coeff (k - i)) := by
    rw [finSum_succ (k + 1)]
    rw [Nat.sub_self, AssocRing.natCast_zero, AssocRing.zero_mul, AssocRing.mul_zero, AssocRing.add_zero']
    apply finSum_congr
    intro i hi
    have hsub : k + 1 - i = (k - i) + 1 := by omega
    rw [hsub, coeff_deriv]
  rw [term1, term2]

end CommAndDomain

theorem eq_const_of_deriv_eq_zero {K : Type u} [TorsionFreeRing K] {p : Poly K}
    (hd : deriv p = 0) : p = const (p.coeff 0) := by
  apply ext
  intro k
  cases k with
  | zero => simp [coeff_const]
  | succ m =>
    rw [coeff_const, if_neg (by omega)]
    have hm : (deriv p).coeff m = (0 : Poly K).coeff m := congrArg (fun q => q.coeff m) hd
    rw [coeff_deriv, coeff_zero] at hm
    exact TorsionFreeRing.eq_zero_of_natCast_mul_eq_zero (by omega) hm

private theorem exists_min_nonzero_upto {R : Type u} [AssocRing R] (f : Nat → R) :
    ∀ k : Nat, (∃ j, j ≤ k ∧ f j ≠ 0) → ∃ d : Nat, f d ≠ 0 ∧ ∀ i : Nat, i < d → f i = 0
  | 0, ⟨j, hj, hfj⟩ => by
    have hj0 : j = 0 := by omega
    subst hj0
    exact ⟨0, hfj, fun _ hi => by omega⟩
  | m + 1, ⟨j, hj, hfj⟩ => by
    by_cases hexm : ∃ j', j' ≤ m ∧ f j' ≠ 0
    · exact exists_min_nonzero_upto f m hexm
    · have hjm : j = m + 1 := by
        by_cases hle : j ≤ m
        · exact False.elim (hexm ⟨j, hle, hfj⟩)
        · omega
      subst hjm
      refine ⟨m + 1, hfj, fun i hi => ?_⟩
      by_cases hfi : f i = 0
      · exact hfi
      · exact False.elim (hexm ⟨i, by omega, hfi⟩)

private theorem exists_min_nonzero {R : Type u} [AssocRing R] {f : Nat → R}
    {n : Nat} (hn : f n ≠ 0) : ∃ d : Nat, f d ≠ 0 ∧ ∀ i : Nat, i < d → f i = 0 :=
  exists_min_nonzero_upto f n ⟨n, Nat.le_refl n, hn⟩

instance {K : Type u} [IntegralDomain K] : IntegralDomain (Poly K) where
  one_ne_zero := by
    intro h
    have h0 : (1 : Poly K).coeff 0 = (0 : Poly K).coeff 0 := congrArg (fun p => p.coeff 0) h
    exact IntegralDomain.one_ne_zero h0
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro p q hpq
    by_cases hp : p = 0
    · exact Or.inl hp
    · right
      by_cases hq : q = 0
      · exact hq
      · exfalso
        have hp_ex : ∃ n, p.coeff n ≠ 0 := by
          by_cases hex : ∃ n, p.coeff n ≠ 0
          · exact hex
          · exfalso; apply hp; apply ext; intro n
            by_cases hn : p.coeff n = 0
            · exact hn
            · exact False.elim (hex ⟨n, hn⟩)
        have hq_ex : ∃ m, q.coeff m ≠ 0 := by
          by_cases hex : ∃ m, q.coeff m ≠ 0
          · exact hex
          · exfalso; apply hq; apply ext; intro m
            by_cases hm : q.coeff m = 0
            · exact hm
            · exact False.elim (hex ⟨m, hm⟩)
        rcases hp_ex with ⟨n₀, hn₀⟩
        rcases hq_ex with ⟨m₀, hm₀⟩
        rcases exists_min_nonzero hn₀ with ⟨d₁, hd₁, hmin₁⟩
        rcases exists_min_nonzero hm₀ with ⟨d₂, hd₂, hmin₂⟩
        have hc : (p * q).coeff (d₁ + d₂) = 0 := by rw [hpq]; rfl
        rw [coeff_mul, finSum_single (k := d₁) (by omega)] at hc
        · simp only [Nat.add_sub_cancel_left] at hc
          rcases IntegralDomain.eq_zero_or_eq_zero_of_mul_eq_zero hc with h1 | h2
          · exact hd₁ h1
          · exact hd₂ h2
        · intro i hi hne
          by_cases hlt : i < d₁
          · rw [hmin₁ i hlt, AssocRing.zero_mul]
          · have hlt2 : d₁ + d₂ - i < d₂ := by omega
            rw [hmin₂ (d₁ + d₂ - i) hlt2, AssocRing.mul_zero]

/-- In `K[t]` over any integral domain `K`, the ONLY idempotent polynomials are `0` and `1`. -/
theorem idem_eq_zero_or_one_of_domain {D : Type u} [IntegralDomain D] {e : D}
    (he : e * e = e) : e = 0 ∨ e = 1 := by
  have h : e * (e - 1) = 0 := by
    rw [AssocRing.mul_sub, AssocRing.mul_one', he, AssocRing.sub_self]
  rcases IntegralDomain.eq_zero_or_eq_zero_of_mul_eq_zero h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (AssocRing.sub_eq_zero.mp h1)

end Poly

/-! ## Section 3: Idempotent Connected Families, Conjugacy & Projective Ideals -/

section IdempotentTheory
variable {A : Type u} [AssocRing A]

def IsIdem (e : A) : Prop := e * e = e

def IsProperIdem (e : A) : Prop := IsIdem e ∧ e ≠ 0 ∧ e ≠ 1

def IsCentral (z : A) : Prop := ∀ x : A, z * x = x * z

def IsCentralIdem (e : A) : Prop := IsIdem e ∧ IsCentral e

def IsPrimitiveIdem (e : A) : Prop :=
  IsIdem e ∧ e ≠ 0 ∧
  ∀ e₁ e₂ : A, IsIdem e₁ → IsIdem e₂ → e₁ * e₂ = 0 → e₂ * e₁ = 0 →
    e = e₁ + e₂ → e₁ = 0 ∨ e₂ = 0

theorem isIdem_zero : IsIdem (0 : A) := AssocRing.zero_mul 0
theorem isIdem_one : IsIdem (1 : A) := AssocRing.one_mul' 1

theorem isIdem_compl {e : A} (he : IsIdem e) : IsIdem (1 - e) := by
  unfold IsIdem at *
  rw [AssocRing.sub_mul, AssocRing.one_mul', AssocRing.mul_sub]
  rw [AssocRing.mul_one', he, AssocRing.sub_self, AssocRing.sub_zero]

/-- Elementary `𝔸¹`-polynomial family step between two idempotents in `A`. -/
def PolyStep (e₀ e₁ : A) : Prop :=
  ∃ E : Poly A, IsIdem E ∧ Poly.eval0 E = e₀ ∧ Poly.eval1 E = e₁

theorem polyStep_isIdem_left {e₀ e₁ : A} (h : PolyStep e₀ e₁) : IsIdem e₀ := by
  rcases h with ⟨E, hE, rfl, _⟩
  unfold IsIdem at *
  rw [← Poly.eval0_mul, hE]

theorem polyStep_isIdem_right {e₀ e₁ : A} (h : PolyStep e₀ e₁) : IsIdem e₁ := by
  rcases h with ⟨E, hE, _, rfl⟩
  unfold IsIdem at *
  rw [← Poly.eval1_mul, hE]

/-- Connected-family equivalence relation (`𝔸¹`-homotopy path connectedness) on `E(A)`. -/
inductive PolyConn : A → A → Prop where
  | refl {e : A} : IsIdem e → PolyConn e e
  | step {e₀ e₁ : A} : PolyStep e₀ e₁ → PolyConn e₀ e₁
  | symm {e₀ e₁ : A} : PolyConn e₀ e₁ → PolyConn e₁ e₀
  | trans {e₀ e₁ e₂ : A} : PolyConn e₀ e₁ → PolyConn e₁ e₂ → PolyConn e₀ e₂

theorem polyConn_isIdem {e₀ e₁ : A} (h : PolyConn e₀ e₁) : IsIdem e₀ ∧ IsIdem e₁ := by
  induction h with
  | refl he => exact ⟨he, he⟩
  | step hs => exact ⟨polyStep_isIdem_left hs, polyStep_isIdem_right hs⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih1 ih2 => exact ⟨ih1.1, ih2.2⟩

def IdemElem (A : Type u) [AssocRing A] : Type u := { e : A // IsIdem e }

def idemSetoid (A : Type u) [AssocRing A] : Setoid (IdemElem A) where
  r := fun x y => PolyConn x.1 y.1
  iseqv := ⟨fun x => PolyConn.refl x.2, PolyConn.symm, PolyConn.trans⟩

/-- The connected-family spectrum `π₀^{𝔸¹}(E(A))` of all idempotents in `A`. -/
def IdemSpectrum (A : Type u) [AssocRing A] : Type u := Quotient (idemSetoid A)

def ProperIdemElem (A : Type u) [AssocRing A] : Type u := { e : A // IsProperIdem e }

def properIdemSetoid (A : Type u) [AssocRing A] : Setoid (ProperIdemElem A) where
  r := fun x y => PolyConn x.1 y.1
  iseqv := ⟨fun x => PolyConn.refl x.2.1, PolyConn.symm, PolyConn.trans⟩

/-- The connected-family spectrum `π₀^{𝔸¹}(E°(A))` of nontrivial idempotents (`e ∉ {0, 1}`). -/
def ProperIdemSpectrum (A : Type u) [AssocRing A] : Type u := Quotient (properIdemSetoid A)

/-- Two-sided invertible pair and unit conjugacy `e₁ = u e₀ u⁻¹`. -/
def IsUnitPair (u v : A) : Prop := u * v = 1 ∧ v * u = 1

def UnitConj (e₀ e₁ : A) : Prop :=
  ∃ u v : A, IsUnitPair u v ∧ e₁ = u * e₀ * v

/-- Genuine left `A`-module isomorphism between cyclic projective left ideals `A e₀` and `A e₁`. -/
def LeftIdeal (A : Type u) [AssocRing A] (e : A) : Type u := { x : A // x * e = x }

structure LeftIdealIso (e₀ e₁ : A) where
  toFun : LeftIdeal A e₀ → LeftIdeal A e₁
  invFun : LeftIdeal A e₁ → LeftIdeal A e₀
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  map_add : ∀ x₁ x₂, (toFun ⟨x₁.1 + x₂.1, by rw [AssocRing.right_distrib, x₁.2, x₂.2]⟩).1 =
    (toFun x₁).1 + (toFun x₂).1
  map_smul : ∀ (a : A) x, (toFun ⟨a * x.1, by rw [AssocRing.mul_assoc, x.2]⟩).1 =
    a * (toFun x).1
  inv_smul : ∀ (a : A) y, (invFun ⟨a * y.1, by rw [AssocRing.mul_assoc, y.2]⟩).1 =
    a * (invFun y).1

/-- Murray–von Neumann algebraic equivalence of idempotents `A e₀ ≅_A A e₁`. -/
theorem leftIdealIso_iff_murrayVonNeumann {e₀ e₁ : A} (he₀ : IsIdem e₀) (he₁ : IsIdem e₁) :
    Nonempty (LeftIdealIso e₀ e₁) ↔
    ∃ u v : A, u * v = e₀ ∧ v * u = e₁ := by
  constructor
  · rintro ⟨iso⟩
    let x₀ : LeftIdeal A e₀ := ⟨e₀, he₀⟩
    let y₁ : LeftIdeal A e₁ := ⟨e₁, he₁⟩
    let u : A := (iso.toFun x₀).1
    let v : A := (iso.invFun y₁).1
    refine ⟨u, v, ?_, ?_⟩
    · have hu_mem : u * e₁ = u := (iso.toFun x₀).2
      have hsmul : (iso.invFun ⟨u * y₁.1, by rw [AssocRing.mul_assoc, y₁.2]⟩).1 = u * v :=
        iso.inv_smul u y₁
      have heq : (⟨u * y₁.1, by rw [AssocRing.mul_assoc, y₁.2]⟩ : LeftIdeal A e₁) = iso.toFun x₀ := by
        cases h : iso.toFun x₀ with
        | mk val prop =>
          have hu_val : u = val := by simp [u, h]
          apply Subtype.ext
          dsimp only [y₁]
          rw [← hu_val, hu_mem]
      rw [heq, iso.left_inv x₀] at hsmul
      exact hsmul.symm
    · have hv_mem : v * e₀ = v := (iso.invFun y₁).2
      have hsmul : (iso.toFun ⟨v * x₀.1, by rw [AssocRing.mul_assoc, x₀.2]⟩).1 = v * u :=
        iso.map_smul v x₀
      have heq : (⟨v * x₀.1, by rw [AssocRing.mul_assoc, x₀.2]⟩ : LeftIdeal A e₀) = iso.invFun y₁ := by
        cases h : iso.invFun y₁ with
        | mk val prop =>
          have hv_val : v = val := by simp [v, h]
          apply Subtype.ext
          dsimp only [x₀]
          rw [← hv_val, hv_mem]
      rw [heq, iso.right_inv y₁] at hsmul
      exact hsmul.symm
  · rintro ⟨u, v, huv, hvu⟩
    let u' := e₀ * u * e₁
    let v' := e₁ * v * e₀
    have hu'v' : u' * v' = e₀ := by
      dsimp only [u', v']
      calc
        (e₀ * u * e₁) * (e₁ * v * e₀) = e₀ * u * (e₁ * (e₁ * v)) * e₀ := by
          simp only [AssocRing.mul_assoc]
        _ = e₀ * u * (e₁ * v) * e₀ := by rw [← AssocRing.mul_assoc e₁ e₁ v, he₁]
        _ = e₀ * (u * (v * u) * v) * e₀ := by
          rw [← hvu]
          simp only [AssocRing.mul_assoc]
        _ = e₀ * ((u * v) * (u * v)) * e₀ := by simp only [AssocRing.mul_assoc]
        _ = e₀ := by rw [huv, he₀, he₀, he₀]
    have hv'u' : v' * u' = e₁ := by
      dsimp only [u', v']
      calc
        (e₁ * v * e₀) * (e₀ * u * e₁) = e₁ * v * (e₀ * (e₀ * u)) * e₁ := by
          simp only [AssocRing.mul_assoc]
        _ = e₁ * v * (e₀ * u) * e₁ := by rw [← AssocRing.mul_assoc e₀ e₀ u, he₀]
        _ = e₁ * (v * (u * v) * u) * e₁ := by
          rw [← huv]
          simp only [AssocRing.mul_assoc]
        _ = e₁ * ((v * u) * (v * u)) * e₁ := by simp only [AssocRing.mul_assoc]
        _ = e₁ := by rw [hvu, he₁, he₁, he₁]
    refine ⟨{
      toFun := fun x => ⟨x.1 * u', by
        dsimp only [u']; rw [AssocRing.mul_assoc, AssocRing.mul_assoc (e₀ * u) e₁ e₁, he₁, ← AssocRing.mul_assoc]⟩
      invFun := fun y => ⟨y.1 * v', by
        dsimp only [v']; rw [AssocRing.mul_assoc, AssocRing.mul_assoc (e₁ * v) e₀ e₀, he₀, ← AssocRing.mul_assoc]⟩
      left_inv := fun x => Subtype.ext (by dsimp only; rw [AssocRing.mul_assoc, hu'v', x.2])
      right_inv := fun y => Subtype.ext (by dsimp only; rw [AssocRing.mul_assoc, hv'u', y.2])
      map_add := fun x₁ x₂ => AssocRing.right_distrib x₁.1 x₂.1 u'
      map_smul := fun a x => AssocRing.mul_assoc a x.1 u'
      inv_smul := fun a y => AssocRing.mul_assoc a y.1 v'
    }⟩

theorem unitConj_imp_leftIdealIso {e₀ e₁ : A} (he₀ : IsIdem e₀) (he₁ : IsIdem e₁)
    (hc : UnitConj e₀ e₁) : Nonempty (LeftIdealIso e₀ e₁) := by
  rcases hc with ⟨u, v, ⟨huv, hvu⟩, rfl⟩
  rw [leftIdealIso_iff_murrayVonNeumann he₀ he₁]
  refine ⟨e₀ * v, u * e₀, ?_, ?_⟩
  · rw [AssocRing.mul_assoc, ← AssocRing.mul_assoc v u e₀, hvu, AssocRing.one_mul', he₀]
  · calc
      (u * e₀) * (e₀ * v) = u * (e₀ * e₀) * v := by simp only [AssocRing.mul_assoc]
      _ = u * e₀ * v := by rw [he₀]

end IdempotentTheory

/-! ## Section 4: Universal Nilpotent Homotopy Lifting & Non-Semisimple `T₂(K)` -/

section NilpotentLifting
variable {A : Type u} [AssocRing A]

/-- Universal intertwining element `u = e₁ e₀ + (1 - e₁)(1 - e₀)` for two idempotents. -/
def intertwineIdem (e₀ e₁ : A) : A :=
  e₁ * e₀ + (1 - e₁) * (1 - e₀)

theorem intertwineIdem_intertwines {e₀ e₁ : A} (he₀ : IsIdem e₀) (he₁ : IsIdem e₁) :
    intertwineIdem e₀ e₁ * e₀ = e₁ * intertwineIdem e₀ e₁ := by
  unfold intertwineIdem
  have h1e0 : (1 - e₀) * e₀ = 0 := by
    rw [AssocRing.sub_mul, AssocRing.one_mul', he₀, AssocRing.sub_self]
  have he11 : e₁ * (1 - e₁) = 0 := by
    rw [AssocRing.mul_sub, AssocRing.mul_one', he₁, AssocRing.sub_self]
  have lhs : (e₁ * e₀ + (1 - e₁) * (1 - e₀)) * e₀ = e₁ * e₀ := by
    rw [AssocRing.right_distrib, AssocRing.mul_assoc e₁ e₀ e₀, he₀]
    rw [AssocRing.mul_assoc (1 - e₁) (1 - e₀) e₀, h1e0, AssocRing.mul_zero, AssocRing.add_zero']
  have rhs : e₁ * (e₁ * e₀ + (1 - e₁) * (1 - e₀)) = e₁ * e₀ := by
    rw [AssocRing.left_distrib, ← AssocRing.mul_assoc e₁ e₁ e₀, he₁]
    rw [← AssocRing.mul_assoc e₁ (1 - e₁) (1 - e₀), he11, AssocRing.zero_mul, AssocRing.add_zero']
  rw [lhs, rhs]

theorem intertwineIdem_eq_one_add {e₀ e₁ : A} (he₁ : IsIdem e₁) :
    intertwineIdem e₀ e₁ = 1 + (e₁ - (1 - e₁)) * (e₀ - e₁) := by
  unfold intertwineIdem
  have h1 : e₁ * e₀ = e₁ + e₁ * (e₀ - e₁) := by
    rw [AssocRing.mul_sub, he₁, AssocRing.sub_eq_add_neg]
    rw [← AssocRing.add_assoc e₁ (e₁ * e₀) (-e₁), AssocRing.add_comm e₁ (e₁ * e₀)]
    rw [AssocRing.add_assoc (e₁ * e₀) e₁ (-e₁), AssocRing.add_right_neg, AssocRing.add_zero']
  have h2 : (1 - e₁) * (1 - e₀) = (1 - e₁) - (1 - e₁) * (e₀ - e₁) := by
    have hkill : (1 - e₁) * e₁ = 0 := by
      rw [AssocRing.sub_mul, AssocRing.one_mul', he₁, AssocRing.sub_self]
    rw [AssocRing.mul_sub, AssocRing.mul_sub, AssocRing.mul_one', hkill, AssocRing.sub_zero]
  have hsum : e₁ + (1 - e₁) = 1 := by
    rw [AssocRing.sub_eq_add_neg, AssocRing.add_comm 1 (-e₁), ← AssocRing.add_assoc,
        AssocRing.add_right_neg, AssocRing.zero_add']
  rw [h1, h2]
  let d := e₀ - e₁
  change (e₁ + e₁ * d) + ((1 - e₁) - (1 - e₁) * d) = 1 + (e₁ - (1 - e₁)) * d
  conv => lhs; arg 2; rw [AssocRing.sub_eq_add_neg]
  conv => rhs; arg 2; rw [AssocRing.sub_mul, AssocRing.sub_eq_add_neg]
  calc
    (e₁ + e₁ * d) + ((1 - e₁) + -((1 - e₁) * d))
      = e₁ + (e₁ * d + ((1 - e₁) + -((1 - e₁) * d))) := AssocRing.add_assoc _ _ _
    _ = e₁ + ((1 - e₁) + (e₁ * d + -((1 - e₁) * d))) := by
        rw [← AssocRing.add_assoc (e₁ * d), AssocRing.add_comm (e₁ * d) (1 - e₁), AssocRing.add_assoc]
    _ = (e₁ + (1 - e₁)) + (e₁ * d + -((1 - e₁) * d)) := (AssocRing.add_assoc _ _ _).symm
    _ = 1 + (e₁ * d + -((1 - e₁) * d)) := by rw [hsum]

/-- Explicit inverse in `A[t]` of `1 + w t` whenever `w` is nilpotent (`w^N = 0`). -/
def nilpotentLinUnit (w : A) : Poly A :=
  1 + Poly.const w * Poly.varT

def nilpotentLinInv (w : A) (N : Nat) : Poly A where
  coeff := fun m => if m < N then AssocRing.pow (-w) m else 0
  isBounded := ⟨N, fun m hm => if_neg (by omega)⟩

theorem coeff_nilpotentLinUnit (w : A) (k : Nat) :
    (nilpotentLinUnit w).coeff k = if k = 0 then 1 else if k = 1 then w else 0 := by
  unfold nilpotentLinUnit
  rw [Poly.coeff_add, Poly.coeff_one, Poly.const_mul_poly, Poly.coeff_varT]
  cases k with
  | zero => simp [AssocRing.mul_zero, AssocRing.add_zero']
  | succ m =>
    cases m with
    | zero => simp [AssocRing.mul_one', AssocRing.zero_add']
    | succ r => simp [AssocRing.mul_zero, AssocRing.add_zero']

theorem nilpotentLin_mul_right {w : A} {N : Nat} (hN_pos : 0 < N) (hw : AssocRing.pow w N = 0) :
    nilpotentLinUnit w * nilpotentLinInv w N = 1 := by
  have hnw : AssocRing.pow (-w) N = 0 := AssocRing.pow_neg_eq_zero_of_pow_eq_zero hw
  apply Poly.ext
  intro k
  rw [Poly.coeff_mul, Poly.coeff_one]
  cases k with
  | zero =>
    rw [finSum_succ, finSum_zero_len, AssocRing.zero_add', coeff_nilpotentLinUnit]
    simp [nilpotentLinInv, hN_pos, AssocRing.pow_zero, AssocRing.one_mul']
  | succ m =>
    rw [if_neg (by omega)]
    -- Only i = 0 and i = 1 in finSum (m + 2) can have nonzero nilpotentLinUnit coeff!
    rw [finSum_shift_one (m + 1), finSum_shift_one m]
    have hrest : finSum m (fun i =>
        (nilpotentLinUnit w).coeff (i + 2) * (nilpotentLinInv w N).coeff (m + 1 - (i + 2))) = 0 := by
      apply finSum_eq_zero
      intro i _
      rw [coeff_nilpotentLinUnit, if_neg (by omega), if_neg (by omega), AssocRing.zero_mul]
    rw [hrest, AssocRing.add_zero']
    rw [coeff_nilpotentLinUnit w 0, if_pos rfl, AssocRing.one_mul']
    rw [coeff_nilpotentLinUnit w 1, if_neg (by decide), if_pos rfl]
    simp only [Nat.sub_zero, Nat.add_sub_cancel]
    change (if m + 1 < N then AssocRing.pow (-w) (m + 1) else 0) +
           w * (if m < N then AssocRing.pow (-w) m else 0) = 0
    by_cases hm1 : m + 1 < N
    · rw [if_pos hm1, if_pos (by omega), AssocRing.pow_succ]
      have hcancel : w * AssocRing.pow (-w) m = -(AssocRing.pow (-w) m * (-w)) := by
        rw [← AssocRing.pow_comm_self (-w) m, AssocRing.neg_mul, AssocRing.neg_neg]
      rw [hcancel]
      exact AssocRing.add_right_neg _
    · rw [if_neg hm1]
      by_cases hm : m < N
      · have hm_eq : m + 1 = N := by omega
        rw [if_pos hm, AssocRing.zero_add']
        have hstep : w * AssocRing.pow (-w) m = -(AssocRing.pow (-w) (m + 1)) := by
          rw [AssocRing.pow_succ, ← AssocRing.pow_comm_self (-w) m, AssocRing.neg_mul]
          rw [AssocRing.neg_neg]
        rw [hstep, hm_eq, hnw, AssocRing.neg_zero]
      · rw [if_neg hm, AssocRing.mul_zero, AssocRing.add_zero']

theorem nilpotentLin_mul_left {w : A} {N : Nat} (hN_pos : 0 < N) (hw : AssocRing.pow w N = 0) :
    nilpotentLinInv w N * nilpotentLinUnit w = 1 := by
  have hnw : AssocRing.pow (-w) N = 0 := AssocRing.pow_neg_eq_zero_of_pow_eq_zero hw
  apply Poly.ext
  intro k
  rw [Poly.coeff_mul, Poly.coeff_one]
  cases k with
  | zero =>
    rw [finSum_succ, finSum_zero_len, AssocRing.zero_add', coeff_nilpotentLinUnit]
    simp [nilpotentLinInv, hN_pos, AssocRing.pow_zero, AssocRing.mul_one']
  | succ m =>
    rw [if_neg (by omega)]
    -- Split off top two indices i = m + 1 and i = m of finSum (m + 2)
    rw [finSum_succ (m + 1), finSum_succ m]
    have hlow : finSum m (fun i =>
        (nilpotentLinInv w N).coeff i * (nilpotentLinUnit w).coeff (m + 1 - i)) = 0 := by
      apply finSum_eq_zero
      intro i hi
      rw [coeff_nilpotentLinUnit, if_neg (by omega), if_neg (by omega), AssocRing.mul_zero]
    rw [hlow, AssocRing.zero_add']
    have hs1 : m + 1 - m = 1 := by omega
    have hs0 : m + 1 - (m + 1) = 0 := by omega
    rw [hs1, hs0]
    rw [coeff_nilpotentLinUnit w 1, if_neg (by decide), if_pos rfl]
    rw [coeff_nilpotentLinUnit w 0, if_pos rfl, AssocRing.mul_one']
    change (if m < N then AssocRing.pow (-w) m else 0) * w +
           (if m + 1 < N then AssocRing.pow (-w) (m + 1) else 0) = 0
    by_cases hm1 : m + 1 < N
    · rw [if_pos (by omega), if_pos hm1, AssocRing.pow_succ, AssocRing.mul_neg]
      exact AssocRing.add_right_neg _
    · rw [if_neg hm1, AssocRing.add_zero']
      by_cases hm : m < N
      · have hm_eq : m + 1 = N := by omega
        rw [if_pos hm]
        have hstep : AssocRing.pow (-w) m * w = -(AssocRing.pow (-w) (m + 1)) := by
          rw [AssocRing.pow_succ, AssocRing.mul_neg, AssocRing.neg_neg]
        rw [hstep, hm_eq, hnw, AssocRing.neg_zero]
      · rw [if_neg hm, AssocRing.zero_mul]

/-- Universal Nilpotent Homotopy Theorem: whenever two idempotents `e₀, e₁ ∈ E(A)` satisfy
    `((e₁ - (1 - e₁)) * (e₀ - e₁))^N = 0` (in particular, whenever `e₀ - e₁` lies in a nilpotent
    two-sided ideal `J` with `J^N = 0`), they are connected by an explicit single-step
    polynomial idempotent family `E(t) = (1 + t w) e₀ (1 + t w)⁻¹ ∈ E(A[t])`! -/
theorem nilpotent_diff_polyStep {e₀ e₁ : A} (he₀ : IsIdem e₀) (he₁ : IsIdem e₁)
    {N : Nat} (hN : 0 < N)
    (hw : AssocRing.pow ((e₁ - (1 - e₁)) * (e₀ - e₁)) N = 0) :
    PolyStep e₀ e₁ := by
  let w := (e₁ - (1 - e₁)) * (e₀ - e₁)
  let U := nilpotentLinUnit w
  let V := nilpotentLinInv w N
  have hUV : U * V = 1 := nilpotentLin_mul_right hN hw
  have hVU : V * U = 1 := nilpotentLin_mul_left hN hw
  let E : Poly A := U * Poly.const e₀ * V
  refine ⟨E, ?_, ?_, ?_⟩
  · unfold IsIdem
    dsimp only [E]
    calc
      (U * Poly.const e₀ * V) * (U * Poly.const e₀ * V)
        = U * Poly.const e₀ * ((V * U) * Poly.const e₀) * V := by
          simp only [AssocRing.mul_assoc]
      _ = U * (Poly.const e₀ * Poly.const e₀) * V := by
          rw [hVU, AssocRing.one_mul', AssocRing.mul_assoc U]
      _ = U * Poly.const e₀ * V := by rw [← Poly.const_mul, he₀]
  · dsimp only [E, U]
    rw [Poly.eval0_mul, Poly.eval0_mul, Poly.eval0_const]
    have hU0 : Poly.eval0 (nilpotentLinUnit w) = 1 := by
      unfold Poly.eval0; rw [coeff_nilpotentLinUnit, if_pos rfl]
    have hV0 : Poly.eval0 V = 1 := by
      unfold Poly.eval0; simp [V, nilpotentLinInv, hN, AssocRing.pow_zero]
    rw [hU0, hV0, AssocRing.one_mul', AssocRing.mul_one']
  · dsimp only [E]
    have hU1 : Poly.eval1 U = intertwineIdem e₀ e₁ := by
      dsimp only [U, nilpotentLinUnit]
      rw [Poly.eval1_add, Poly.eval1_one, Poly.eval1_mul, Poly.eval1_const, Poly.eval1_varT,
          AssocRing.mul_one']
      exact (intertwineIdem_eq_one_add he₁).symm
    have huv1 : Poly.eval1 U * Poly.eval1 V = 1 := by
      rw [← Poly.eval1_mul, hUV, Poly.eval1_one]
    rw [Poly.eval1_mul, Poly.eval1_mul, Poly.eval1_const, hU1]
    rw [intertwineIdem_intertwines he₀ he₁, AssocRing.mul_assoc, ← hU1, huv1, AssocRing.mul_one']

end NilpotentLifting

/-- Non-semisimple `2 × 2` upper-triangular matrix algebra `T₂(R)` (`[[a, b], [0, c]]`),
    whose Jacobson radical `J = {[[0, b], [0, 0]]}` satisfies `J² = 0` and `T₂(R)/J ≅ R × R`. -/
structure UpperTri2 (R : Type u) where
  a : R
  b : R
  c : R
  deriving DecidableEq

namespace UpperTri2

theorem ext {R : Type u} {x y : UpperTri2 R} (ha : x.a = y.a) (hb : x.b = y.b) (hc : x.c = y.c) :
    x = y := by
  cases x; cases y; subst ha; subst hb; subst hc; rfl

section Ring
variable {R : Type u} [AssocRing R]

instance : AssocRing (UpperTri2 R) where
  add := fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c⟩
  sub := fun x y => ⟨x.a - y.a, x.b - y.b, x.c - y.c⟩
  neg := fun x => ⟨-x.a, -x.b, -x.c⟩
  mul := fun x y => ⟨x.a * y.a, x.a * y.b + x.b * y.c, x.c * y.c⟩
  zero := ⟨0, 0, 0⟩
  one := ⟨1, 0, 1⟩
  sub_eq_add_neg := fun x y => ext (AssocRing.sub_eq_add_neg _ _) (AssocRing.sub_eq_add_neg _ _) (AssocRing.sub_eq_add_neg _ _)
  add_assoc := fun x y z => ext (AssocRing.add_assoc _ _ _) (AssocRing.add_assoc _ _ _) (AssocRing.add_assoc _ _ _)
  add_comm := fun x y => ext (AssocRing.add_comm _ _) (AssocRing.add_comm _ _) (AssocRing.add_comm _ _)
  zero_add := fun x => ext (AssocRing.zero_add' _) (AssocRing.zero_add' _) (AssocRing.zero_add' _)
  add_zero := fun x => ext (AssocRing.add_zero' _) (AssocRing.add_zero' _) (AssocRing.add_zero' _)
  add_left_neg := fun x => ext (AssocRing.add_left_neg' _) (AssocRing.add_left_neg' _) (AssocRing.add_left_neg' _)
  mul_assoc := fun x y z => by
    apply ext
    · exact AssocRing.mul_assoc _ _ _
    · change (x.a * y.a) * z.b + (x.a * y.b + x.b * y.c) * z.c =
             x.a * (y.a * z.b + y.b * z.c) + x.b * (y.c * z.c)
      rw [AssocRing.right_distrib, AssocRing.left_distrib]
      rw [AssocRing.mul_assoc x.a y.a z.b, AssocRing.mul_assoc x.a y.b z.c, AssocRing.mul_assoc x.b y.c z.c]
      rw [AssocRing.add_assoc]
    · exact AssocRing.mul_assoc _ _ _
  one_mul := fun x => by
    apply ext
    · exact AssocRing.one_mul' _
    · change 1 * x.b + 0 * x.c = x.b
      rw [AssocRing.one_mul', AssocRing.zero_mul, AssocRing.add_zero']
    · exact AssocRing.one_mul' _
  mul_one := fun x => by
    apply ext
    · exact AssocRing.mul_one' _
    · change x.a * 0 + x.b * 1 = x.b
      rw [AssocRing.mul_zero, AssocRing.mul_one', AssocRing.zero_add']
    · exact AssocRing.mul_one' _
  left_distrib := fun x y z => by
    apply ext
    · exact AssocRing.left_distrib _ _ _
    · change x.a * (y.b + z.b) + x.b * (y.c + z.c) =
             (x.a * y.b + x.b * y.c) + (x.a * z.b + x.b * z.c)
      rw [AssocRing.left_distrib, AssocRing.left_distrib]
      rw [AssocRing.add_assoc (x.a * y.b) (x.a * z.b)]
      rw [← AssocRing.add_assoc (x.a * z.b) (x.b * y.c), AssocRing.add_comm (x.a * z.b) (x.b * y.c)]
      rw [AssocRing.add_assoc (x.b * y.c), ← AssocRing.add_assoc (x.a * y.b)]
    · exact AssocRing.left_distrib _ _ _
  right_distrib := fun x y z => by
    apply ext
    · exact AssocRing.right_distrib _ _ _
    · change (x.a + y.a) * z.b + (x.b + y.b) * z.c =
             (x.a * z.b + x.b * z.c) + (y.a * z.b + y.b * z.c)
      rw [AssocRing.right_distrib, AssocRing.right_distrib]
      rw [AssocRing.add_assoc (x.a * z.b) (y.a * z.b)]
      rw [← AssocRing.add_assoc (y.a * z.b) (x.b * z.c), AssocRing.add_comm (y.a * z.b) (x.b * z.c)]
      rw [AssocRing.add_assoc (x.b * z.c), ← AssocRing.add_assoc (x.a * z.b)]
    · exact AssocRing.right_distrib _ _ _

theorem pow2_eq_zero_of_diag_zero {x : UpperTri2 R} (ha : x.a = 0) (hc : x.c = 0) :
    AssocRing.pow x 2 = 0 := by
  change (1 * x) * x = 0
  rw [AssocRing.one_mul']
  apply ext
  · change x.a * x.a = 0; rw [ha, AssocRing.zero_mul]
  · change x.a * x.b + x.b * x.c = 0
    rw [ha, hc, AssocRing.zero_mul, AssocRing.mul_zero, AssocRing.add_zero']
  · change x.c * x.c = 0; rw [hc, AssocRing.zero_mul]

def projA (P : Poly (UpperTri2 R)) : Poly R where
  coeff := fun k => (P.coeff k).a
  isBounded := by
    rcases P.isBounded with ⟨N, hN⟩
    refine ⟨N, fun k hk => ?_⟩
    rw [hN k hk]; rfl

def projC (P : Poly (UpperTri2 R)) : Poly R where
  coeff := fun k => (P.coeff k).c
  isBounded := by
    rcases P.isBounded with ⟨N, hN⟩
    refine ⟨N, fun k hk => ?_⟩
    rw [hN k hk]; rfl

theorem projA_mul (P Q : Poly (UpperTri2 R)) : projA (P * Q) = projA P * projA Q := by
  apply Poly.ext
  intro k
  change (finSum (k + 1) (fun i => P.coeff i * Q.coeff (k - i))).a =
         finSum (k + 1) (fun i => (P.coeff i).a * (Q.coeff (k - i)).a)
  have hsum : ∀ n (g : Nat → UpperTri2 R), (finSum n g).a = finSum n (fun i => (g i).a) := by
    intro n g
    induction n with
    | zero => rfl
    | succ m ih => rw [finSum_succ, finSum_succ, ← ih]; rfl
  rw [hsum]
  rfl

theorem projC_mul (P Q : Poly (UpperTri2 R)) : projC (P * Q) = projC P * projC Q := by
  apply Poly.ext
  intro k
  have hsum : ∀ n (g : Nat → UpperTri2 R), (finSum n g).c = finSum n (fun i => (g i).c) := by
    intro n g
    induction n with
    | zero => rfl
    | succ m ih => rw [finSum_succ, finSum_succ, ← ih]; rfl
  exact hsum (k + 1) (fun i => P.coeff i * Q.coeff (k - i))

theorem eval1_projA (P : Poly (UpperTri2 R)) : Poly.eval1 (projA P) = (Poly.eval1 P).a := by
  rcases P.isBounded with ⟨N, hN⟩
  have hPA : ∀ k, N ≤ k → (projA P).coeff k = 0 := by
    intro k hk; change (P.coeff k).a = 0; rw [hN k hk]; rfl
  rw [Poly.eval1_eq_finSum (projA P) hPA, Poly.eval1_eq_finSum P hN]
  induction N with
  | zero => rfl
  | succ m ih =>
    rw [finSum_succ, finSum_succ]
    change finSum m (projA P).coeff + (P.coeff m).a = (finSum m P.coeff).a + (P.coeff m).a
    -- Prove unconditionally for all prefix sums:
    have hgen : ∀ n, finSum n (projA P).coeff = (finSum n P.coeff).a := by
      intro n; induction n with
      | zero => rfl
      | succ l ihl => rw [finSum_succ, finSum_succ, ihl]; rfl
    rw [hgen m]

theorem eval1_projC (P : Poly (UpperTri2 R)) : Poly.eval1 (projC P) = (Poly.eval1 P).c := by
  rcases P.isBounded with ⟨N, hN⟩
  have hPC : ∀ k, N ≤ k → (projC P).coeff k = 0 := by
    intro k hk; change (P.coeff k).c = 0; rw [hN k hk]; rfl
  rw [Poly.eval1_eq_finSum (projC P) hPC, Poly.eval1_eq_finSum P hN]
  have hgen : ∀ n, finSum n (projC P).coeff = (finSum n P.coeff).c := by
    intro n; induction n with
    | zero => rfl
    | succ l ihl => rw [finSum_succ, finSum_succ, ihl]; rfl
  exact hgen N

end Ring

section DomainSpectrum
variable {K : Type u} [IntegralDomain K]

noncomputable def isOneBool (x : K) : Bool :=
  @decide (x = 1) (Classical.propDecidable (x = 1))

theorem isOneBool_one : isOneBool (1 : K) = true := by
  unfold isOneBool
  cases Classical.propDecidable ((1 : K) = 1) with
  | isTrue _ => rfl
  | isFalse h => exact False.elim (h rfl)

theorem isOneBool_zero : isOneBool (0 : K) = false := by
  unfold isOneBool
  cases Classical.propDecidable ((0 : K) = 1) with
  | isTrue h => exact False.elim (IntegralDomain.one_ne_zero h.symm)
  | isFalse _ => rfl

theorem polyConn_diag_eq {e₀ e₁ : UpperTri2 K} (hc : PolyConn e₀ e₁) :
    e₀.a = e₁.a ∧ e₀.c = e₁.c := by
  induction hc with
  | refl _ => exact ⟨rfl, rfl⟩
  | step hs =>
    rcases hs with ⟨P, hP, rfl, rfl⟩
    have hPa : projA P * projA P = projA P := by rw [← projA_mul, hP]
    have hPc : projC P * projC P = projC P := by rw [← projC_mul, hP]
    have ha_eq : (Poly.eval0 P).a = (Poly.eval1 P).a := by
      rcases Poly.idem_eq_zero_or_one_of_domain hPa with hz | ho
      · have h0 : (Poly.eval0 P).a = 0 := congrArg (fun q => q.coeff 0) hz
        have h1 : (Poly.eval1 P).a = 0 := by rw [← eval1_projA, hz, Poly.eval1_zero]
        rw [h0, h1]
      · have h0 : (Poly.eval0 P).a = 1 := congrArg (fun q => q.coeff 0) ho
        have h1 : (Poly.eval1 P).a = 1 := by rw [← eval1_projA, ho, Poly.eval1_one]
        rw [h0, h1]
    have hc_eq : (Poly.eval0 P).c = (Poly.eval1 P).c := by
      rcases Poly.idem_eq_zero_or_one_of_domain hPc with hz | ho
      · have h0 : (Poly.eval0 P).c = 0 := congrArg (fun q => q.coeff 0) hz
        have h1 : (Poly.eval1 P).c = 0 := by rw [← eval1_projC, hz, Poly.eval1_zero]
        rw [h0, h1]
      · have h0 : (Poly.eval0 P).c = 1 := congrArg (fun q => q.coeff 0) ho
        have h1 : (Poly.eval1 P).c = 1 := by rw [← eval1_projC, ho, Poly.eval1_one]
        rw [h0, h1]
    exact ⟨ha_eq, hc_eq⟩
  | symm _ ih => exact ⟨ih.1.symm, ih.2.symm⟩
  | trans _ _ ih1 ih2 => exact ⟨ih1.1.trans ih2.1, ih1.2.trans ih2.2⟩

/-- Exact characterization of connected families in non-semisimple `T₂(K)`:
    two idempotents in `T₂(K)` lie in the same `𝔸¹`-connected family iff they have
    equal diagonal projections `(a, c) ∈ {0, 1}²`, yielding `4 > 2 = b` components! -/
theorem polyConn_iff_diag_eq {e₀ e₁ : UpperTri2 K} (he₀ : IsIdem e₀) (he₁ : IsIdem e₁) :
    PolyConn e₀ e₁ ↔ e₀.a = e₁.a ∧ e₀.c = e₁.c := by
  constructor
  · exact polyConn_diag_eq
  · rintro ⟨ha, hc⟩
    apply PolyConn.step
    apply nilpotent_diff_polyStep he₀ he₁ (N := 2) (by decide)
    apply pow2_eq_zero_of_diag_zero
    · change ((e₁ - (1 - e₁)).a) * (e₀.a - e₁.a) = 0
      rw [ha, AssocRing.sub_self, AssocRing.mul_zero]
    · change ((e₁ - (1 - e₁)).c) * (e₀.c - e₁.c) = 0
      rw [hc, AssocRing.sub_self, AssocRing.mul_zero]

def diagIdem (p : Bool × Bool) : UpperTri2 K :=
  ⟨if p.1 then 1 else 0, 0, if p.2 then 1 else 0⟩

theorem isIdem_diagIdem (p : Bool × Bool) : IsIdem (diagIdem p : UpperTri2 K) := by
  rcases p with ⟨b1, b2⟩
  cases b1 <;> cases b2 <;>
  · apply ext
    · change (diagIdem _).a * (diagIdem _).a = (diagIdem _).a
      simp [diagIdem, AssocRing.zero_mul, AssocRing.one_mul']
    · change (diagIdem _).a * (diagIdem _).b + (diagIdem _).b * (diagIdem _).c = (diagIdem _).b
      simp [diagIdem, AssocRing.zero_mul, AssocRing.mul_zero, AssocRing.add_zero']
    · change (diagIdem _).c * (diagIdem _).c = (diagIdem _).c
      simp [diagIdem, AssocRing.zero_mul, AssocRing.one_mul']

/-- Exact 4-element bijection `Bool × Bool ≃ IdemSpectrum (UpperTri2 K)` for non-semisimple `T₂(K)`. -/
noncomputable def upperTri2SpectrumToBool2 : IdemSpectrum (UpperTri2 K) → Bool × Bool :=
  Quotient.lift
    (fun e => (isOneBool e.1.a, isOneBool e.1.c))
    (fun _ _ h => by
      dsimp only
      have hd := polyConn_diag_eq h
      rw [hd.1, hd.2])

def bool2ToUpperTri2Spectrum (p : Bool × Bool) : IdemSpectrum (UpperTri2 K) :=
  Quotient.mk (idemSetoid (UpperTri2 K)) ⟨diagIdem p, isIdem_diagIdem p⟩

theorem upperTri2_spectrum_left_inv (p : Bool × Bool) :
    upperTri2SpectrumToBool2 (bool2ToUpperTri2Spectrum p : IdemSpectrum (UpperTri2 K)) = p := by
  rcases p with ⟨b1, b2⟩
  cases b1 <;> cases b2 <;>
  · change (isOneBool (diagIdem _).a, isOneBool (diagIdem _).c) = _
    simp [diagIdem, isOneBool_zero, isOneBool_one]

theorem upperTri2_spectrum_right_inv (s : IdemSpectrum (UpperTri2 K)) :
    bool2ToUpperTri2Spectrum (upperTri2SpectrumToBool2 s) = s := by
  refine Quotient.inductionOn s (fun e => ?_)
  apply Quotient.sound
  change PolyConn (diagIdem (isOneBool e.1.a, isOneBool e.1.c)) e.1
  rw [polyConn_iff_diag_eq (isIdem_diagIdem _) e.2]
  have ha_idem : e.1.a * e.1.a = e.1.a := congrArg UpperTri2.a e.2
  have hc_idem : e.1.c * e.1.c = e.1.c := congrArg UpperTri2.c e.2
  constructor
  · rcases Poly.idem_eq_zero_or_one_of_domain ha_idem with ha0 | ha1
    · rw [ha0]; simp [diagIdem, isOneBool_zero]
    · rw [ha1]; simp [diagIdem, isOneBool_one]
  · rcases Poly.idem_eq_zero_or_one_of_domain hc_idem with hc0 | hc1
    · rw [hc0]; simp [diagIdem, isOneBool_zero]
    · rw [hc1]; simp [diagIdem, isOneBool_one]

end DomainSpectrum
end UpperTri2

/-! ### Universal Newton Idempotent Lift (`f(x) = 3x² - 2x³`) -/

section NewtonLift
variable {A : Type u} [AssocRing A]

/-- Newton's universal idempotent-lifting polynomial `f(x) = 3x² - 2x³` over ANY associative ring. -/
def newtonLiftStep (x : A) : A :=
  (x * x + x * x + x * x) - (x * x * x + x * x * x)

theorem newtonLiftStep_sub_self (x : A) :
    newtonLiftStep x - x = (x * x - x) * (1 - (x + x)) := by
  unfold newtonLiftStep
  -- Expand RHS: (x² - x)(1 - 2x) = x² - 2x³ - x + 2x² = 3x² - 2x³ - x
  have rhs_exp : (x * x - x) * (1 - (x + x)) =
      ((x * x + x * x + x * x) - (x * x * x + x * x * x)) - x := by
    rw [AssocRing.sub_mul, AssocRing.mul_sub, AssocRing.mul_sub]
    rw [AssocRing.mul_one', AssocRing.mul_one']
    rw [AssocRing.left_distrib (x * x) x x, AssocRing.left_distrib x x x]
    -- Use additive group cancellation: show LHS + x + (x³ + x³) = RHS + x + (x³ + x³)
    apply AssocRing.add_right_cancel (c := x)
    rw [AssocRing.sub_eq_add_neg (((x * x + x * x + x * x) - (x * x * x + x * x * x))) x]
    rw [AssocRing.add_assoc _ (-x) x, AssocRing.add_left_neg', AssocRing.add_zero']
    apply AssocRing.add_right_cancel (c := x * x * x + x * x * x)
    rw [AssocRing.sub_eq_add_neg (x * x + x * x + x * x)]
    rw [AssocRing.add_assoc (x * x + x * x + x * x) _ _, AssocRing.add_left_neg', AssocRing.add_zero']
    -- Remaining LHS: ((x² - (x³ + x³)) - (x - (x² + x²))) + x + (x³ + x³)
    have sub_sub : ∀ u v : A, u - (x - v) = u + v - x := by
      intro u v
      rw [AssocRing.sub_eq_add_neg u, AssocRing.sub_eq_add_neg x, AssocRing.neg_add, AssocRing.neg_neg]
      rw [AssocRing.add_comm (-x) v, ← AssocRing.add_assoc u v (-x), ← AssocRing.sub_eq_add_neg]
    rw [sub_sub (x * x - (x * x * x + x * x * x)) (x * x + x * x)]
    rw [AssocRing.sub_eq_add_neg _ x, AssocRing.add_assoc _ (-x) x, AssocRing.add_left_neg', AssocRing.add_zero']
    let c3 := x * x * x + x * x * x
    change ((x * x - c3) + (x * x + x * x)) + c3 = x * x + x * x + x * x
    rw [AssocRing.sub_eq_add_neg (x * x) c3]
    calc
      ((x * x + -c3) + (x * x + x * x)) + c3
        = (x * x + ((x * x + x * x) + -c3)) + c3 := by
          rw [AssocRing.add_assoc (x * x) (-c3), AssocRing.add_comm (-c3) (x * x + x * x)]
      _ = (x * x + x * x + x * x) + (-c3 + c3) := by
          rw [← AssocRing.add_assoc (x * x) (x * x + x * x) (-c3)]
          rw [← AssocRing.add_assoc (x * x) (x * x) (x * x)]
          rw [AssocRing.add_assoc (x * x + x * x + x * x) (-c3) c3]
      _ = x * x + x * x + x * x := by rw [AssocRing.add_left_neg', AssocRing.add_zero']
  exact rhs_exp.symm

end NewtonLift

/-! ## Utility Structures: Bijections & Injections -/

def Injective {α : Type u} {β : Type v} (f : α → β) : Prop :=
  ∀ x₁ x₂ : α, f x₁ = f x₂ → x₁ = x₂

structure EquivBij (α : Type u) (β : Type v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x : α, invFun (toFun x) = x
  right_inv : ∀ y : β, toFun (invFun y) = y

/-! ## Section 5: Exact 3-Component Spectrum of `M₂(K) ≅ Cl_{1,1}(K)` (`3 > 1 = b`) -/

structure Mat2 (R : Type u) where
  a : R
  b : R
  c : R
  d : R
  deriving DecidableEq

namespace Mat2

theorem ext {R : Type u} {x y : Mat2 R}
    (ha : x.a = y.a) (hb : x.b = y.b) (hc : x.c = y.c) (hd : x.d = y.d) : x = y := by
  cases x; cases y; subst ha; subst hb; subst hc; subst hd; rfl

private theorem four_add_swap {R : Type u} [AssocRing R] (p q r s : R) :
    (p + q) + (r + s) = (p + r) + (q + s) := by
  calc
    (p + q) + (r + s) = p + (q + (r + s)) := AssocRing.add_assoc _ _ _
    _ = p + (r + (q + s)) := by
      rw [← AssocRing.add_assoc q r s, AssocRing.add_comm q r, AssocRing.add_assoc r q s]
    _ = (p + r) + (q + s) := (AssocRing.add_assoc _ _ _).symm

section Ring
variable {R : Type u} [AssocRing R]

instance : AssocRing (Mat2 R) where
  add := fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩
  sub := fun x y => ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩
  neg := fun x => ⟨-x.a, -x.b, -x.c, -x.d⟩
  mul := fun x y =>
    ⟨x.a * y.a + x.b * y.c, x.a * y.b + x.b * y.d,
     x.c * y.a + x.d * y.c, x.c * y.b + x.d * y.d⟩
  zero := ⟨0, 0, 0, 0⟩
  one := ⟨1, 0, 0, 1⟩
  sub_eq_add_neg := fun _ _ => ext
    (AssocRing.sub_eq_add_neg _ _) (AssocRing.sub_eq_add_neg _ _)
    (AssocRing.sub_eq_add_neg _ _) (AssocRing.sub_eq_add_neg _ _)
  add_assoc := fun _ _ _ => ext
    (AssocRing.add_assoc _ _ _) (AssocRing.add_assoc _ _ _)
    (AssocRing.add_assoc _ _ _) (AssocRing.add_assoc _ _ _)
  add_comm := fun _ _ => ext
    (AssocRing.add_comm _ _) (AssocRing.add_comm _ _)
    (AssocRing.add_comm _ _) (AssocRing.add_comm _ _)
  zero_add := fun _ => ext
    (AssocRing.zero_add' _) (AssocRing.zero_add' _)
    (AssocRing.zero_add' _) (AssocRing.zero_add' _)
  add_zero := fun _ => ext
    (AssocRing.add_zero' _) (AssocRing.add_zero' _)
    (AssocRing.add_zero' _) (AssocRing.add_zero' _)
  add_left_neg := fun _ => ext
    (AssocRing.add_left_neg' _) (AssocRing.add_left_neg' _)
    (AssocRing.add_left_neg' _) (AssocRing.add_left_neg' _)
  mul_assoc := fun x y z => by
    apply ext
    · change (x.a * y.a + x.b * y.c) * z.a + (x.a * y.b + x.b * y.d) * z.c =
             x.a * (y.a * z.a + y.b * z.c) + x.b * (y.c * z.a + y.d * z.c)
      rw [AssocRing.right_distrib, AssocRing.right_distrib, AssocRing.left_distrib, AssocRing.left_distrib]
      simp only [AssocRing.mul_assoc]
      exact four_add_swap _ _ _ _
    · change (x.a * y.a + x.b * y.c) * z.b + (x.a * y.b + x.b * y.d) * z.d =
             x.a * (y.a * z.b + y.b * z.d) + x.b * (y.c * z.b + y.d * z.d)
      rw [AssocRing.right_distrib, AssocRing.right_distrib, AssocRing.left_distrib, AssocRing.left_distrib]
      simp only [AssocRing.mul_assoc]
      exact four_add_swap _ _ _ _
    · change (x.c * y.a + x.d * y.c) * z.a + (x.c * y.b + x.d * y.d) * z.c =
             x.c * (y.a * z.a + y.b * z.c) + x.d * (y.c * z.a + y.d * z.c)
      rw [AssocRing.right_distrib, AssocRing.right_distrib, AssocRing.left_distrib, AssocRing.left_distrib]
      simp only [AssocRing.mul_assoc]
      exact four_add_swap _ _ _ _
    · change (x.c * y.a + x.d * y.c) * z.b + (x.c * y.b + x.d * y.d) * z.d =
             x.c * (y.a * z.b + y.b * z.d) + x.d * (y.c * z.b + y.d * z.d)
      rw [AssocRing.right_distrib, AssocRing.right_distrib, AssocRing.left_distrib, AssocRing.left_distrib]
      simp only [AssocRing.mul_assoc]
      exact four_add_swap _ _ _ _
  one_mul := fun x => by
    apply ext
    · change 1 * x.a + 0 * x.c = x.a; rw [AssocRing.one_mul', AssocRing.zero_mul, AssocRing.add_zero']
    · change 1 * x.b + 0 * x.d = x.b; rw [AssocRing.one_mul', AssocRing.zero_mul, AssocRing.add_zero']
    · change 0 * x.a + 1 * x.c = x.c; rw [AssocRing.zero_mul, AssocRing.one_mul', AssocRing.zero_add']
    · change 0 * x.b + 1 * x.d = x.d; rw [AssocRing.zero_mul, AssocRing.one_mul', AssocRing.zero_add']
  mul_one := fun x => by
    apply ext
    · change x.a * 1 + x.b * 0 = x.a; rw [AssocRing.mul_one', AssocRing.mul_zero, AssocRing.add_zero']
    · change x.a * 0 + x.b * 1 = x.b; rw [AssocRing.mul_zero, AssocRing.mul_one', AssocRing.zero_add']
    · change x.c * 1 + x.d * 0 = x.c; rw [AssocRing.mul_one', AssocRing.mul_zero, AssocRing.add_zero']
    · change x.c * 0 + x.d * 1 = x.d; rw [AssocRing.mul_zero, AssocRing.mul_one', AssocRing.zero_add']
  left_distrib := fun x y z => by
    apply ext
    · change x.a * (y.a + z.a) + x.b * (y.c + z.c) = (x.a * y.a + x.b * y.c) + (x.a * z.a + x.b * z.c)
      rw [AssocRing.left_distrib, AssocRing.left_distrib]; exact four_add_swap _ _ _ _
    · change x.a * (y.b + z.b) + x.b * (y.d + z.d) = (x.a * y.b + x.b * y.d) + (x.a * z.b + x.b * z.d)
      rw [AssocRing.left_distrib, AssocRing.left_distrib]; exact four_add_swap _ _ _ _
    · change x.c * (y.a + z.a) + x.d * (y.c + z.c) = (x.c * y.a + x.d * y.c) + (x.c * z.a + x.d * z.c)
      rw [AssocRing.left_distrib, AssocRing.left_distrib]; exact four_add_swap _ _ _ _
    · change x.c * (y.b + z.b) + x.d * (y.d + z.d) = (x.c * y.b + x.d * y.d) + (x.c * z.b + x.d * z.d)
      rw [AssocRing.left_distrib, AssocRing.left_distrib]; exact four_add_swap _ _ _ _
  right_distrib := fun x y z => by
    apply ext
    · change (x.a + y.a) * z.a + (x.b + y.b) * z.c = (x.a * z.a + x.b * z.c) + (y.a * z.a + y.b * z.c)
      rw [AssocRing.right_distrib, AssocRing.right_distrib]; exact four_add_swap _ _ _ _
    · change (x.a + y.a) * z.b + (x.b + y.b) * z.d = (x.a * z.b + x.b * z.d) + (y.a * z.b + y.b * z.d)
      rw [AssocRing.right_distrib, AssocRing.right_distrib]; exact four_add_swap _ _ _ _
    · change (x.c + y.c) * z.a + (x.d + y.d) * z.c = (x.c * z.a + x.d * z.c) + (y.c * z.a + y.d * z.c)
      rw [AssocRing.right_distrib, AssocRing.right_distrib]; exact four_add_swap _ _ _ _
    · change (x.c + y.c) * z.b + (x.d + y.d) * z.d = (x.c * z.b + x.d * z.d) + (y.c * z.b + y.d * z.d)
      rw [AssocRing.right_distrib, AssocRing.right_distrib]; exact four_add_swap _ _ _ _

def smul (s : R) (M : Mat2 R) : Mat2 R := ⟨s * M.a, s * M.b, s * M.c, s * M.d⟩

def tr (M : Mat2 R) : R := M.a + M.d

theorem tr_add (M N : Mat2 R) : tr (M + N) = tr M + tr N :=
  four_add_swap M.a N.a M.d N.d

@[simp] theorem zero_a : (0 : Mat2 R).a = 0 := rfl
@[simp] theorem zero_b : (0 : Mat2 R).b = 0 := rfl
@[simp] theorem zero_c : (0 : Mat2 R).c = 0 := rfl
@[simp] theorem zero_d : (0 : Mat2 R).d = 0 := rfl
@[simp] theorem one_a : (1 : Mat2 R).a = 1 := rfl
@[simp] theorem one_b : (1 : Mat2 R).b = 0 := rfl
@[simp] theorem one_c : (1 : Mat2 R).c = 0 := rfl
@[simp] theorem one_d : (1 : Mat2 R).d = 1 := rfl
@[simp] theorem add_a (X Y : Mat2 R) : (X + Y).a = X.a + Y.a := rfl
@[simp] theorem add_b (X Y : Mat2 R) : (X + Y).b = X.b + Y.b := rfl
@[simp] theorem add_c (X Y : Mat2 R) : (X + Y).c = X.c + Y.c := rfl
@[simp] theorem add_d (X Y : Mat2 R) : (X + Y).d = X.d + Y.d := rfl
@[simp] theorem mul_a (X Y : Mat2 R) : (X * Y).a = X.a * Y.a + X.b * Y.c := rfl
@[simp] theorem mul_b (X Y : Mat2 R) : (X * Y).b = X.a * Y.b + X.b * Y.d := rfl
@[simp] theorem mul_c (X Y : Mat2 R) : (X * Y).c = X.c * Y.a + X.d * Y.c := rfl
@[simp] theorem mul_d (X Y : Mat2 R) : (X * Y).d = X.c * Y.b + X.d * Y.d := rfl

def E11 : Mat2 R := ⟨1, 0, 0, 0⟩
def E22 : Mat2 R := ⟨0, 0, 0, 1⟩

theorem isIdem_E11 : IsIdem (E11 : Mat2 R) := by
  apply ext <;> simp [E11, AssocRing.one_mul', AssocRing.zero_mul, AssocRing.mul_zero, AssocRing.add_zero']

theorem isIdem_E22 : IsIdem (E22 : Mat2 R) := by
  apply ext <;> simp [E22, AssocRing.one_mul', AssocRing.zero_mul, AssocRing.mul_zero, AssocRing.zero_add', AssocRing.add_zero']

/-- Isomorphism between `Poly (Mat2 R)` and `Mat2 (Poly R)`. -/
def polyToMat2Poly (P : Poly (Mat2 R)) : Mat2 (Poly R) :=
  ⟨⟨fun k => (P.coeff k).a, by rcases P.isBounded with ⟨N, hN⟩; exact ⟨N, fun k hk => by dsimp only; rw [hN k hk]; rfl⟩⟩,
   ⟨fun k => (P.coeff k).b, by rcases P.isBounded with ⟨N, hN⟩; exact ⟨N, fun k hk => by dsimp only; rw [hN k hk]; rfl⟩⟩,
   ⟨fun k => (P.coeff k).c, by rcases P.isBounded with ⟨N, hN⟩; exact ⟨N, fun k hk => by dsimp only; rw [hN k hk]; rfl⟩⟩,
   ⟨fun k => (P.coeff k).d, by rcases P.isBounded with ⟨N, hN⟩; exact ⟨N, fun k hk => by dsimp only; rw [hN k hk]; rfl⟩⟩⟩

def mat2PolyToPoly (M : Mat2 (Poly R)) : Poly (Mat2 R) where
  coeff := fun k => ⟨M.a.coeff k, M.b.coeff k, M.c.coeff k, M.d.coeff k⟩
  isBounded := by
    rcases M.a.isBounded with ⟨Na, ha⟩
    rcases M.b.isBounded with ⟨Nb, hb⟩
    rcases M.c.isBounded with ⟨Nc, hc⟩
    rcases M.d.isBounded with ⟨Nd, hd⟩
    refine ⟨Na + Nb + Nc + Nd, fun k hk => ?_⟩
    apply ext
    · exact ha k (by omega)
    · exact hb k (by omega)
    · exact hc k (by omega)
    · exact hd k (by omega)

theorem polyToMat2Poly_mul (P Q : Poly (Mat2 R)) :
    polyToMat2Poly (P * Q) = polyToMat2Poly P * polyToMat2Poly Q := by
  have sum_a : ∀ n (g : Nat → Mat2 R), (finSum n g).a = finSum n (fun i => (g i).a) := by
    intro n g; induction n with | zero => rfl | succ m ih => rw [finSum_succ, finSum_succ, add_a, ih]
  have sum_b : ∀ n (g : Nat → Mat2 R), (finSum n g).b = finSum n (fun i => (g i).b) := by
    intro n g; induction n with | zero => rfl | succ m ih => rw [finSum_succ, finSum_succ, add_b, ih]
  have sum_c : ∀ n (g : Nat → Mat2 R), (finSum n g).c = finSum n (fun i => (g i).c) := by
    intro n g; induction n with | zero => rfl | succ m ih => rw [finSum_succ, finSum_succ, add_c, ih]
  have sum_d : ∀ n (g : Nat → Mat2 R), (finSum n g).d = finSum n (fun i => (g i).d) := by
    intro n g; induction n with | zero => rfl | succ m ih => rw [finSum_succ, finSum_succ, add_d, ih]
  apply ext
  · apply Poly.ext; intro k
    change ((P * Q).coeff k).a = ((polyToMat2Poly P) * (polyToMat2Poly Q)).a.coeff k
    rw [Poly.coeff_mul, sum_a, mul_a, Poly.coeff_add, Poly.coeff_mul, Poly.coeff_mul, ← finSum_add]; rfl
  · apply Poly.ext; intro k
    change ((P * Q).coeff k).b = ((polyToMat2Poly P) * (polyToMat2Poly Q)).b.coeff k
    rw [Poly.coeff_mul, sum_b, mul_b, Poly.coeff_add, Poly.coeff_mul, Poly.coeff_mul, ← finSum_add]; rfl
  · apply Poly.ext; intro k
    change ((P * Q).coeff k).c = ((polyToMat2Poly P) * (polyToMat2Poly Q)).c.coeff k
    rw [Poly.coeff_mul, sum_c, mul_c, Poly.coeff_add, Poly.coeff_mul, Poly.coeff_mul, ← finSum_add]; rfl
  · apply Poly.ext; intro k
    change ((P * Q).coeff k).d = ((polyToMat2Poly P) * (polyToMat2Poly Q)).d.coeff k
    rw [Poly.coeff_mul, sum_d, mul_d, Poly.coeff_add, Poly.coeff_mul, Poly.coeff_mul, ← finSum_add]; rfl

theorem mat2PolyToPoly_mul (M N : Mat2 (Poly R)) :
    mat2PolyToPoly (M * N) = mat2PolyToPoly M * mat2PolyToPoly N := by
  have sum_a : ∀ n (g : Nat → Mat2 R), (finSum n g).a = finSum n (fun i => (g i).a) := by
    intro n g; induction n with | zero => rfl | succ m ih => rw [finSum_succ, finSum_succ, add_a, ih]
  have sum_b : ∀ n (g : Nat → Mat2 R), (finSum n g).b = finSum n (fun i => (g i).b) := by
    intro n g; induction n with | zero => rfl | succ m ih => rw [finSum_succ, finSum_succ, add_b, ih]
  have sum_c : ∀ n (g : Nat → Mat2 R), (finSum n g).c = finSum n (fun i => (g i).c) := by
    intro n g; induction n with | zero => rfl | succ m ih => rw [finSum_succ, finSum_succ, add_c, ih]
  have sum_d : ∀ n (g : Nat → Mat2 R), (finSum n g).d = finSum n (fun i => (g i).d) := by
    intro n g; induction n with | zero => rfl | succ m ih => rw [finSum_succ, finSum_succ, add_d, ih]
  apply Poly.ext
  intro k
  apply ext
  · change ((M * N).a).coeff k = ((mat2PolyToPoly M * mat2PolyToPoly N).coeff k).a
    rw [Poly.coeff_mul, sum_a, mul_a, Poly.coeff_add, Poly.coeff_mul, Poly.coeff_mul, ← finSum_add]; rfl
  · change ((M * N).b).coeff k = ((mat2PolyToPoly M * mat2PolyToPoly N).coeff k).b
    rw [Poly.coeff_mul, sum_b, mul_b, Poly.coeff_add, Poly.coeff_mul, Poly.coeff_mul, ← finSum_add]; rfl
  · change ((M * N).c).coeff k = ((mat2PolyToPoly M * mat2PolyToPoly N).coeff k).c
    rw [Poly.coeff_mul, sum_c, mul_c, Poly.coeff_add, Poly.coeff_mul, Poly.coeff_mul, ← finSum_add]; rfl
  · change ((M * N).d).coeff k = ((mat2PolyToPoly M * mat2PolyToPoly N).coeff k).d
    rw [Poly.coeff_mul, sum_d, mul_d, Poly.coeff_add, Poly.coeff_mul, Poly.coeff_mul, ← finSum_add]; rfl

theorem eval1_mat2PolyToPoly (M : Mat2 (Poly R)) :
    Poly.eval1 (mat2PolyToPoly M) =
      ⟨Poly.eval1 M.a, Poly.eval1 M.b, Poly.eval1 M.c, Poly.eval1 M.d⟩ := by
  rcases M.a.isBounded with ⟨Na, ha⟩
  rcases M.b.isBounded with ⟨Nb, hb⟩
  rcases M.c.isBounded with ⟨Nc, hc⟩
  rcases M.d.isBounded with ⟨Nd, hd⟩
  let N := Na + Nb + Nc + Nd
  have hMa : ∀ k, N ≤ k → M.a.coeff k = 0 := fun k hk => ha k (by omega)
  have hMb : ∀ k, N ≤ k → M.b.coeff k = 0 := fun k hk => hb k (by omega)
  have hMc : ∀ k, N ≤ k → M.c.coeff k = 0 := fun k hk => hc k (by omega)
  have hMd : ∀ k, N ≤ k → M.d.coeff k = 0 := fun k hk => hd k (by omega)
  have hMN : ∀ k, N ≤ k → (mat2PolyToPoly M).coeff k = 0 := by
    intro k hk; apply ext (hMa k hk) (hMb k hk) (hMc k hk) (hMd k hk)
  rw [Poly.eval1_eq_finSum (mat2PolyToPoly M) hMN,
      Poly.eval1_eq_finSum M.a hMa, Poly.eval1_eq_finSum M.b hMb,
      Poly.eval1_eq_finSum M.c hMc, Poly.eval1_eq_finSum M.d hMd]
  have hgen : ∀ n, finSum n (mat2PolyToPoly M).coeff =
      ⟨finSum n M.a.coeff, finSum n M.b.coeff, finSum n M.c.coeff, finSum n M.d.coeff⟩ := by
    intro n; induction n with
    | zero => rfl
    | succ m ih => rw [finSum_succ, ih, finSum_succ, finSum_succ, finSum_succ, finSum_succ]; rfl
  exact hgen N

theorem eval1_polyToMat2Poly (P : Poly (Mat2 R)) :
    (⟨Poly.eval1 (polyToMat2Poly P).a, Poly.eval1 (polyToMat2Poly P).b,
      Poly.eval1 (polyToMat2Poly P).c, Poly.eval1 (polyToMat2Poly P).d⟩ : Mat2 R) =
    Poly.eval1 P := by
  have heq : mat2PolyToPoly (polyToMat2Poly P) = P := by
    apply Poly.ext; intro k; apply ext <;> rfl
  rw [← eval1_mat2PolyToPoly (polyToMat2Poly P), heq]

end Ring

section CayleyHamiltonAndTrichotomy
variable {R : Type u} [CommRing R]

def det (M : Mat2 R) : R := M.a * M.d - M.b * M.c

private theorem cancel_two_add {u v w : R} : (u + v) - (u + w) + (w - v) = 0 := by
  apply AssocRing.add_left_cancel (a := u + w)
  rw [AssocRing.add_zero']
  calc
    (u + w) + ((u + v) - (u + w) + (w - v))
      = ((u + w) + ((u + v) + -(u + w))) + (w + -v) := by
        rw [AssocRing.sub_eq_add_neg, AssocRing.sub_eq_add_neg, AssocRing.add_assoc (u + w)]
    _ = (u + v) + (w + -v) := by
        rw [AssocRing.add_comm (u + v) (-(u + w)), ← AssocRing.add_assoc (u + w),
            AssocRing.add_right_neg, AssocRing.zero_add']
    _ = u + w := by
        rw [AssocRing.add_comm w (-v), ← AssocRing.add_assoc (u + v),
            AssocRing.add_assoc u v (-v), AssocRing.add_right_neg, AssocRing.add_zero']

/-- Specialization of Cayley–Hamilton to idempotent `2 × 2` matrices:
    `(1 - tr M) • M + (det M) • I₂ = 0`. -/
theorem idem_cayley_hamilton {M : Mat2 R} (hM : IsIdem M) :
    smul (1 - tr M) M + smul (det M) 1 = 0 := by
  have ha : M.a * M.a + M.b * M.c = M.a := congrArg Mat2.a hM
  have hb : M.a * M.b + M.b * M.d = M.b := congrArg Mat2.b hM
  have hc : M.c * M.a + M.d * M.c = M.c := congrArg Mat2.c hM
  have hd : M.c * M.b + M.d * M.d = M.d := congrArg Mat2.d hM
  apply ext
  · change (1 - (M.a + M.d)) * M.a + (M.a * M.d - M.b * M.c) * 1 = 0
    rw [AssocRing.sub_mul, AssocRing.one_mul', AssocRing.mul_one', AssocRing.right_distrib]
    rw [CommRing.mul_comm M.d M.a]
    conv => lhs; arg 1; arg 1; rw [← ha]
    exact cancel_two_add
  · change (1 - (M.a + M.d)) * M.b + (M.a * M.d - M.b * M.c) * 0 = 0
    rw [AssocRing.mul_zero, AssocRing.add_zero', AssocRing.sub_mul, AssocRing.one_mul']
    rw [AssocRing.right_distrib, CommRing.mul_comm M.d M.b, hb, AssocRing.sub_self]
  · change (1 - (M.a + M.d)) * M.c + (M.a * M.d - M.b * M.c) * 0 = 0
    rw [AssocRing.mul_zero, AssocRing.add_zero', AssocRing.sub_mul, AssocRing.one_mul']
    rw [AssocRing.right_distrib, CommRing.mul_comm M.a M.c, hc, AssocRing.sub_self]
  · change (1 - (M.a + M.d)) * M.d + (M.a * M.d - M.b * M.c) * 1 = 0
    rw [AssocRing.sub_mul, AssocRing.one_mul', AssocRing.mul_one', AssocRing.right_distrib]
    conv => lhs; arg 1; arg 1; rw [← hd]
    rw [AssocRing.add_comm (M.c * M.b) (M.d * M.d), CommRing.mul_comm M.c M.b]
    rw [AssocRing.add_comm (M.a * M.d) (M.d * M.d)]
    exact cancel_two_add

theorem smul_mul_self (s : R) (M : Mat2 R) : smul s M * M = smul s (M * M) := by
  apply ext
  · change (s * M.a) * M.a + (s * M.b) * M.c = s * (M.a * M.a + M.b * M.c)
    rw [AssocRing.left_distrib, AssocRing.mul_assoc, AssocRing.mul_assoc]
  · change (s * M.a) * M.b + (s * M.b) * M.d = s * (M.a * M.b + M.b * M.d)
    rw [AssocRing.left_distrib, AssocRing.mul_assoc, AssocRing.mul_assoc]
  · change (s * M.c) * M.a + (s * M.d) * M.c = s * (M.c * M.a + M.d * M.c)
    rw [AssocRing.left_distrib, AssocRing.mul_assoc, AssocRing.mul_assoc]
  · change (s * M.c) * M.b + (s * M.d) * M.d = s * (M.c * M.b + M.d * M.d)
    rw [AssocRing.left_distrib, AssocRing.mul_assoc, AssocRing.mul_assoc]

theorem smul_add_smul (s t : R) (M : Mat2 R) : smul s M + smul t M = smul (s + t) M := by
  apply ext
  · exact (AssocRing.right_distrib s t M.a).symm
  · exact (AssocRing.right_distrib s t M.b).symm
  · exact (AssocRing.right_distrib s t M.c).symm
  · exact (AssocRing.right_distrib s t M.d).symm

end CayleyHamiltonAndTrichotomy

section DomainTrichotomy
variable {D : Type u} [IntegralDomain D]

private theorem smul_eq_zero_imp {s : D} {M : Mat2 D} (h : smul s M = 0) (hM : M ≠ 0) :
    s = 0 := by
  by_cases ha : M.a ≠ 0
  · rcases IntegralDomain.eq_zero_or_eq_zero_of_mul_eq_zero (congrArg Mat2.a h) with hs | hc
    · exact hs
    · exact False.elim (ha hc)
  · by_cases hb : M.b ≠ 0
    · rcases IntegralDomain.eq_zero_or_eq_zero_of_mul_eq_zero (congrArg Mat2.b h) with hs | hc
      · exact hs
      · exact False.elim (hb hc)
    · by_cases hc : M.c ≠ 0
      · rcases IntegralDomain.eq_zero_or_eq_zero_of_mul_eq_zero (congrArg Mat2.c h) with hs | hc'
        · exact hs
        · exact False.elim (hc hc')
      · by_cases hd : M.d ≠ 0
        · rcases IntegralDomain.eq_zero_or_eq_zero_of_mul_eq_zero (congrArg Mat2.d h) with hs | hd'
          · exact hs
          · exact False.elim (hd hd')
        · exfalso; apply hM
          apply ext
          · by_cases x : M.a = 0; exact x; exact False.elim (ha x)
          · by_cases x : M.b = 0; exact x; exact False.elim (hb x)
          · by_cases x : M.c = 0; exact x; exact False.elim (hc x)
          · by_cases x : M.d = 0; exact x; exact False.elim (hd x)

/-- Universal Trichotomy of `2 × 2` idempotents over ANY integral domain `D` (any characteristic):
    every idempotent in `M₂(D)` is `0`, `I₂`, or satisfies `det M = 0 ∧ tr M = 1`. -/
theorem idempotent_trichotomy {M : Mat2 D} (hM : IsIdem M) :
    M = 0 ∨ M = 1 ∨ (M ≠ 0 ∧ M ≠ 1 ∧ det M = 0 ∧ tr M = 1) := by
  by_cases h0 : M = 0
  · exact Or.inl h0
  · by_cases h1 : M = 1
    · exact Or.inr (Or.inl h1)
    · right; right
      refine ⟨h0, h1, ?_⟩
      have hch := idem_cayley_hamilton hM
      have hmul : (smul (1 - tr M) M + smul (det M) 1) * M = 0 * M :=
        congrArg (fun X => X * M) hch
      rw [AssocRing.right_distrib, AssocRing.zero_mul, smul_mul_self, hM] at hmul
      have h1M : smul (det M) (1 : Mat2 D) * M = smul (det M) M := by
        apply ext
        · change (det M * 1) * M.a + (det M * 0) * M.c = det M * M.a
          rw [AssocRing.mul_one', AssocRing.mul_zero, AssocRing.zero_mul, AssocRing.add_zero']
        · change (det M * 1) * M.b + (det M * 0) * M.d = det M * M.b
          rw [AssocRing.mul_one', AssocRing.mul_zero, AssocRing.zero_mul, AssocRing.add_zero']
        · change (det M * 0) * M.a + (det M * 1) * M.c = det M * M.c
          rw [AssocRing.mul_one', AssocRing.mul_zero, AssocRing.zero_mul, AssocRing.zero_add']
        · change (det M * 0) * M.b + (det M * 1) * M.d = det M * M.d
          rw [AssocRing.mul_one', AssocRing.mul_zero, AssocRing.zero_mul, AssocRing.zero_add']
      rw [h1M, smul_add_smul] at hmul
      have hrel : (1 - tr M) + det M = 0 := smul_eq_zero_imp hmul h0
      have hneg : 1 - tr M = -(det M) := (AssocRing.neg_eq_of_add_eq_zero (by rw [AssocRing.add_comm]; exact hrel)).symm
      rw [hneg] at hch
      have hdiff : smul (-(det M)) M + smul (det M) 1 = smul (det M) (1 - M) := by
        apply ext
        · change -(det M) * M.a + det M * 1 = det M * (1 - M.a)
          rw [AssocRing.mul_sub, AssocRing.mul_one', AssocRing.neg_mul, AssocRing.add_comm, ← AssocRing.sub_eq_add_neg]
        · change -(det M) * M.b + det M * 0 = det M * (0 - M.b)
          rw [AssocRing.mul_zero, AssocRing.add_zero', AssocRing.zero_sub, AssocRing.mul_neg, AssocRing.neg_mul]
        · change -(det M) * M.c + det M * 0 = det M * (0 - M.c)
          rw [AssocRing.mul_zero, AssocRing.add_zero', AssocRing.zero_sub, AssocRing.mul_neg, AssocRing.neg_mul]
        · change -(det M) * M.d + det M * 1 = det M * (1 - M.d)
          rw [AssocRing.mul_sub, AssocRing.mul_one', AssocRing.neg_mul, AssocRing.add_comm, ← AssocRing.sub_eq_add_neg]
      rw [hdiff] at hch
      have h1M_ne : (1 : Mat2 D) - M ≠ 0 := by
        intro hc
        exact h1 (AssocRing.sub_eq_zero.mp hc).symm
      have hdet : det M = 0 := smul_eq_zero_imp hch h1M_ne
      rw [hdet, AssocRing.add_zero'] at hrel
      have htr : tr M = 1 := (AssocRing.sub_eq_zero.mp hrel).symm
      exact ⟨hdet, htr⟩

/-- Class invariant `0, 1, 2` (`Fin 3`) of `2 × 2` idempotents over any integral domain `D`. -/
noncomputable def mat2Class (M : Mat2 D) : Fin 3 :=
  if @decide (M = 0) (Classical.propDecidable _) then ⟨0, by decide⟩
  else if @decide (M = 1) (Classical.propDecidable _) then ⟨2, by decide⟩
  else ⟨1, by decide⟩

theorem mat2Class_zero : mat2Class (0 : Mat2 D) = ⟨0, by decide⟩ := by
  unfold mat2Class
  cases Classical.propDecidable ((0 : Mat2 D) = 0) with
  | isTrue _ => rfl
  | isFalse h => exact False.elim (h rfl)

theorem mat2Class_one : mat2Class (1 : Mat2 D) = ⟨2, by decide⟩ := by
  have h10 : (1 : Mat2 D) ≠ 0 := by
    intro h; exact IntegralDomain.one_ne_zero (congrArg Mat2.a h)
  unfold mat2Class
  cases Classical.propDecidable ((1 : Mat2 D) = 0) with
  | isTrue h => exact False.elim (h10 h)
  | isFalse _ =>
    cases Classical.propDecidable ((1 : Mat2 D) = 1) with
    | isTrue _ => rfl
    | isFalse h => exact False.elim (h rfl)

theorem mat2Class_proper {M : Mat2 D} (h0 : M ≠ 0) (h1 : M ≠ 1) :
    mat2Class M = ⟨1, by decide⟩ := by
  unfold mat2Class
  cases Classical.propDecidable (M = 0) with
  | isTrue h => exact False.elim (h0 h)
  | isFalse _ =>
    cases Classical.propDecidable (M = 1) with
    | isTrue h => exact False.elim (h1 h)
    | isFalse _ => rfl

/-- Polynomial homotopy invariance of `mat2Class` over ANY integral domain `D`! -/
theorem polyConn_mat2Class_eq {E₀ E₁ : Mat2 D} (hc : PolyConn E₀ E₁) :
    mat2Class E₀ = mat2Class E₁ := by
  induction hc with
  | refl _ => rfl
  | step hs =>
    rcases hs with ⟨P, hP, rfl, rfl⟩
    let MP : Mat2 (Poly D) := polyToMat2Poly P
    have hMP : IsIdem MP := by
      unfold IsIdem
      dsimp only [MP]
      rw [← polyToMat2Poly_mul, hP]
    rcases idempotent_trichotomy hMP with hz | ho | ⟨_, _, hdet, htr⟩
    · have he0 : Poly.eval0 P = 0 := by
        apply ext
        · exact congrArg (fun q => q.coeff 0) (congrArg Mat2.a hz)
        · exact congrArg (fun q => q.coeff 0) (congrArg Mat2.b hz)
        · exact congrArg (fun q => q.coeff 0) (congrArg Mat2.c hz)
        · exact congrArg (fun q => q.coeff 0) (congrArg Mat2.d hz)
      have he1 : Poly.eval1 P = 0 := by
        rw [← eval1_polyToMat2Poly P]
        change (⟨Poly.eval1 MP.a, Poly.eval1 MP.b, Poly.eval1 MP.c, Poly.eval1 MP.d⟩ : Mat2 D) = 0
        rw [hz]
        apply ext <;> exact Poly.eval1_zero
      rw [he0, he1]
    · have he0 : Poly.eval0 P = 1 := by
        apply ext
        · exact congrArg (fun q => q.coeff 0) (congrArg Mat2.a ho)
        · exact congrArg (fun q => q.coeff 0) (congrArg Mat2.b ho)
        · exact congrArg (fun q => q.coeff 0) (congrArg Mat2.c ho)
        · exact congrArg (fun q => q.coeff 0) (congrArg Mat2.d ho)
      have he1 : Poly.eval1 P = 1 := by
        rw [← eval1_polyToMat2Poly P]
        change (⟨Poly.eval1 MP.a, Poly.eval1 MP.b, Poly.eval1 MP.c, Poly.eval1 MP.d⟩ : Mat2 D) = 1
        rw [ho]
        apply ext
        · exact Poly.eval1_one
        · exact Poly.eval1_zero
        · exact Poly.eval1_zero
        · exact Poly.eval1_one
      rw [he0, he1]
    · -- Both eval0 P and eval1 P have det = 0 and tr = 1, hence neither is 0 nor 1!
      have htr0 : tr (Poly.eval0 P) = 1 := by
        have h0 := congrArg Poly.eval0 htr
        exact h0
      have hdet0 : det (Poly.eval0 P) = 0 := by
        have hd0 : Poly.eval0 (MP.a * MP.d - MP.b * MP.c) = 0 := congrArg Poly.eval0 hdet
        have hsub : Poly.eval0 (MP.a * MP.d - MP.b * MP.c) = det (Poly.eval0 P) := by
          change (MP.a * MP.d - MP.b * MP.c).coeff 0 = det (Poly.eval0 P)
          rw [Poly.coeff_sub]
          change Poly.eval0 (MP.a * MP.d) - Poly.eval0 (MP.b * MP.c) = det (Poly.eval0 P)
          rw [Poly.eval0_mul, Poly.eval0_mul]
          rfl
        rw [← hsub]; exact hd0
      have htr1 : tr (Poly.eval1 P) = 1 := by
        rw [← eval1_polyToMat2Poly P]
        change Poly.eval1 MP.a + Poly.eval1 MP.d = 1
        rw [← Poly.eval1_add]
        change Poly.eval1 (tr MP) = 1
        rw [htr, Poly.eval1_one]
      have hdet1 : det (Poly.eval1 P) = 0 := by
        rw [← eval1_polyToMat2Poly P]
        change Poly.eval1 MP.a * Poly.eval1 MP.d - Poly.eval1 MP.b * Poly.eval1 MP.c = 0
        rw [← Poly.eval1_mul, ← Poly.eval1_mul, AssocRing.sub_eq_add_neg, ← Poly.eval1_neg, ← Poly.eval1_add]
        change Poly.eval1 (det MP) = 0
        rw [hdet, Poly.eval1_zero]
      have hn0_0 : Poly.eval0 P ≠ 0 := by
        intro hc; rw [hc] at htr0
        change (0 : D) + 0 = 1 at htr0
        rw [AssocRing.add_zero'] at htr0
        exact IntegralDomain.one_ne_zero htr0.symm
      have hn0_1 : Poly.eval0 P ≠ 1 := by
        intro hc; rw [hc] at hdet0
        change (1 : D) * 1 - 0 * 0 = 0 at hdet0
        rw [AssocRing.one_mul', AssocRing.zero_mul, AssocRing.sub_zero] at hdet0
        exact IntegralDomain.one_ne_zero hdet0
      have hn1_0 : Poly.eval1 P ≠ 0 := by
        intro hc; rw [hc] at htr1
        change (0 : D) + 0 = 1 at htr1
        rw [AssocRing.add_zero'] at htr1
        exact IntegralDomain.one_ne_zero htr1.symm
      have hn1_1 : Poly.eval1 P ≠ 1 := by
        intro hc; rw [hc] at hdet1
        change (1 : D) * 1 - 0 * 0 = 0 at hdet1
        rw [AssocRing.one_mul', AssocRing.zero_mul, AssocRing.sub_zero] at hdet1
        exact IntegralDomain.one_ne_zero hdet1
      rw [mat2Class_proper hn0_0 hn0_1, mat2Class_proper hn1_0 hn1_1]
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

end DomainTrichotomy

section FieldExactSpectrum
variable {K : Type u} [Field K]

theorem polyConn_upper1 (b : K) : PolyConn (⟨1, b, 0, 0⟩ : Mat2 K) E11 := by
  apply PolyConn.symm
  apply PolyConn.step
  let M : Mat2 (Poly K) := ⟨1, Poly.const b * Poly.varT, 0, 0⟩
  refine ⟨mat2PolyToPoly M, ?_, ?_, ?_⟩
  · unfold IsIdem
    rw [← mat2PolyToPoly_mul]
    apply congrArg mat2PolyToPoly
    apply ext
    · change (1 : Poly K) * 1 + (Poly.const b * Poly.varT) * 0 = 1
      rw [AssocRing.one_mul', AssocRing.mul_zero, AssocRing.add_zero']
    · change (1 : Poly K) * (Poly.const b * Poly.varT) + (Poly.const b * Poly.varT) * 0 = _
      rw [AssocRing.one_mul', AssocRing.mul_zero, AssocRing.add_zero']
    · change (0 : Poly K) * 1 + 0 * 0 = 0
      rw [AssocRing.zero_mul, AssocRing.zero_mul, AssocRing.add_zero']
    · change (0 : Poly K) * _ + 0 * 0 = 0
      rw [AssocRing.zero_mul, AssocRing.zero_mul, AssocRing.add_zero']
  · apply ext
    · rfl
    · change Poly.eval0 (Poly.const b * Poly.varT) = 0
      rw [Poly.eval0_mul, Poly.eval0_varT, AssocRing.mul_zero]
    · rfl
    · rfl
  · rw [eval1_mat2PolyToPoly]
    apply ext
    · exact Poly.eval1_one
    · rw [Poly.eval1_mul, Poly.eval1_const, Poly.eval1_varT, AssocRing.mul_one']
    · exact Poly.eval1_zero
    · exact Poly.eval1_zero

theorem polyConn_upper2 (b : K) : PolyConn (⟨0, b, 0, 1⟩ : Mat2 K) E22 := by
  apply PolyConn.symm
  apply PolyConn.step
  let M : Mat2 (Poly K) := ⟨0, Poly.const b * Poly.varT, 0, 1⟩
  refine ⟨mat2PolyToPoly M, ?_, ?_, ?_⟩
  · unfold IsIdem
    rw [← mat2PolyToPoly_mul]
    apply congrArg mat2PolyToPoly
    apply ext
    · change (0 : Poly K) * 0 + _ * 0 = 0; rw [AssocRing.zero_mul, AssocRing.mul_zero, AssocRing.add_zero']
    · change (0 : Poly K) * _ + (Poly.const b * Poly.varT) * 1 = _
      rw [AssocRing.zero_mul, AssocRing.mul_one', AssocRing.zero_add']
    · change (0 : Poly K) * 0 + 1 * 0 = 0; rw [AssocRing.zero_mul, AssocRing.mul_zero, AssocRing.add_zero']
    · change (0 : Poly K) * _ + (1 : Poly K) * 1 = 1
      rw [AssocRing.zero_mul, AssocRing.one_mul', AssocRing.zero_add']
  · apply ext
    · rfl
    · change Poly.eval0 (Poly.const b * Poly.varT) = 0
      rw [Poly.eval0_mul, Poly.eval0_varT, AssocRing.mul_zero]
    · rfl
    · rfl
  · rw [eval1_mat2PolyToPoly]
    apply ext
    · exact Poly.eval1_zero
    · rw [Poly.eval1_mul, Poly.eval1_const, Poly.eval1_varT, AssocRing.mul_one']
    · exact Poly.eval1_zero
    · exact Poly.eval1_one

theorem polyConn_lower2 (c : K) : PolyConn (⟨0, 0, c, 1⟩ : Mat2 K) E22 := by
  apply PolyConn.symm
  apply PolyConn.step
  let M : Mat2 (Poly K) := ⟨0, 0, Poly.const c * Poly.varT, 1⟩
  refine ⟨mat2PolyToPoly M, ?_, ?_, ?_⟩
  · unfold IsIdem
    rw [← mat2PolyToPoly_mul]
    apply congrArg mat2PolyToPoly
    apply ext
    · change (0 : Poly K) * 0 + 0 * _ = 0; rw [AssocRing.zero_mul, AssocRing.zero_mul, AssocRing.add_zero']
    · change (0 : Poly K) * 0 + 0 * 1 = 0; rw [AssocRing.zero_mul, AssocRing.zero_mul, AssocRing.add_zero']
    · change (Poly.const c * Poly.varT) * 0 + 1 * (Poly.const c * Poly.varT) = _
      rw [AssocRing.mul_zero, AssocRing.one_mul', AssocRing.zero_add']
    · change _ * 0 + (1 : Poly K) * 1 = 1
      rw [AssocRing.mul_zero, AssocRing.one_mul', AssocRing.zero_add']
  · apply ext
    · rfl
    · rfl
    · change Poly.eval0 (Poly.const c * Poly.varT) = 0
      rw [Poly.eval0_mul, Poly.eval0_varT, AssocRing.mul_zero]
    · rfl
  · rw [eval1_mat2PolyToPoly]
    apply ext
    · exact Poly.eval1_zero
    · exact Poly.eval1_zero
    · rw [Poly.eval1_mul, Poly.eval1_const, Poly.eval1_varT, AssocRing.mul_one']
    · exact Poly.eval1_one

/-- Explicit quadratic `𝔸¹`-homotopy `F(t) = [[t, 1], [t(1-t), 1-t]]` connecting `E₂₂` to `E₁₁`! -/
theorem polyConn_E22_E11 : PolyConn (E22 : Mat2 K) E11 := by
  have h1 : PolyConn (E22 : Mat2 K) ⟨0, 1, 0, 1⟩ := PolyConn.symm (polyConn_upper2 1)
  have h2 : PolyConn (⟨0, 1, 0, 1⟩ : Mat2 K) ⟨1, 1, 0, 0⟩ := by
    apply PolyConn.step
    let T : Poly K := Poly.varT
    let oneSubT : Poly K := 1 - T
    let M : Mat2 (Poly K) := ⟨T, 1, T * oneSubT, oneSubT⟩
    refine ⟨mat2PolyToPoly M, ?_, ?_, ?_⟩
    · unfold IsIdem
      rw [← mat2PolyToPoly_mul]
      apply congrArg mat2PolyToPoly
      have hsum : T + oneSubT = 1 := by
        dsimp only [oneSubT]
        rw [AssocRing.sub_eq_add_neg, AssocRing.add_comm 1 (-T), ← AssocRing.add_assoc,
            AssocRing.add_right_neg, AssocRing.zero_add']
      apply ext
      · change T * T + 1 * (T * oneSubT) = T
        rw [AssocRing.one_mul', ← AssocRing.left_distrib, hsum, AssocRing.mul_one']
      · change T * 1 + 1 * oneSubT = 1
        rw [AssocRing.mul_one', AssocRing.one_mul', hsum]
      · change (T * oneSubT) * T + oneSubT * (T * oneSubT) = T * oneSubT
        rw [CommRing.mul_comm (T * oneSubT) T, ← AssocRing.right_distrib, hsum, AssocRing.one_mul']
      · change (T * oneSubT) * 1 + oneSubT * oneSubT = oneSubT
        rw [AssocRing.mul_one', ← AssocRing.right_distrib, hsum, AssocRing.one_mul']
    · apply ext
      · exact Poly.eval0_varT
      · exact Poly.eval0_one
      · change Poly.eval0 (T * (1 - T)) = 0
        rw [Poly.eval0_mul, Poly.eval0_varT, AssocRing.zero_mul]
      · change Poly.eval0 (1 - T) = 1
        unfold Poly.eval0
        rw [Poly.coeff_sub, Poly.coeff_one, Poly.coeff_varT, if_pos rfl, if_neg (by decide), AssocRing.sub_zero]
    · rw [eval1_mat2PolyToPoly]
      have he1_sub : Poly.eval1 oneSubT = 0 := by
        dsimp only [oneSubT]
        rw [AssocRing.sub_eq_add_neg, Poly.eval1_add, Poly.eval1_one, Poly.eval1_neg, Poly.eval1_varT,
            AssocRing.add_right_neg]
      apply ext
      · exact Poly.eval1_varT
      · exact Poly.eval1_one
      · rw [Poly.eval1_mul, he1_sub, AssocRing.mul_zero]
      · exact he1_sub
  exact PolyConn.trans h1 (PolyConn.trans h2 (polyConn_upper1 1))

/-- Every rank-1 idempotent (`det E = 0 ∧ tr E = 1`) in `M₂(K)` over ANY field `K` is
    `𝔸¹`-connected to `E₁₁`! -/
theorem polyConn_rank1_to_E11 {E : Mat2 K} (hE : IsIdem E)
    (hdet : det E = 0) (htr : tr E = 1) : PolyConn E E11 := by
  by_cases ha : E.a = 0
  · have hd : E.d = 1 := by
      unfold tr at htr
      rw [ha, AssocRing.zero_add'] at htr
      exact htr
    have hbc : E.b * E.c = 0 := by
      unfold det at hdet
      rw [ha, AssocRing.zero_mul, AssocRing.zero_sub] at hdet
      have hneg := congrArg (fun x => -x) hdet
      dsimp only at hneg
      rw [AssocRing.neg_neg, AssocRing.neg_zero] at hneg
      exact hneg
    rcases IntegralDomain.eq_zero_or_eq_zero_of_mul_eq_zero hbc with hb0 | hc0
    · have hEq : E = ⟨0, 0, E.c, 1⟩ := ext ha hb0 rfl hd
      rw [hEq]
      exact PolyConn.trans (polyConn_lower2 E.c) polyConn_E22_E11
    · have hEq : E = ⟨0, E.b, 0, 1⟩ := ext ha rfl hc0 hd
      rw [hEq]
      exact PolyConn.trans (polyConn_upper2 E.b) polyConn_E22_E11
  · -- E.a ≠ 0: conjugate by elementary lower transvection L(t) = [[1, 0], [-q t, 1]] where q = c * a⁻¹!
    let q : K := E.c * Field.inv E.a
    let qt : Poly K := Poly.const q * Poly.varT
    let L : Mat2 (Poly K) := ⟨1, 0, -qt, 1⟩
    let Rmat : Mat2 (Poly K) := ⟨1, 0, qt, 1⟩
    let Ec : Mat2 (Poly K) := ⟨Poly.const E.a, Poly.const E.b, Poly.const E.c, Poly.const E.d⟩
    have hRL : Rmat * L = 1 := by
      apply ext
      · change (1 : Poly K) * 1 + 0 * (-qt) = 1; rw [AssocRing.one_mul', AssocRing.zero_mul, AssocRing.add_zero']
      · change (1 : Poly K) * 0 + 0 * 1 = 0; rw [AssocRing.mul_zero, AssocRing.zero_mul, AssocRing.add_zero']
      · change qt * 1 + 1 * (-qt) = 0; rw [AssocRing.mul_one', AssocRing.one_mul', AssocRing.add_right_neg]
      · change qt * 0 + (1 : Poly K) * 1 = 1; rw [AssocRing.mul_zero, AssocRing.one_mul', AssocRing.zero_add']
    have hEc_idem : Ec * Ec = Ec := by
      have hP : mat2PolyToPoly Ec = Poly.const E := by
        apply Poly.ext; intro k; unfold mat2PolyToPoly
        by_cases hk : k = 0
        · subst hk; rfl
        · dsimp only; rw [Poly.coeff_const, Poly.coeff_const, Poly.coeff_const, Poly.coeff_const, Poly.coeff_const]
          rw [if_neg hk, if_neg hk, if_neg hk, if_neg hk, if_neg hk]; rfl
      apply ext
      · change Poly.const E.a * Poly.const E.a + Poly.const E.b * Poly.const E.c = Poly.const E.a
        rw [← Poly.const_mul, ← Poly.const_mul, ← Poly.const_add]
        exact congrArg Poly.const (congrArg Mat2.a hE)
      · change Poly.const E.a * Poly.const E.b + Poly.const E.b * Poly.const E.d = Poly.const E.b
        rw [← Poly.const_mul, ← Poly.const_mul, ← Poly.const_add]
        exact congrArg Poly.const (congrArg Mat2.b hE)
      · change Poly.const E.c * Poly.const E.a + Poly.const E.d * Poly.const E.c = Poly.const E.c
        rw [← Poly.const_mul, ← Poly.const_mul, ← Poly.const_add]
        exact congrArg Poly.const (congrArg Mat2.c hE)
      · change Poly.const E.c * Poly.const E.b + Poly.const E.d * Poly.const E.d = Poly.const E.d
        rw [← Poly.const_mul, ← Poly.const_mul, ← Poly.const_add]
        exact congrArg Poly.const (congrArg Mat2.d hE)
    have hstep : PolyStep E ⟨1, E.b, 0, 0⟩ := by
      let G := L * Ec * Rmat
      refine ⟨mat2PolyToPoly G, ?_, ?_, ?_⟩
      · unfold IsIdem
        rw [← mat2PolyToPoly_mul]
        apply congrArg mat2PolyToPoly
        dsimp only [G]
        calc
          (L * Ec * Rmat) * (L * Ec * Rmat)
            = L * Ec * ((Rmat * L) * Ec) * Rmat := by simp only [AssocRing.mul_assoc]
          _ = L * (Ec * Ec) * Rmat := by rw [hRL, AssocRing.one_mul', AssocRing.mul_assoc L]
          _ = L * Ec * Rmat := by rw [hEc_idem]
      · -- At t = 0: eval0 qt = 0, so L(0) = 1, R(0) = 1, G(0) = E
        have hqt0 : Poly.eval0 qt = 0 := by
          dsimp only [qt]; rw [Poly.eval0_mul, Poly.eval0_varT, AssocRing.mul_zero]
        have hev : ∀ X : Mat2 (Poly K), Poly.eval0 (mat2PolyToPoly X) =
            ⟨Poly.eval0 X.a, Poly.eval0 X.b, Poly.eval0 X.c, Poly.eval0 X.d⟩ := fun _ => rfl
        have hmul0 : ∀ X Y : Mat2 (Poly K),
            Poly.eval0 (mat2PolyToPoly (X * Y)) =
            Poly.eval0 (mat2PolyToPoly X) * Poly.eval0 (mat2PolyToPoly Y) := by
          intro X Y; rw [mat2PolyToPoly_mul, Poly.eval0_mul]
        rw [hmul0, hmul0]
        have hL0 : Poly.eval0 (mat2PolyToPoly L) = 1 := by
          rw [hev]; apply ext
          · rfl
          · rfl
          · change Poly.eval0 (-qt) = 0; rw [Poly.eval0_neg, hqt0, AssocRing.neg_zero]
          · rfl
        have hR0 : Poly.eval0 (mat2PolyToPoly Rmat) = 1 := by
          rw [hev]
          apply ext
          · rfl
          · rfl
          · exact hqt0
          · rfl
        have hE0 : Poly.eval0 (mat2PolyToPoly Ec) = E := by
          rw [hev]; apply ext <;> rfl
        rw [hL0, hE0, hR0, AssocRing.one_mul', AssocRing.mul_one']
      · -- At t = 1: L(1) = [[1,0],[-q,1]], R(1) = [[1,0],[q,1]], product is [[1, E.b], [0, 0]]!
        have hmul1 : ∀ X Y : Mat2 (Poly K),
            Poly.eval1 (mat2PolyToPoly (X * Y)) =
            Poly.eval1 (mat2PolyToPoly X) * Poly.eval1 (mat2PolyToPoly Y) := by
          intro X Y; rw [mat2PolyToPoly_mul, Poly.eval1_mul]
        rw [hmul1, hmul1]
        have hqt1 : Poly.eval1 qt = q := by
          dsimp only [qt]; rw [Poly.eval1_mul, Poly.eval1_const, Poly.eval1_varT, AssocRing.mul_one']
        have hL1 : Poly.eval1 (mat2PolyToPoly L) = ⟨1, 0, -q, 1⟩ := by
          rw [eval1_mat2PolyToPoly]
          apply ext Poly.eval1_one Poly.eval1_zero (by rw [Poly.eval1_neg, hqt1]) Poly.eval1_one
        have hR1 : Poly.eval1 (mat2PolyToPoly Rmat) = ⟨1, 0, q, 1⟩ := by
          rw [eval1_mat2PolyToPoly]
          apply ext Poly.eval1_one Poly.eval1_zero hqt1 Poly.eval1_one
        have hE1 : Poly.eval1 (mat2PolyToPoly Ec) = E := by
          rw [eval1_mat2PolyToPoly]
          apply ext (Poly.eval1_const _) (Poly.eval1_const _) (Poly.eval1_const _) (Poly.eval1_const _)
        rw [hL1, hE1, hR1]
        have had_bc : E.a * E.d = E.b * E.c := AssocRing.sub_eq_zero.mp hdet
        have hqa : q * E.a = E.c := by
          dsimp only [q]
          rw [AssocRing.mul_assoc, Field.inv_mul_cancel ha, AssocRing.mul_one']
        have hqb : E.b * q = E.d := by
          dsimp only [q]
          rw [← AssocRing.mul_assoc, ← had_bc, CommRing.mul_comm E.a E.d, AssocRing.mul_assoc,
              Field.mul_inv_cancel ha, AssocRing.mul_one']
        have hc_mid : (-q) * E.a + 1 * E.c = 0 := by
          rw [AssocRing.neg_mul, hqa, AssocRing.one_mul', AssocRing.add_left_neg']
        have hd_mid : (-q) * E.b + 1 * E.d = 0 := by
          rw [AssocRing.neg_mul, CommRing.mul_comm q E.b, hqb, AssocRing.one_mul', AssocRing.add_left_neg']
        apply ext
        · change (1 * E.a + 0 * E.c) * 1 + (1 * E.b + 0 * E.d) * q = 1
          rw [AssocRing.one_mul', AssocRing.one_mul', AssocRing.zero_mul, AssocRing.zero_mul,
              AssocRing.add_zero', AssocRing.add_zero', AssocRing.mul_one', hqb]
          exact htr
        · change (1 * E.a + 0 * E.c) * 0 + (1 * E.b + 0 * E.d) * 1 = E.b
          rw [AssocRing.mul_zero, AssocRing.zero_add', AssocRing.mul_one', AssocRing.one_mul',
              AssocRing.zero_mul, AssocRing.add_zero']
        · change ((-q) * E.a + 1 * E.c) * 1 + ((-q) * E.b + 1 * E.d) * q = 0
          rw [hc_mid, hd_mid, AssocRing.zero_mul, AssocRing.zero_mul, AssocRing.add_zero']
        · change ((-q) * E.a + 1 * E.c) * 0 + ((-q) * E.b + 1 * E.d) * 1 = 0
          rw [hc_mid, hd_mid, AssocRing.zero_mul, AssocRing.zero_mul, AssocRing.add_zero']
    exact PolyConn.trans (PolyConn.step hstep) (polyConn_upper1 E.b)

/-- Canonical representatives of the 3 connected components of `E(M₂(K))`: `0`, `E₁₁`, `I₂`. -/
def mat2Rep : Fin 3 → IdemElem (Mat2 K)
  | ⟨0, _⟩ => ⟨0, isIdem_zero⟩
  | ⟨1, _⟩ => ⟨E11, isIdem_E11⟩
  | ⟨2, _⟩ => ⟨1, isIdem_one⟩

/-- Exact Bijection Theorem (`π₀^{𝔸¹}(E(M₂(K))) ≃ Fin 3`):
    For EVERY field `K` (of ANY characteristic), `M₂(K) ≅ Cl_{1,1}(K)` has `b = 1` matrix
    block, yet its connected-family spectrum of idempotents has EXACTLY `3 > 1` elements! -/
noncomputable def mat2IdemSpectrumEquivFin3 : EquivBij (IdemSpectrum (Mat2 K)) (Fin 3) where
  toFun := Quotient.lift (fun e => mat2Class e.1) (fun _ _ h => polyConn_mat2Class_eq h)
  invFun := fun idx => Quotient.mk (idemSetoid (Mat2 K)) (mat2Rep idx)
  left_inv := fun s => by
    refine Quotient.inductionOn s (fun e => ?_)
    apply Quotient.sound
    rcases idempotent_trichotomy e.2 with h0 | h1 | ⟨hn0, hn1, hdet, htr⟩
    · change PolyConn (mat2Rep (mat2Class e.1)).1 e.1
      rw [h0, mat2Class_zero]
      exact PolyConn.refl isIdem_zero
    · change PolyConn (mat2Rep (mat2Class e.1)).1 e.1
      rw [h1, mat2Class_one]
      exact PolyConn.refl isIdem_one
    · change PolyConn (mat2Rep (mat2Class e.1)).1 e.1
      rw [mat2Class_proper hn0 hn1]
      exact PolyConn.symm (polyConn_rank1_to_E11 e.2 hdet htr)
  right_inv := fun idx => by
    rcases idx with ⟨val, hlt⟩
    match val with
    | 0 => exact mat2Class_zero
    | 1 =>
      have hn0 : (E11 : Mat2 K) ≠ 0 := fun h => IntegralDomain.one_ne_zero (congrArg Mat2.a h)
      have hn1 : (E11 : Mat2 K) ≠ 1 := fun h => IntegralDomain.one_ne_zero (congrArg Mat2.d h).symm
      exact mat2Class_proper hn0 hn1
    | 2 => exact mat2Class_one
    | n + 3 => omega

/-- Small-rank proper coincidence: on `M₂(K)`, excluding `0` and `1` leaves EXACTLY `1 = b`
    connected component (`ProperIdemSpectrum (Mat2 K) ≃ Unit`). -/
def mat2ProperSpectrumEquivUnit : EquivBij (ProperIdemSpectrum (Mat2 K)) Unit where
  toFun := fun _ => ()
  invFun := fun _ =>
    have hn0 : (E11 : Mat2 K) ≠ 0 := fun h => IntegralDomain.one_ne_zero (congrArg Mat2.a h)
    have hn1 : (E11 : Mat2 K) ≠ 1 := fun h => IntegralDomain.one_ne_zero (congrArg Mat2.d h).symm
    Quotient.mk (properIdemSetoid (Mat2 K)) ⟨E11, isIdem_E11, hn0, hn1⟩
  left_inv := fun s => by
    refine Quotient.inductionOn s (fun e => ?_)
    apply Quotient.sound
    rcases idempotent_trichotomy e.2.1 with h0 | h1 | ⟨_, _, hdet, htr⟩
    · exact False.elim (e.2.2.1 h0)
    · exact False.elim (e.2.2.2 h1)
    · exact PolyConn.symm (polyConn_rank1_to_E11 e.2.1 hdet htr)
  right_inv := fun u => by cases u; rfl

/-- Primitive Idempotent Characterization on `M₂(K)`: over ANY field `K` (including char 2!),
    `E ∈ M₂(K)` is a primitive idempotent iff `det E = 0 ∧ tr E = 1`! -/
theorem mat2_isPrimitiveIdem_iff (E : Mat2 K) :
    IsPrimitiveIdem E ↔ IsIdem E ∧ det E = 0 ∧ tr E = 1 := by
  constructor
  · rintro ⟨hE, hne0, hprim⟩
    rcases idempotent_trichotomy hE with h0 | h1 | ⟨_, _, hdet, htr⟩
    · exact False.elim (hne0 h0)
    · -- I₂ = E₁₁ + E₂₂ is NOT primitive!
      exfalso
      have horth1 : (E11 : Mat2 K) * E22 = 0 := by
        apply ext <;> simp [E11, E22, AssocRing.one_mul', AssocRing.zero_mul, AssocRing.mul_zero, AssocRing.add_zero']
      have horth2 : (E22 : Mat2 K) * E11 = 0 := by
        apply ext <;> simp [E11, E22, AssocRing.one_mul', AssocRing.zero_mul, AssocRing.mul_zero, AssocRing.add_zero']
      have hsum : (1 : Mat2 K) = E11 + E22 := by
        apply ext <;> simp [E11, E22, AssocRing.add_zero', AssocRing.zero_add']
      rcases hprim E11 E22 isIdem_E11 isIdem_E22 horth1 horth2 (h1.trans hsum) with he11 | he22
      · exact IntegralDomain.one_ne_zero (congrArg Mat2.a he11)
      · exact IntegralDomain.one_ne_zero (congrArg Mat2.d he22)
    · exact ⟨hE, hdet, htr⟩
  · rintro ⟨hE, hdet, htr⟩
    have hne0 : E ≠ 0 := by
      intro hc; rw [hc] at htr
      change (0 : K) + 0 = 1 at htr
      rw [AssocRing.add_zero'] at htr
      exact IntegralDomain.one_ne_zero htr.symm
    refine ⟨hE, hne0, ?_⟩
    intro e₁ e₂ he₁ he₂ ho12 _ hsum
    by_cases h10 : e₁ = 0
    · exact Or.inl h10
    · right
      by_cases h20 : e₂ = 0
      · exact h20
      · exfalso
        have h1_ne_one : e₁ ≠ 1 := by
          intro hc; rw [hc, AssocRing.one_mul'] at ho12; exact h20 ho12
        have h2_ne_one : e₂ ≠ 1 := by
          intro hc; rw [hc, AssocRing.mul_one'] at ho12; exact h10 ho12
        rcases idempotent_trichotomy he₁ with hc | hc | ⟨_, _, _, htr1⟩
        · exact h10 hc
        · exact h1_ne_one hc
        · rcases idempotent_trichotomy he₂ with hc | hc | ⟨_, _, _, htr2⟩
          · exact h20 hc
          · exact h2_ne_one hc
          · have htr_sum : tr E = tr e₁ + tr e₂ := by rw [hsum, tr_add]
            rw [htr, htr1, htr2] at htr_sum
            -- 1 = 1 + 1 implies 0 = 1 in K (works in ALL characteristics, including char 2!)
            have h01 : (0 : K) = 1 := by
              apply AssocRing.add_left_cancel (a := (1 : K))
              rw [AssocRing.add_zero']
              exact htr_sum
            exact IntegralDomain.one_ne_zero h01.symm

end FieldExactSpectrum
end Mat2

/-! ## Section 6: General `n × n` Matrices `Mat n R`, Leibniz–Trace Theorem & `Cl_{m,m}` -/

def sumFin {R : Type u} [AssocRing R] {n : Nat} (f : Fin n → R) : R :=
  finSum n (fun i => if h : i < n then f ⟨i, h⟩ else 0)

section SumFinLemmas
variable {R : Type u} [AssocRing R]

theorem sumFin_add {n : Nat} (f g : Fin n → R) :
    sumFin (fun i => f i + g i) = sumFin f + sumFin g := by
  unfold sumFin
  rw [← finSum_add]
  apply finSum_congr
  intro i hi
  rw [dif_pos hi, dif_pos hi, dif_pos hi]

theorem sumFin_mul_left {n : Nat} (a : R) (f : Fin n → R) :
    a * sumFin f = sumFin (fun i => a * f i) := by
  unfold sumFin
  rw [finSum_mul_left]
  apply finSum_congr
  intro i hi
  rw [dif_pos hi, dif_pos hi]

theorem sumFin_mul_right {n : Nat} (a : R) (f : Fin n → R) :
    sumFin f * a = sumFin (fun i => f i * a) := by
  unfold sumFin
  rw [finSum_mul_right]
  apply finSum_congr
  intro i hi
  rw [dif_pos hi, dif_pos hi]

theorem sumFin_comm {m n : Nat} (h : Fin m → Fin n → R) :
    sumFin (fun i => sumFin (fun j => h i j)) =
    sumFin (fun j => sumFin (fun i => h i j)) := by
  unfold sumFin
  have lhs_eq :
      finSum m (fun i => if hi : i < m then finSum n (fun j => if hj : j < n then h ⟨i, hi⟩ ⟨j, hj⟩ else 0) else 0) =
      finSum m (fun i => finSum n (fun j => if hi : i < m then (if hj : j < n then h ⟨i, hi⟩ ⟨j, hj⟩ else 0) else 0)) := by
    apply finSum_congr
    intro i hi
    rw [dif_pos hi]
    apply finSum_congr
    intro j _
    rw [dif_pos hi]
  have rhs_eq :
      finSum n (fun j => if hj : j < n then finSum m (fun i => if hi : i < m then h ⟨i, hi⟩ ⟨j, hj⟩ else 0) else 0) =
      finSum n (fun j => finSum m (fun i => if hi : i < m then (if hj : j < n then h ⟨i, hi⟩ ⟨j, hj⟩ else 0) else 0)) := by
    apply finSum_congr
    intro j hj
    rw [dif_pos hj]
    apply finSum_congr
    intro i hi
    by_cases him : i < m
    · rw [dif_pos him, dif_pos him, dif_pos hj]
    · rw [dif_neg him, dif_neg him]
  rw [lhs_eq, rhs_eq, finSum_comm]

theorem sumFin_eq_zero {n : Nat} {f : Fin n → R} (h : ∀ i, f i = 0) : sumFin f = 0 := by
  unfold sumFin
  apply finSum_eq_zero
  intro i hi
  rw [dif_pos hi, h ⟨i, hi⟩]

theorem sumFin_single {n : Nat} (j : Fin n) (f : Fin n → R)
    (hz : ∀ i : Fin n, i ≠ j → f i = 0) : sumFin f = f j := by
  unfold sumFin
  rw [finSum_single (k := j.1) j.2]
  · rw [dif_pos j.2]
  · intro i hi hne
    rw [dif_pos hi]
    exact hz ⟨i, hi⟩ (fun heq => hne (congrArg Fin.val heq))

end SumFinLemmas

/-- General `n × n` matrix ring `M_n(R)` over any associative ring `R`. -/
structure Mat (n : Nat) (R : Type u) where
  entry : Fin n → Fin n → R

namespace Mat

theorem ext {n : Nat} {R : Type u} {A B : Mat n R}
    (h : ∀ i j : Fin n, A.entry i j = B.entry i j) : A = B := by
  cases A with
  | mk ea =>
    cases B with
    | mk eb =>
      have he : ea = eb := funext (fun i => funext (fun j => h i j))
      subst he
      rfl

section Ring
variable {n : Nat} {R : Type u} [AssocRing R]

instance : AssocRing (Mat n R) where
  add := fun A B => ⟨fun i j => A.entry i j + B.entry i j⟩
  sub := fun A B => ⟨fun i j => A.entry i j - B.entry i j⟩
  neg := fun A => ⟨fun i j => -(A.entry i j)⟩
  mul := fun A B => ⟨fun i k => sumFin (fun j => A.entry i j * B.entry j k)⟩
  zero := ⟨fun _ _ => 0⟩
  one := ⟨fun i j => if i = j then 1 else 0⟩
  sub_eq_add_neg := fun _ _ => ext (fun _ _ => AssocRing.sub_eq_add_neg _ _)
  add_assoc := fun _ _ _ => ext (fun _ _ => AssocRing.add_assoc _ _ _)
  add_comm := fun _ _ => ext (fun _ _ => AssocRing.add_comm _ _)
  zero_add := fun _ => ext (fun _ _ => AssocRing.zero_add' _)
  add_zero := fun _ => ext (fun _ _ => AssocRing.add_zero' _)
  add_left_neg := fun _ => ext (fun _ _ => AssocRing.add_left_neg' _)
  mul_assoc := fun A B C => by
    apply ext
    intro i l
    change sumFin (fun k => sumFin (fun j => A.entry i j * B.entry j k) * C.entry k l) =
           sumFin (fun j => A.entry i j * sumFin (fun k => B.entry j k * C.entry k l))
    have s1 :
        sumFin (fun k => sumFin (fun j => A.entry i j * B.entry j k) * C.entry k l) =
        sumFin (fun k => sumFin (fun j => A.entry i j * (B.entry j k * C.entry k l))) := by
      unfold sumFin
      apply finSum_congr
      intro k hk
      rw [dif_pos hk, dif_pos hk]
      dsimp only
      have hmr := sumFin_mul_right (C.entry ⟨k, hk⟩ l) (fun j => A.entry i j * B.entry j ⟨k, hk⟩)
      unfold sumFin at hmr
      rw [hmr]
      apply finSum_congr
      intro j hj
      rw [dif_pos hj, dif_pos hj]
      dsimp only
      exact AssocRing.mul_assoc _ _ _
    have s2 :
        sumFin (fun j => A.entry i j * sumFin (fun k => B.entry j k * C.entry k l)) =
        sumFin (fun j => sumFin (fun k => A.entry i j * (B.entry j k * C.entry k l))) := by
      unfold sumFin
      apply finSum_congr
      intro j hj
      rw [dif_pos hj, dif_pos hj]
      have hml := sumFin_mul_left (A.entry i ⟨j, hj⟩) (fun k => B.entry ⟨j, hj⟩ k * C.entry k l)
      unfold sumFin at hml
      exact hml
    rw [s1, s2, sumFin_comm]
  one_mul := fun A => by
    apply ext
    intro i k
    change sumFin (fun j => (if i = j then (1 : R) else 0) * A.entry j k) = A.entry i k
    rw [sumFin_single i]
    · simp [AssocRing.one_mul']
    · intro j hne
      have hij : i ≠ j := fun h => hne h.symm
      rw [if_neg hij, AssocRing.zero_mul]
  mul_one := fun A => by
    apply ext
    intro i k
    change sumFin (fun j => A.entry i j * (if j = k then (1 : R) else 0)) = A.entry i k
    rw [sumFin_single k]
    · simp [AssocRing.mul_one']
    · intro j hne
      rw [if_neg hne, AssocRing.mul_zero]
  left_distrib := fun A B C => by
    apply ext
    intro i k
    change sumFin (fun j => A.entry i j * (B.entry j k + C.entry j k)) =
           sumFin (fun j => A.entry i j * B.entry j k) + sumFin (fun j => A.entry i j * C.entry j k)
    rw [← sumFin_add]
    unfold sumFin
    apply finSum_congr
    intro j hj
    rw [dif_pos hj, dif_pos hj]
    dsimp only
    exact AssocRing.left_distrib _ _ _
  right_distrib := fun A B C => by
    apply ext
    intro i k
    change sumFin (fun j => (A.entry i j + B.entry i j) * C.entry j k) =
           sumFin (fun j => A.entry i j * C.entry j k) + sumFin (fun j => B.entry i j * C.entry j k)
    rw [← sumFin_add]
    unfold sumFin
    apply finSum_congr
    intro j hj
    rw [dif_pos hj, dif_pos hj]
    dsimp only
    exact AssocRing.right_distrib _ _ _

/-- Matrix trace `tr(A) = ∑_{i=0}^{n-1} A_{i,i}`. -/
def tr (A : Mat n R) : R := sumFin (fun i => A.entry i i)

theorem tr_zero : tr (0 : Mat n R) = 0 := sumFin_eq_zero (fun _ => rfl)

theorem tr_add (A B : Mat n R) : tr (A + B) = tr A + tr B := sumFin_add _ _

def toMatPoly (P : Poly (Mat n R)) : Mat n (Poly R) where
  entry := fun i j =>
    { coeff := fun k => (P.coeff k).entry i j
      isBounded := by
        rcases P.isBounded with ⟨N, hN⟩
        exact ⟨N, fun k hk => by rw [hN k hk]; rfl⟩ }

theorem toMatPoly_mul (P Q : Poly (Mat n R)) :
    toMatPoly (P * Q) = toMatPoly P * toMatPoly Q := by
  have entry_finSum : ∀ (i j : Fin n) (m : Nat) (g : Nat → Mat n R),
      (finSum m g).entry i j = finSum m (fun k => (g k).entry i j) := by
    intro i j m g
    induction m with
    | zero => rfl
    | succ l ih => rw [finSum_succ, finSum_succ, ← ih]; rfl
  apply ext
  intro i l
  apply Poly.ext
  intro k
  change (finSum (k + 1) (fun r => P.coeff r * Q.coeff (k - r))).entry i l =
         (sumFin (fun j => (toMatPoly P).entry i j * (toMatPoly Q).entry j l)).coeff k
  rw [entry_finSum]
  have coeff_sumFin : ∀ (m : Nat) (h : Nat → Poly R),
      (finSum m h).coeff k = finSum m (fun j => (h j).coeff k) := by
    intro m h
    induction m with
    | zero => rfl
    | succ s ih => rw [finSum_succ, Poly.coeff_add, ih, finSum_succ]
  unfold sumFin
  rw [coeff_sumFin]
  -- Swap `r` (length `k + 1`) and `j` (length `n`) via `finSum_comm`!
  have lhs_swap :
      finSum (k + 1) (fun r => (P.coeff r * Q.coeff (k - r)).entry i l) =
      finSum (k + 1) (fun r => finSum n (fun j =>
        if hj : j < n then (P.coeff r).entry i ⟨j, hj⟩ * (Q.coeff (k - r)).entry ⟨j, hj⟩ l else 0)) := by
    rfl
  rw [lhs_swap, finSum_comm]
  apply finSum_congr
  intro j hj
  rw [dif_pos hj]
  apply finSum_congr
  intro r _
  rw [dif_pos hj]
  rfl

theorem eval0_tr_toMatPoly (P : Poly (Mat n R)) :
    Poly.eval0 (tr (toMatPoly P)) = tr (Poly.eval0 P) := by
  have coeff0_finSum : ∀ (m : Nat) (h : Nat → Poly R),
      (finSum m h).coeff 0 = finSum m (fun i => (h i).coeff 0) := by
    intro m h
    induction m with
    | zero => rfl
    | succ s ih => rw [finSum_succ, Poly.coeff_add, ih, finSum_succ]
  unfold Poly.eval0 tr sumFin
  rw [coeff0_finSum]
  apply finSum_congr
  intro i hi
  rw [dif_pos hi, dif_pos hi]
  rfl

theorem eval1_tr_toMatPoly (P : Poly (Mat n R)) :
    Poly.eval1 (tr (toMatPoly P)) = tr (Poly.eval1 P) := by
  rcases P.isBounded with ⟨N, hN⟩
  have htrN : ∀ k, N ≤ k → (tr (toMatPoly P)).coeff k = 0 := by
    intro k hk
    have coeff_finSum : ∀ (m : Nat) (h : Nat → Poly R),
        (finSum m h).coeff k = finSum m (fun i => (h i).coeff k) := by
      intro m h; induction m with | zero => rfl | succ s ih => rw [finSum_succ, Poly.coeff_add, ih, finSum_succ]
    unfold tr sumFin
    rw [coeff_finSum]
    apply finSum_eq_zero
    intro i hi
    rw [dif_pos hi]
    change (P.coeff k).entry ⟨i, hi⟩ ⟨i, hi⟩ = 0
    rw [hN k hk]; rfl
  rw [Poly.eval1_eq_finSum (tr (toMatPoly P)) htrN, Poly.eval1_eq_finSum P hN]
  have entry_finSum : ∀ (i j : Fin n) (m : Nat) (g : Nat → Mat n R),
      (finSum m g).entry i j = finSum m (fun k => (g k).entry i j) := by
    intro i j m g; induction m with | zero => rfl | succ l ih => rw [finSum_succ, finSum_succ, ← ih]; rfl
  have coeff_finSum : ∀ (k m : Nat) (h : Nat → Poly R),
      (finSum m h).coeff k = finSum m (fun i => (h i).coeff k) := by
    intro k m h; induction m with | zero => rfl | succ s ih => rw [finSum_succ, Poly.coeff_add, ih, finSum_succ]
  unfold tr sumFin
  have lhs_eq :
      finSum N (fun k => (finSum n (fun i => if hi : i < n then (toMatPoly P).entry ⟨i, hi⟩ ⟨i, hi⟩ else 0)).coeff k) =
      finSum N (fun k => finSum n (fun i => if hi : i < n then (P.coeff k).entry ⟨i, hi⟩ ⟨i, hi⟩ else 0)) := by
    apply finSum_congr
    intro k _
    rw [coeff_finSum]
    apply finSum_congr
    intro i hi
    rw [dif_pos hi, dif_pos hi]
    rfl
  rw [lhs_eq, finSum_comm]
  apply finSum_congr
  intro i hi
  rw [dif_pos hi]
  dsimp only
  rw [entry_finSum]
  apply finSum_congr
  intro k _
  rw [dif_pos hi]

end Ring

section CommTraceAndLeibniz
variable {n : Nat} {K : Type u} [CommRing K]

/-- Cyclicity of trace `tr(A * B) = tr(B * A)` over any commutative ring `K`. -/
theorem tr_mul_comm (A B : Mat n K) : tr (A * B) = tr (B * A) := by
  unfold tr
  change sumFin (fun i => sumFin (fun j => A.entry i j * B.entry j i)) =
         sumFin (fun j => sumFin (fun i => B.entry j i * A.entry i j))
  rw [sumFin_comm]
  unfold sumFin
  apply finSum_congr
  intro j hj
  rw [dif_pos hj, dif_pos hj]
  apply finSum_congr
  intro i hi
  rw [dif_pos hi, dif_pos hi]
  dsimp only
  exact CommRing.mul_comm _ _

def matDeriv (M : Mat n (Poly K)) : Mat n (Poly K) where
  entry := fun i j => Poly.deriv (M.entry i j)

theorem matDeriv_mul (A B : Mat n (Poly K)) :
    matDeriv (A * B) = matDeriv A * B + A * matDeriv B := by
  have deriv_finSum : ∀ (m : Nat) (h : Nat → Poly K),
      Poly.deriv (finSum m h) = finSum m (fun j => Poly.deriv (h j)) := by
    intro m h
    induction m with
    | zero => exact Poly.deriv_zero
    | succ s ih => rw [finSum_succ, Poly.deriv_add, ih, finSum_succ]
  apply ext
  intro i l
  change Poly.deriv (sumFin (fun j => A.entry i j * B.entry j l)) =
         sumFin (fun j => Poly.deriv (A.entry i j) * B.entry j l) +
         sumFin (fun j => A.entry i j * Poly.deriv (B.entry j l))
  rw [← sumFin_add]
  unfold sumFin
  rw [deriv_finSum]
  apply finSum_congr
  intro j hj
  rw [dif_pos hj, dif_pos hj, Poly.deriv_mul]

theorem tr_matDeriv (M : Mat n (Poly K)) : tr (matDeriv M) = Poly.deriv (tr M) := by
  have deriv_finSum : ∀ (m : Nat) (h : Nat → Poly K),
      Poly.deriv (finSum m h) = finSum m (fun j => Poly.deriv (h j)) := by
    intro m h; induction m with | zero => exact Poly.deriv_zero | succ s ih => rw [finSum_succ, Poly.deriv_add, ih, finSum_succ]
  unfold tr sumFin
  rw [deriv_finSum]
  apply finSum_congr
  intro i hi
  rw [dif_pos hi, dif_pos hi]
  rfl

/-- Universal Leibniz–Trace Theorem for polynomial idempotents:
    for EVERY `n : Nat` and EVERY commutative ring `K`, if `M ∈ M_n(K[t])` satisfies
    `M * M = M`, then `D(tr(M)) = 0`! -/
theorem deriv_tr_idem_eq_zero {M : Mat n (Poly K)} (hM : M * M = M) :
    Poly.deriv (tr M) = 0 := by
  let M' := matDeriv M
  have h1 : M' = M' * M + M * M' := by
    dsimp only [M']
    conv => lhs; rw [← hM]
    exact matDeriv_mul M M
  have h2 : M * M' * M = 0 := by
    have hm : M * M' = M * (M' * M + M * M') := congrArg (fun X => M * X) h1
    rw [AssocRing.left_distrib, ← AssocRing.mul_assoc M M' M, ← AssocRing.mul_assoc M M M', hM] at hm
    -- hm : M * M' = M * M' * M + M * M'
    apply AssocRing.add_right_cancel (c := M * M')
    rw [AssocRing.zero_add']
    exact hm.symm
  have htr1 : tr (M * M') = 0 := by
    calc
      tr (M * M') = tr ((M * M) * M') := by rw [hM]
      _ = tr (M * (M * M')) := by rw [AssocRing.mul_assoc]
      _ = tr ((M * M') * M) := tr_mul_comm M (M * M')
      _ = tr 0 := by rw [h2]
      _ = 0 := tr_zero
  have htr2 : tr (M' * M) = 0 := by rw [tr_mul_comm, htr1]
  rw [← tr_matDeriv]
  change tr M' = 0
  rw [h1, tr_add, htr2, htr1, AssocRing.add_zero']

/-- Murray–von Neumann / projective left-ideal module isomorphism preserves matrix trace! -/
theorem leftIdealIso_tr_eq {E₀ E₁ : Mat n K} (he₀ : IsIdem E₀) (he₁ : IsIdem E₁)
    (hiso : Nonempty (LeftIdealIso E₀ E₁)) : tr E₀ = tr E₁ := by
  rcases (leftIdealIso_iff_murrayVonNeumann he₀ he₁).mp hiso with ⟨u, v, huv, hvu⟩
  rw [← huv, ← hvu, tr_mul_comm]

/-- Unit conjugacy `E₁ = U E₀ U⁻¹` preserves matrix trace! -/
theorem unitConj_tr_eq {E₀ E₁ : Mat n K} (he₀ : IsIdem E₀) (he₁ : IsIdem E₁)
    (hconj : UnitConj E₀ E₁) : tr E₀ = tr E₁ :=
  leftIdealIso_tr_eq he₀ he₁ (unitConj_imp_leftIdealIso he₀ he₁ hconj)

end CommTraceAndLeibniz

section TorsionFreeRankSeparation
variable {K : Type u} [TorsionFreeRing K]

/-- Over any `ℤ`-torsion-free commutative ring `K` (e.g. `ℤ`, `ℚ`, `ℝ`, `ℂ`),
    every `𝔸¹`-connected family in `M_n(K)` has CONSTANT matrix trace! -/
theorem polyConn_tr_eq {n : Nat} {E₀ E₁ : Mat n K} (hc : PolyConn E₀ E₁) :
    tr E₀ = tr E₁ := by
  induction hc with
  | refl _ => rfl
  | step hs =>
    rcases hs with ⟨P, hP, rfl, rfl⟩
    let M := toMatPoly P
    have hM : M * M = M := by
      dsimp only [M]
      rw [← toMatPoly_mul, hP]
    have hd : Poly.deriv (tr M) = 0 := deriv_tr_idem_eq_zero hM
    have hconst : tr M = Poly.const ((tr M).coeff 0) := Poly.eq_const_of_deriv_eq_zero hd
    rw [← eval0_tr_toMatPoly P, ← eval1_tr_toMatPoly P]
    change Poly.eval0 (tr M) = Poly.eval1 (tr M)
    rw [hconst, Poly.eval0_const, Poly.eval1_const]
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem natCast_injective : Injective (AssocRing.natCast : Nat → K) := by
  intro a b hab
  by_cases hlt : a < b
  · exfalso
    have hb_eq : b = a + (b - a) := by omega
    rw [hb_eq, AssocRing.natCast_add] at hab
    have hdiff : AssocRing.natCast (b - a) * (1 : K) = 0 := by
      rw [AssocRing.mul_one']
      apply AssocRing.add_left_cancel (a := (AssocRing.natCast a : K))
      rw [AssocRing.add_zero']
      exact hab.symm
    exact TorsionFreeRing.one_ne_zero
      (TorsionFreeRing.eq_zero_of_natCast_mul_eq_zero (k := b - a) (by omega) hdiff)
  · by_cases hgt : b < a
    · exfalso
      have ha_eq : a = b + (a - b) := by omega
      rw [ha_eq, AssocRing.natCast_add] at hab
      have hdiff : AssocRing.natCast (a - b) * (1 : K) = 0 := by
        rw [AssocRing.mul_one']
        apply AssocRing.add_left_cancel (a := (AssocRing.natCast b : K))
        rw [AssocRing.add_zero']
        exact hab
      exact TorsionFreeRing.one_ne_zero
        (TorsionFreeRing.eq_zero_of_natCast_mul_eq_zero (k := a - b) (by omega) hdiff)
    · omega

/-- Canonical rank-`r` diagonal projection `P_r = diag(1_r, 0_{n-r}) ∈ M_n(K)`. -/
def projMat (n r : Nat) : Mat n K where
  entry := fun i j => if i = j ∧ i.1 < r then 1 else 0

theorem isIdem_projMat (n r : Nat) : IsIdem (projMat n r : Mat n K) := by
  apply ext
  intro i l
  change sumFin (fun j => (projMat n r : Mat n K).entry i j * (projMat n r).entry j l) =
         (projMat n r).entry i l
  rw [sumFin_single i]
  · unfold projMat
    dsimp only
    by_cases hil : i = l
    · subst hil
      by_cases hir : i.1 < r
      · rw [if_pos ⟨rfl, hir⟩, AssocRing.one_mul']
      · rw [if_neg (fun h => hir h.2), AssocRing.zero_mul]
    · have h2 : ¬ (i = l ∧ i.1 < r) := fun h => hil h.1
      rw [if_neg h2, AssocRing.mul_zero]
  · intro j hji
    unfold projMat
    dsimp only
    have hij : ¬ (i = j ∧ i.1 < r) := fun h => hji h.1.symm
    rw [if_neg hij, AssocRing.zero_mul]

theorem tr_projMat {n r : Nat} (hr : r ≤ n) :
    tr (projMat n r : Mat n K) = AssocRing.natCast r := by
  unfold tr sumFin projMat
  dsimp only
  have hprefix : ∀ m : Nat, m ≤ n →
      finSum m (fun i => if hi : i < n then (if (⟨i, hi⟩ : Fin n) = ⟨i, hi⟩ ∧ i < r then (1 : K) else 0) else 0) =
      AssocRing.natCast (if m ≤ r then m else r) := by
    intro m hmn
    induction m with
    | zero => simp [finSum_zero_len, AssocRing.natCast_zero]
    | succ k ih =>
      have hkn : k < n := by omega
      rw [finSum_succ, ih (by omega), dif_pos hkn]
      by_cases hkr : k < r
      · have hk1 : k + 1 ≤ r := by omega
        have hkr_le : k ≤ r := by omega
        have hcond : (⟨k, hkn⟩ : Fin n) = ⟨k, hkn⟩ ∧ k < r := ⟨rfl, hkr⟩
        rw [if_pos hkr_le, if_pos hcond, if_pos hk1]
        rfl
      · have hk1 : ¬ (k + 1 ≤ r) := by omega
        have hncond : ¬ ((⟨k, hkn⟩ : Fin n) = ⟨k, hkn⟩ ∧ k < r) := fun h => hkr h.2
        rw [if_neg hncond, if_neg hk1, AssocRing.add_zero']
        by_cases hkr_eq : k ≤ r
        · have heq : k = r := by omega
          rw [if_pos hkr_eq, heq]
        · rw [if_neg hkr_eq]
  rw [hprefix n (Nat.le_refl n)]
  by_cases hnr : n ≤ r
  · have heq : n = r := by omega
    rw [if_pos hnr, heq]
  · rw [if_neg hnr]

theorem isProperIdem_projMat {n r : Nat} (hr1 : 1 ≤ r) (hrn : r < n) :
    IsProperIdem (projMat n r : Mat n K) := by
  refine ⟨isIdem_projMat n r, ?_, ?_⟩
  · intro h0
    let idx0 : Fin n := ⟨0, by omega⟩
    have he0 : (projMat n r : Mat n K).entry idx0 idx0 = (0 : Mat n K).entry idx0 idx0 :=
      congrArg (fun M => M.entry idx0 idx0) h0
    unfold projMat at he0
    dsimp only [idx0] at he0
    rw [if_pos ⟨rfl, by omega⟩] at he0
    exact TorsionFreeRing.one_ne_zero he0
  · intro h1
    let idxr : Fin n := ⟨r, hrn⟩
    have her : (projMat n r : Mat n K).entry idxr idxr = (1 : Mat n K).entry idxr idxr :=
      congrArg (fun M => M.entry idxr idxr) h1
    unfold projMat at her
    change (if idxr = idxr ∧ r < r then (1 : K) else 0) = (if idxr = idxr then 1 else 0) at her
    rw [if_neg (fun h => Nat.lt_irrefl r h.2), if_pos rfl] at her
    exact TorsionFreeRing.one_ne_zero her.symm

/-- Single-block injection `Fin (n + 1) ↪ IdemSpectrum (Mat n K)`:
    for EVERY `n ≥ 1`, `M_n(K)` (`b = 1` matrix block!) has at least `n + 1 > 1`
    pairwise `𝔸¹`-disconnected idempotent families! -/
def singleBlockAllMap (n : Nat) (idx : Fin (n + 1)) : IdemSpectrum (Mat n K) :=
  Quotient.mk (idemSetoid (Mat n K)) ⟨projMat n idx.1, isIdem_projMat n idx.1⟩

theorem singleBlockAllMap_injective (n : Nat) :
    Injective (singleBlockAllMap n : Fin (n + 1) → IdemSpectrum (Mat n K)) := by
  intro i j hij
  have hconn : PolyConn (projMat n i.1 : Mat n K) (projMat n j.1) := Quotient.exact hij
  have htr : tr (projMat n i.1 : Mat n K) = tr (projMat n j.1 : Mat n K) := polyConn_tr_eq hconn
  rw [tr_projMat (by omega), tr_projMat (by omega)] at htr
  exact Fin.ext (natCast_injective i.1 j.1 htr)

/-- Distinct-rank projections `P_r, P_s` (`r ≠ s`) in `M_n(K)` generate non-isomorphic
    projective left ideals `M_n(K) P_r ≇ M_n(K) P_s` AND are non-conjugate! -/
theorem projMat_not_leftIdealIso {n r s : Nat} (hr : r ≤ n) (hs : s ≤ n) (hne : r ≠ s) :
    ¬ Nonempty (LeftIdealIso (projMat n r : Mat n K) (projMat n s)) := by
  intro hiso
  have htr := leftIdealIso_tr_eq (isIdem_projMat n r) (isIdem_projMat n s) hiso
  rw [tr_projMat hr, tr_projMat hs] at htr
  exact hne (natCast_injective r s htr)

/-- Refutation of Clause II EVEN FOR PROPER IDEMPOTENTS (`e ∉ {0, 1}`) on a single matrix block:
    for EVERY `n ≥ 3` (including `M₃(K)` with `2 > 1` and `Cl_{2,2}(K) ≅ M₄(K)` with `3 > 1`),
    `M_n(K)` has `b = 1` single matrix block yet at least `n - 1 ≥ 2 > 1 = b` pairwise
    `𝔸¹`-disconnected proper idempotent families! -/
def singleBlockProperMap {n : Nat} (hn : 3 ≤ n) (idx : Fin (n - 1)) :
    ProperIdemSpectrum (Mat n K) :=
  Quotient.mk (properIdemSetoid (Mat n K))
    ⟨projMat n (idx.1 + 1), isProperIdem_projMat (by omega) (by omega)⟩

theorem singleBlockProperMap_injective {n : Nat} (hn : 3 ≤ n) :
    Injective (singleBlockProperMap hn : Fin (n - 1) → ProperIdemSpectrum (Mat n K)) := by
  intro i j hij
  have hconn : PolyConn (projMat n (i.1 + 1) : Mat n K) (projMat n (j.1 + 1)) := Quotient.exact hij
  have htr : tr (projMat n (i.1 + 1) : Mat n K) = tr (projMat n (j.1 + 1) : Mat n K) := polyConn_tr_eq hconn
  rw [tr_projMat (by omega), tr_projMat (by omega)] at htr
  have hval : i.1 + 1 = j.1 + 1 := natCast_injective (i.1 + 1) (j.1 + 1) htr
  exact Fin.ext (by omega)

/-- Concrete `Cl_{2,2}(K) ≅ M₄(K)` Nontrivial Counterexample (`b = 1`, `≥ 3 > 1` proper components). -/
theorem clifford22_proper_three_gt_one :
    3 > 1 ∧ ∃ f : Fin 3 → ProperIdemSpectrum (Mat 4 K), Injective f :=
  ⟨by decide, singleBlockProperMap (n := 4) (by decide), singleBlockProperMap_injective (n := 4) (by decide)⟩

private theorem two_pow_gt_self_aux (n : Nat) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ k ih =>
    have hp : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
    omega

/-- Unbounded Split-Clifford Divergence Theorem (`Cl_{m,m}(K) ≅ M_{2^m}(K)`):
    No function `F(b)` of the matrix-block count `b` alone can bound `|π₀(E°(A))|`!
    Along `M_{2^m}(K)`, `b = 1` stays constant while proper idempotent connected
    components exceed ANY prescribed natural number `M`. -/
theorem split_clifford_unbounded_proper_spectrum (M : Nat) :
    ∃ m : Nat, M < 2 ^ m - 1 ∧ 3 ≤ 2 ^ m ∧
      ∃ h : 3 ≤ 2 ^ m, Injective (singleBlockProperMap h : Fin (2 ^ m - 1) → ProperIdemSpectrum (Mat (2 ^ m) K)) := by
  let m := M + 2
  have hpow : M + 2 < 2 ^ (M + 2) := two_pow_gt_self_aux (M + 2)
  have hge3 : 3 ≤ 2 ^ m := by dsimp only [m]; omega
  refine ⟨m, by dsimp only [m]; omega, hge3, hge3, singleBlockProperMap_injective hge3⟩

end TorsionFreeRankSeparation
end Mat

/-! ## Section 7: Multi-Block Algebras, Exact `2^b` & `3^b` Spectra, Sporadic Classification,
    Clause III Disproof, Primitive Idempotent Salvage, and Infinite-Dimensional Disproof -/

/-- Dependent product ring `∏_{i : ι} B i` (covers inhomogeneous Artin–Wedderburn products
    `∏_{i=1}^b M_{n_i}(K)`, homogeneous products `R^b`, and infinite products `ℤ^ℕ`). -/
structure PiRing {ι : Type v} (B : ι → Type u) where
  val : (i : ι) → B i

namespace PiRing

theorem ext {ι : Type v} {B : ι → Type u} {x y : PiRing B}
    (h : ∀ i : ι, x.val i = y.val i) : x = y := by
  cases x with
  | mk vx =>
    cases y with
    | mk vy =>
      have hv : vx = vy := funext h
      subst hv
      rfl

section GeneralProduct
variable {ι : Type v} {B : ι → Type u} [∀ i, AssocRing (B i)]

instance : AssocRing (PiRing B) where
  add := fun x y => ⟨fun i => x.val i + y.val i⟩
  sub := fun x y => ⟨fun i => x.val i - y.val i⟩
  neg := fun x => ⟨fun i => -(x.val i)⟩
  mul := fun x y => ⟨fun i => x.val i * y.val i⟩
  zero := ⟨fun _ => 0⟩
  one := ⟨fun _ => 1⟩
  sub_eq_add_neg := fun _ _ => ext (fun _ => AssocRing.sub_eq_add_neg _ _)
  add_assoc := fun _ _ _ => ext (fun _ => AssocRing.add_assoc _ _ _)
  add_comm := fun _ _ => ext (fun _ => AssocRing.add_comm _ _)
  zero_add := fun _ => ext (fun _ => AssocRing.zero_add' _)
  add_zero := fun _ => ext (fun _ => AssocRing.add_zero' _)
  add_left_neg := fun _ => ext (fun _ => AssocRing.add_left_neg' _)
  mul_assoc := fun _ _ _ => ext (fun _ => AssocRing.mul_assoc _ _ _)
  one_mul := fun _ => ext (fun _ => AssocRing.one_mul' _)
  mul_one := fun _ => ext (fun _ => AssocRing.mul_one' _)
  left_distrib := fun _ _ _ => ext (fun _ => AssocRing.left_distrib _ _ _)
  right_distrib := fun _ _ _ => ext (fun _ => AssocRing.right_distrib _ _ _)

def coordPoly (i : ι) (P : Poly (PiRing B)) : Poly (B i) where
  coeff := fun k => (P.coeff k).val i
  isBounded := by
    rcases P.isBounded with ⟨N, hN⟩
    exact ⟨N, fun k hk => by rw [hN k hk]; rfl⟩

theorem coordPoly_mul (i : ι) (P Q : Poly (PiRing B)) :
    coordPoly i (P * Q) = coordPoly i P * coordPoly i Q := by
  have val_finSum : ∀ (m : Nat) (g : Nat → PiRing B),
      (finSum m g).val i = finSum m (fun k => (g k).val i) := by
    intro m g; induction m with | zero => rfl | succ s ih => rw [finSum_succ, finSum_succ, ← ih]; rfl
  apply Poly.ext
  intro k
  change (finSum (k + 1) (fun r => P.coeff r * Q.coeff (k - r))).val i =
         finSum (k + 1) (fun r => (P.coeff r).val i * (Q.coeff (k - r)).val i)
  rw [val_finSum]
  rfl

theorem eval1_coordPoly (i : ι) (P : Poly (PiRing B)) :
    Poly.eval1 (coordPoly i P) = (Poly.eval1 P).val i := by
  rcases P.isBounded with ⟨N, hN⟩
  have hcN : ∀ k, N ≤ k → (coordPoly i P).coeff k = 0 := by
    intro k hk; change (P.coeff k).val i = 0; rw [hN k hk]; rfl
  rw [Poly.eval1_eq_finSum (coordPoly i P) hcN, Poly.eval1_eq_finSum P hN]
  have val_finSum : ∀ (m : Nat) (g : Nat → PiRing B),
      (finSum m g).val i = finSum m (fun k => (g k).val i) := by
    intro m g; induction m with | zero => rfl | succ s ih => rw [finSum_succ, finSum_succ, ← ih]; rfl
  exact (val_finSum N P.coeff).symm

@[simp] theorem zero_val (i : ι) : (0 : PiRing B).val i = 0 := rfl
@[simp] theorem one_val (i : ι) : (1 : PiRing B).val i = 1 := rfl
@[simp] theorem add_val (x y : PiRing B) (i : ι) : (x + y).val i = x.val i + y.val i := rfl
@[simp] theorem mul_val (x y : PiRing B) (i : ι) : (x * y).val i = x.val i * y.val i := rfl

theorem isIdem_val {x : PiRing B} (hx : IsIdem x) (i : ι) : IsIdem (x.val i) :=
  congrArg (fun z : PiRing B => z.val i) hx

/-- Coordinate projection preserves `PolyConn` on arbitrary (finite or infinite!) products! -/
theorem polyConn_coord {x y : PiRing B} (hc : PolyConn x y) (i : ι) :
    PolyConn (x.val i) (y.val i) := by
  induction hc with
  | refl hx => exact PolyConn.refl (isIdem_val hx i)
  | step hs =>
    rcases hs with ⟨P, hP, rfl, rfl⟩
    apply PolyConn.step
    refine ⟨coordPoly i P, ?_, rfl, eval1_coordPoly i P⟩
    unfold IsIdem
    rw [← coordPoly_mul, hP]
  | symm _ ih => exact PolyConn.symm ih
  | trans _ _ ih1 ih2 => exact PolyConn.trans ih1 ih2

end GeneralProduct
end PiRing

/-- Inhomogeneous Artin–Wedderburn multi-block matrix algebra `⨁_{i=0}^{b-1} M_{dims i}(K)`. -/
abbrev BlockAlg (b : Nat) (dims : Fin b → Nat) (K : Type u) :=
  PiRing (fun i : Fin b => Mat (dims i) K)

section MultiBlockInjection
variable {K : Type u} [TorsionFreeRing K]

/-- Multi-rank diagonal idempotents `((i : Fin b) → Fin (dims i + 1)) ↪ IdemSpectrum (BlockAlg b dims K)`
    giving at least `∏_{i=1}^b (dims i + 1)` pairwise `𝔸¹`-disconnected idempotent families! -/
def multiBlockMap {b : Nat} (dims : Fin b → Nat)
    (ranks : (i : Fin b) → Fin (dims i + 1)) : IdemSpectrum (BlockAlg b dims K) :=
  Quotient.mk (idemSetoid (BlockAlg b dims K))
    ⟨⟨fun i => Mat.projMat (dims i) (ranks i).1⟩,
     PiRing.ext (fun i => Mat.isIdem_projMat (dims i) (ranks i).1)⟩

theorem multiBlockMap_injective {b : Nat} (dims : Fin b → Nat) :
    Injective (multiBlockMap dims : ((i : Fin b) → Fin (dims i + 1)) → IdemSpectrum (BlockAlg b dims K)) := by
  intro r₁ r₂ heq
  have hconn : PolyConn (⟨fun i => Mat.projMat (dims i) (r₁ i).1⟩ : BlockAlg b dims K)
                        ⟨fun i => Mat.projMat (dims i) (r₂ i).1⟩ := Quotient.exact heq
  funext i
  have hci : PolyConn (Mat.projMat (dims i) (r₁ i).1 : Mat (dims i) K)
                      (Mat.projMat (dims i) (r₂ i).1) := PiRing.polyConn_coord hconn i
  have htr := Mat.polyConn_tr_eq hci
  have hle1 : (r₁ i).1 ≤ dims i := by have := (r₁ i).2; omega
  have hle2 : (r₂ i).1 ≤ dims i := by have := (r₂ i).2; omega
  rw [Mat.tr_projMat hle1, Mat.tr_projMat hle2] at htr
  exact Fin.ext (Mat.natCast_injective _ _ htr)

end MultiBlockInjection

/-! ### Homogeneous Finite Products `PowRing b R` (`R^b`), Exact `2^b` & `3^b` Bijections & Salvage -/

abbrev PowRing (b : Nat) (R : Type u) := PiRing (fun _ : Fin b => R)

namespace PowRing
section FiniteProductConn
variable {b : Nat} {R : Type u} [AssocRing R]

def upd (x : PowRing b R) (i₀ : Fin b) (v : R) : PowRing b R where
  val := fun j => if j = i₀ then v else x.val j

theorem polyConn_upd {x : PowRing b R} (hx : IsIdem x) (i₀ : Fin b) {u v : R}
    (huv : PolyConn u v) : PolyConn (upd x i₀ u) (upd x i₀ v) := by
  induction huv with
  | refl hu =>
    apply PolyConn.refl
    apply PiRing.ext
    intro j
    rw [PiRing.mul_val]
    dsimp only [upd]
    by_cases hj : j = i₀
    · rw [if_pos hj]; exact hu
    · rw [if_neg hj]; exact PiRing.isIdem_val hx j
  | step hs =>
    rcases hs with ⟨P, hP, rfl, rfl⟩
    apply PolyConn.step
    let Q : Poly (PowRing b R) :=
      { coeff := fun k => ⟨fun j => if j = i₀ then P.coeff k else (Poly.const (x.val j)).coeff k⟩
        isBounded := by
          rcases P.isBounded with ⟨N, hN⟩
          refine ⟨N + 1, fun k hk => PiRing.ext (fun j => ?_)⟩
          change (if j = i₀ then P.coeff k else (Poly.const (x.val j)).coeff k) = 0
          by_cases hj : j = i₀
          · rw [if_pos hj]; exact hN k (by omega)
          · rw [if_neg hj, Poly.coeff_const, if_neg (by omega)] }
    refine ⟨Q, ?_, ?_, ?_⟩
    · unfold IsIdem
      apply Poly.ext
      intro k
      apply PiRing.ext
      intro j
      have hc : (PiRing.coordPoly j (Q * Q)).coeff k = (PiRing.coordPoly j Q).coeff k := by
        rw [PiRing.coordPoly_mul]
        by_cases hj : j = i₀
        · have hQ : PiRing.coordPoly j Q = P := by
            apply Poly.ext; intro m; change (if j = i₀ then P.coeff m else _) = P.coeff m; rw [if_pos hj]
          rw [hQ, hP]
        · have hQ : PiRing.coordPoly j Q = Poly.const (x.val j) := by
            apply Poly.ext; intro m; change (if j = i₀ then _ else _) = _; rw [if_neg hj]
          have hxj : x.val j * x.val j = x.val j := PiRing.isIdem_val hx j
          rw [hQ, ← Poly.const_mul, hxj]
      exact hc
    · apply PiRing.ext
      intro j
      change (if j = i₀ then P.coeff 0 else (Poly.const (x.val j)).coeff 0) =
             (if j = i₀ then Poly.eval0 P else x.val j)
      by_cases hj : j = i₀
      · rw [if_pos hj, if_pos hj]; rfl
      · rw [if_neg hj, if_neg hj]; rfl
    · apply PiRing.ext
      intro j
      rw [← PiRing.eval1_coordPoly j Q]
      change Poly.eval1 (PiRing.coordPoly j Q) = (if j = i₀ then Poly.eval1 P else x.val j)
      by_cases hj : j = i₀
      · have hQ : PiRing.coordPoly j Q = P := by
          apply Poly.ext; intro m; change (if j = i₀ then _ else _) = _; rw [if_pos hj]
        rw [hQ, if_pos hj]
      · have hQ : PiRing.coordPoly j Q = Poly.const (x.val j) := by
          apply Poly.ext; intro m; change (if j = i₀ then _ else _) = _; rw [if_neg hj]
        rw [hQ, if_neg hj, Poly.eval1_const]
  | symm _ ih => exact PolyConn.symm ih
  | trans _ _ ih1 ih2 => exact PolyConn.trans ih1 ih2

def hybrid (x y : PowRing b R) (k : Nat) : PowRing b R where
  val := fun i => if i.1 < k then y.val i else x.val i

theorem isIdem_hybrid {x y : PowRing b R} (hx : IsIdem x) (hy : IsIdem y) (k : Nat) :
    IsIdem (hybrid x y k) := by
  apply PiRing.ext
  intro i
  change (if i.1 < k then y.val i else x.val i) * (if i.1 < k then y.val i else x.val i) =
         (if i.1 < k then y.val i else x.val i)
  by_cases hik : i.1 < k
  · rw [if_pos hik]; exact congrArg (fun z => z.val i) hy
  · rw [if_neg hik]; exact congrArg (fun z => z.val i) hx

/-- Exact Product Connectedness Characterization:
    in `R^b`, two idempotents are `𝔸¹`-connected iff ALL `b` coordinates are `𝔸¹`-connected! -/
theorem polyConn_iff_forall {x y : PowRing b R} (hx : IsIdem x) (hy : IsIdem y) :
    PolyConn x y ↔ ∀ i : Fin b, PolyConn (x.val i) (y.val i) := by
  constructor
  · exact PiRing.polyConn_coord
  · intro hall
    have hstep : ∀ k : Nat, k ≤ b → PolyConn x (hybrid x y k) := by
      intro k hk
      induction k with
      | zero =>
        have h0 : hybrid x y 0 = x := PiRing.ext (fun i => by dsimp only [hybrid]; exact if_neg (Nat.not_lt_zero i.1))
        rw [h0]
        exact PolyConn.refl hx
      | succ m ih =>
        have hmb : m < b := by omega
        let idx : Fin b := ⟨m, hmb⟩
        have hprev : PolyConn x (hybrid x y m) := ih (by omega)
        have h1 : upd (hybrid x y m) idx (x.val idx) = hybrid x y m := by
          apply PiRing.ext
          intro j
          change (if j = idx then x.val idx else (if j.1 < m then y.val j else x.val j)) =
                 (if j.1 < m then y.val j else x.val j)
          by_cases hj : j = idx
          · subst hj; simp [idx]
          · rw [if_neg hj]
        have h2 : upd (hybrid x y m) idx (y.val idx) = hybrid x y (m + 1) := by
          apply PiRing.ext
          intro j
          change (if j = idx then y.val idx else (if j.1 < m then y.val j else x.val j)) =
                 (if j.1 < m + 1 then y.val j else x.val j)
          by_cases hj : j = idx
          · subst hj; simp [idx]
          · rw [if_neg hj]
            have hne_val : j.1 ≠ m := fun hv => hj (Fin.ext hv)
            by_cases hjm : j.1 < m
            · rw [if_pos hjm, if_pos (by omega)]
            · rw [if_neg hjm, if_neg (by omega)]
        have hupd : PolyConn (hybrid x y m) (hybrid x y (m + 1)) := by
          rw [← h1, ← h2]
          exact polyConn_upd (isIdem_hybrid hx hy m) idx (hall idx)
        exact PolyConn.trans hprev hupd
    have hb : hybrid x y b = y := PiRing.ext (fun i => if_pos i.2)
    rw [← hb]
    exact hstep b (Nat.le_refl b)

private theorem quot_exists_rep {α : Type u} {s : Setoid α} (q : Quotient s) :
    ∃ x : α, Quotient.mk s x = q :=
  Quotient.inductionOn q (fun x => ⟨x, rfl⟩)

/-- Universal Product Spectrum Bijection `IdemSpectrum (PowRing b R) ≃ (Fin b → IdemSpectrum R)`! -/
noncomputable def powSpectrumEquiv (b : Nat) (R : Type u) [AssocRing R] :
    EquivBij (IdemSpectrum (PowRing b R)) (Fin b → IdemSpectrum R) where
  toFun := Quotient.lift
    (fun e i => Quotient.mk (idemSetoid R) ⟨e.1.val i, PiRing.isIdem_val e.2 i⟩)
    (fun _ _ h => funext (fun i => Quotient.sound (PiRing.polyConn_coord h i)))
  invFun := fun f =>
    Quotient.mk (idemSetoid (PowRing b R))
      ⟨⟨fun i => (Classical.choose (quot_exists_rep (f i))).1⟩,
       PiRing.ext (fun i => by
         rw [PiRing.mul_val]
         exact (Classical.choose (quot_exists_rep (f i))).2)⟩
  left_inv := fun s => by
    refine Quotient.inductionOn s (fun e => ?_)
    apply Quotient.sound
    let rep : Fin b → IdemElem R := fun i =>
      Classical.choose (quot_exists_rep (Quotient.mk (idemSetoid R) ⟨e.1.val i, PiRing.isIdem_val e.2 i⟩))
    have hrep_idem : IsIdem (⟨fun i => (rep i).1⟩ : PowRing b R) :=
      PiRing.ext (fun i => by rw [PiRing.mul_val]; exact (rep i).2)
    change PolyConn ⟨fun i => (rep i).1⟩ e.1
    rw [polyConn_iff_forall hrep_idem e.2]
    intro i
    have hspec := Classical.choose_spec (quot_exists_rep (Quotient.mk (idemSetoid R) ⟨e.1.val i, PiRing.isIdem_val e.2 i⟩))
    exact Quotient.exact hspec
  right_inv := fun f => by
    funext i
    exact Classical.choose_spec (quot_exists_rep (f i))

end FiniteProductConn
end PowRing

theorem domain_polyConn_eq {D : Type u} [IntegralDomain D] {a b : D} (hc : PolyConn a b) :
    a = b := by
  induction hc with
  | refl _ => rfl
  | step hs =>
    rcases hs with ⟨P, hP, rfl, rfl⟩
    rcases Poly.idem_eq_zero_or_one_of_domain hP with hz | ho
    · rw [hz, Poly.eval0_zero, Poly.eval1_zero]
    · rw [ho, Poly.eval0_one, Poly.eval1_one]
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### Commutative / Central `b`-Block Spectrum (`PowRing b K ≃ Fin b → Bool`, `2^b > b`) -/

section CommutativeBlocks
variable {K : Type u} [IntegralDomain K]

noncomputable def domainIdemSpectrumEquivBool : EquivBij (IdemSpectrum K) Bool where
  toFun := Quotient.lift
    (fun e => UpperTri2.isOneBool e.1)
    (fun _ _ hc => by
      dsimp only
      rw [domain_polyConn_eq hc])
  invFun := fun bl =>
    Quotient.mk (idemSetoid K)
      ⟨if bl then 1 else 0, by cases bl <;> simp [isIdem_zero, isIdem_one]⟩
  left_inv := fun s => by
    refine Quotient.inductionOn s (fun e => ?_)
    apply Quotient.sound
    rcases Poly.idem_eq_zero_or_one_of_domain e.2 with h0 | h1
    · change PolyConn (if UpperTri2.isOneBool e.1 then (1 : K) else 0) e.1
      rw [h0, UpperTri2.isOneBool_zero]
      exact PolyConn.refl isIdem_zero
    · change PolyConn (if UpperTri2.isOneBool e.1 then (1 : K) else 0) e.1
      rw [h1, UpperTri2.isOneBool_one]
      exact PolyConn.refl isIdem_one
  right_inv := fun bl => by
    cases bl
    · exact UpperTri2.isOneBool_zero
    · exact UpperTri2.isOneBool_one

/-- Exact `2^b`-Element Connected-Family Spectrum for `K^b` (and for central idempotents):
    `IdemSpectrum (PowRing b K) ≃ (Fin b → Bool)`. -/
noncomputable def commBlockSpectrumEquiv (b : Nat) :
    EquivBij (IdemSpectrum (PowRing b K)) (Fin b → Bool) where
  toFun := fun s i => domainIdemSpectrumEquivBool.toFun ((PowRing.powSpectrumEquiv b K).toFun s i)
  invFun := fun f => (PowRing.powSpectrumEquiv b K).invFun (fun i => domainIdemSpectrumEquivBool.invFun (f i))
  left_inv := fun s => by
    have h1 : (fun i => domainIdemSpectrumEquivBool.invFun (domainIdemSpectrumEquivBool.toFun ((PowRing.powSpectrumEquiv b K).toFun s i))) =
        (PowRing.powSpectrumEquiv b K).toFun s :=
      funext (fun i => domainIdemSpectrumEquivBool.left_inv _)
    rw [h1]
    exact (PowRing.powSpectrumEquiv b K).left_inv s
  right_inv := fun f => by
    funext i
    rw [(PowRing.powSpectrumEquiv b K).right_inv]
    exact domainIdemSpectrumEquivBool.right_inv (f i)

/-- Every idempotent in commutative `PowRing b K` is CENTRAL (`IsCentralIdem`). -/
theorem powRing_comm_isCentralIdem {b : Nat} {e : PowRing b K} (he : IsIdem e) :
    IsCentralIdem e :=
  ⟨he, fun x => PiRing.ext (fun i => CommRing.mul_comm (e.val i) (x.val i))⟩

end CommutativeBlocks

/-! ### Exact `3^b`-Component Spectrum on `(M₂(K))^b` (e.g. `Cl_{2,1}(K) ≅ M₂(K) × M₂(K)`) -/

noncomputable def mat2PowSpectrumEquiv {K : Type u} [Field K] (b : Nat) :
    EquivBij (IdemSpectrum (PowRing b (Mat2 K))) (Fin b → Fin 3) where
  toFun := fun s i => Mat2.mat2IdemSpectrumEquivFin3.toFun ((PowRing.powSpectrumEquiv b (Mat2 K)).toFun s i)
  invFun := fun f => (PowRing.powSpectrumEquiv b (Mat2 K)).invFun (fun i => Mat2.mat2IdemSpectrumEquivFin3.invFun (f i))
  left_inv := fun s => by
    have h1 : (fun i => Mat2.mat2IdemSpectrumEquivFin3.invFun (Mat2.mat2IdemSpectrumEquivFin3.toFun ((PowRing.powSpectrumEquiv b (Mat2 K)).toFun s i))) =
        (PowRing.powSpectrumEquiv b (Mat2 K)).toFun s :=
      funext (fun i => Mat2.mat2IdemSpectrumEquivFin3.left_inv _)
    rw [h1]
    exact (PowRing.powSpectrumEquiv b (Mat2 K)).left_inv s
  right_inv := fun f => by
    funext i
    rw [(PowRing.powSpectrumEquiv b (Mat2 K)).right_inv]
    exact Mat2.mat2IdemSpectrumEquivFin3.right_inv (f i)

/-! ### Primitive Idempotent Salvage Theorem (`|π₀(Prim(E(A)))| = b`) -/

section PrimitiveSalvage

/-- In any finite product `PowRing b R`, an element `e` is a primitive idempotent iff it is
    supported on a UNIQUE block `i₀ : Fin b` where `e.val i₀` is a primitive idempotent of `R`! -/
theorem powRing_isPrimitiveIdem_iff {b : Nat} {R : Type u} [AssocRing R] (e : PowRing b R) :
    IsPrimitiveIdem e ↔
    ∃ i₀ : Fin b, IsPrimitiveIdem (e.val i₀) ∧ ∀ j : Fin b, j ≠ i₀ → e.val j = 0 := by
  constructor
  · rintro ⟨he, hne0, hprim⟩
    have hex_nz : ∃ i₀ : Fin b, e.val i₀ ≠ 0 := by
      by_cases hex : ∃ i₀ : Fin b, e.val i₀ ≠ 0
      · exact hex
      · exfalso; apply hne0; apply PiRing.ext; intro i
        by_cases hi : e.val i = 0
        · exact hi
        · exact False.elim (hex ⟨i, hi⟩)
    rcases hex_nz with ⟨i₀, hi₀⟩
    have hall_other : ∀ j : Fin b, j ≠ i₀ → e.val j = 0 := by
      intro j hj
      by_cases hej : e.val j = 0
      · exact hej
      · exfalso
        let e₁ : PowRing b R := ⟨fun k => if k = i₀ then e.val k else 0⟩
        let e₂ : PowRing b R := ⟨fun k => if k = i₀ then 0 else e.val k⟩
        have he1_idem : IsIdem e₁ := PiRing.ext (fun k => by
          rw [PiRing.mul_val]; dsimp only [e₁]; by_cases hk : k = i₀
          · rw [if_pos hk]; exact PiRing.isIdem_val he k
          · rw [if_neg hk]; exact AssocRing.zero_mul (0 : R))
        have he2_idem : IsIdem e₂ := PiRing.ext (fun k => by
          rw [PiRing.mul_val]; dsimp only [e₂]; by_cases hk : k = i₀
          · rw [if_pos hk]; exact AssocRing.zero_mul (0 : R)
          · rw [if_neg hk]; exact PiRing.isIdem_val he k)
        have ho12 : e₁ * e₂ = 0 := PiRing.ext (fun k => by
          change (if k = i₀ then e.val k else 0) * (if k = i₀ then 0 else e.val k) = 0
          by_cases hk : k = i₀
          · rw [if_pos hk, if_pos hk, AssocRing.mul_zero]
          · rw [if_neg hk, AssocRing.zero_mul])
        have ho21 : e₂ * e₁ = 0 := PiRing.ext (fun k => by
          change (if k = i₀ then 0 else e.val k) * (if k = i₀ then e.val k else 0) = 0
          by_cases hk : k = i₀
          · rw [if_pos hk, AssocRing.zero_mul]
          · rw [if_neg hk, if_neg hk, AssocRing.mul_zero])
        have hsum : e = e₁ + e₂ := PiRing.ext (fun k => by
          change e.val k = (if k = i₀ then e.val k else 0) + (if k = i₀ then 0 else e.val k)
          by_cases hk : k = i₀
          · rw [if_pos hk, if_pos hk, AssocRing.add_zero']
          · rw [if_neg hk, if_neg hk, AssocRing.zero_add'])
        rcases hprim e₁ e₂ he1_idem he2_idem ho12 ho21 hsum with h1z | h2z
        · have hc := congrArg (fun z : PowRing b R => z.val i₀) h1z
          dsimp only [e₁] at hc; rw [if_pos rfl] at hc; exact hi₀ hc
        · have hc := congrArg (fun z : PowRing b R => z.val j) h2z
          dsimp only [e₂] at hc; rw [if_neg hj] at hc; exact hej hc
    refine ⟨i₀, ⟨PiRing.isIdem_val he i₀, hi₀, ?_⟩, hall_other⟩
    intro u₁ u₂ hu₁ hu₂ hou12 hou21 husum
    let f₁ : PowRing b R := ⟨fun k => if k = i₀ then u₁ else 0⟩
    let f₂ : PowRing b R := ⟨fun k => if k = i₀ then u₂ else 0⟩
    have hf1 : IsIdem f₁ := PiRing.ext (fun k => by
      rw [PiRing.mul_val]; dsimp only [f₁]; by_cases hk : k = i₀
      · rw [if_pos hk]; exact hu₁
      · rw [if_neg hk]; exact AssocRing.zero_mul (0 : R))
    have hf2 : IsIdem f₂ := PiRing.ext (fun k => by
      rw [PiRing.mul_val]; dsimp only [f₂]; by_cases hk : k = i₀
      · rw [if_pos hk]; exact hu₂
      · rw [if_neg hk]; exact AssocRing.zero_mul (0 : R))
    have hfo12 : f₁ * f₂ = 0 := PiRing.ext (fun k => by
      change (if k = i₀ then u₁ else 0) * (if k = i₀ then u₂ else 0) = 0
      by_cases hk : k = i₀
      · rw [if_pos hk, if_pos hk]; exact hou12
      · rw [if_neg hk, AssocRing.zero_mul])
    have hfo21 : f₂ * f₁ = 0 := PiRing.ext (fun k => by
      change (if k = i₀ then u₂ else 0) * (if k = i₀ then u₁ else 0) = 0
      by_cases hk : k = i₀
      · rw [if_pos hk, if_pos hk]; exact hou21
      · rw [if_neg hk, AssocRing.zero_mul])
    have hfsum : e = f₁ + f₂ := PiRing.ext (fun k => by
      change e.val k = (if k = i₀ then u₁ else 0) + (if k = i₀ then u₂ else 0)
      by_cases hk : k = i₀
      · subst hk; rw [if_pos rfl, if_pos rfl]; exact husum
      · rw [if_neg hk, if_neg hk, AssocRing.add_zero', hall_other k hk])
    rcases hprim f₁ f₂ hf1 hf2 hfo12 hfo21 hfsum with h1z | h2z
    · left; have hc := congrArg (fun z => z.val i₀) h1z; dsimp only [f₁] at hc; rw [if_pos rfl] at hc; exact hc
    · right; have hc := congrArg (fun z => z.val i₀) h2z; dsimp only [f₂] at hc; rw [if_pos rfl] at hc; exact hc
  · rintro ⟨i₀, ⟨hi₀_idem, hi₀_ne, hi₀_prim⟩, hall_other⟩
    have he : IsIdem e := PiRing.ext (fun j => by
      by_cases hj : j = i₀
      · subst hj; exact hi₀_idem
      · change e.val j * e.val j = e.val j; rw [hall_other j hj, AssocRing.zero_mul])
    have hne : e ≠ 0 := fun hc => hi₀_ne (congrArg (fun z => z.val i₀) hc)
    refine ⟨he, hne, ?_⟩
    intro e₁ e₂ he₁ he₂ ho12 ho21 hsum
    -- For j ≠ i₀, e₁.val j + e₂.val j = 0 and e₁.val j * e₂.val j = 0, so e₁.val j = (e₁.val j)² = 0!
    have hother_zero : ∀ j : Fin b, j ≠ i₀ → e₁.val j = 0 ∧ e₂.val j = 0 := by
      intro j hj
      have hsj : e₁.val j + e₂.val j = 0 := by
        have h : e.val j = e₁.val j + e₂.val j := congrArg (fun z : PowRing b R => z.val j) hsum
        rw [hall_other j hj] at h
        exact h.symm
      have hoj : e₁.val j * e₂.val j = 0 := congrArg (fun z : PowRing b R => z.val j) ho12
      have h1j : e₁.val j = 0 := by
        have hm : e₁.val j * (e₁.val j + e₂.val j) = e₁.val j * 0 :=
          congrArg (fun x => e₁.val j * x) hsj
        have he1j : e₁.val j * e₁.val j = e₁.val j := PiRing.isIdem_val he₁ j
        rw [AssocRing.left_distrib, he1j, hoj, AssocRing.add_zero', AssocRing.mul_zero] at hm
        exact hm
      have h2j : e₂.val j = 0 := by
        rw [h1j, AssocRing.zero_add'] at hsj
        exact hsj
      exact ⟨h1j, h2j⟩
    rcases hi₀_prim (e₁.val i₀) (e₂.val i₀)
        (PiRing.isIdem_val he₁ i₀) (PiRing.isIdem_val he₂ i₀)
        (congrArg (fun z : PowRing b R => z.val i₀) ho12)
        (congrArg (fun z : PowRing b R => z.val i₀) ho21)
        (congrArg (fun z : PowRing b R => z.val i₀) hsum) with h10 | h20
    · left
      apply PiRing.ext; intro j
      by_cases hj : j = i₀
      · subst hj; exact h10
      · exact (hother_zero j hj).1
    · right
      apply PiRing.ext; intro j
      by_cases hj : j = i₀
      · subst hj; exact h20
      · exact (hother_zero j hj).2

def PrimIdemElem (A : Type u) [AssocRing A] : Type u := { e : A // IsPrimitiveIdem e }

def primIdemSetoid (A : Type u) [AssocRing A] : Setoid (PrimIdemElem A) where
  r := fun x y => PolyConn x.1 y.1
  iseqv := ⟨fun x => PolyConn.refl x.2.1, PolyConn.symm, PolyConn.trans⟩

def PrimIdemSpectrum (A : Type u) [AssocRing A] : Type u := Quotient (primIdemSetoid A)

/-- Primitive Idempotent Salvage on `(M₂(K))^b`:
    While `|π₀(E((M₂(K))^b))| = 3^b ≫ b`, restricting to PRIMITIVE idempotents yields
    EXACTLY `b` connected families (`PrimIdemSpectrum (PowRing b (Mat2 K)) ≃ Fin b`)! -/
noncomputable def mat2PowPrimSpectrumEquiv {K : Type u} [Field K] (b : Nat) :
    EquivBij (PrimIdemSpectrum (PowRing b (Mat2 K))) (Fin b) where
  toFun := Quotient.lift
    (fun e => Classical.choose ((powRing_isPrimitiveIdem_iff e.1).mp e.2))
    (fun e₀ e₁ hc => by
      let i₀ := Classical.choose ((powRing_isPrimitiveIdem_iff e₀.1).mp e₀.2)
      let i₁ := Classical.choose ((powRing_isPrimitiveIdem_iff e₁.1).mp e₁.2)
      have hi₀ := Classical.choose_spec ((powRing_isPrimitiveIdem_iff e₀.1).mp e₀.2)
      have hi₁ := Classical.choose_spec ((powRing_isPrimitiveIdem_iff e₁.1).mp e₁.2)
      change i₀ = i₁
      by_cases heq : i₀ = i₁
      · exact heq
      · exfalso
        have hconn_i0 : PolyConn (e₀.1.val i₀) (e₁.1.val i₀) := PiRing.polyConn_coord hc i₀
        have hcl := Mat2.polyConn_mat2Class_eq hconn_i0
        have hz1 : e₁.1.val i₀ = 0 := hi₁.2 i₀ heq
        rw [hz1, Mat2.mat2Class_zero] at hcl
        rcases (Mat2.mat2_isPrimitiveIdem_iff (e₀.1.val i₀)).mp hi₀.1 with ⟨_, hdet0, htr0⟩
        have hn0 : e₀.1.val i₀ ≠ 0 := hi₀.1.2.1
        have hn1 : e₀.1.val i₀ ≠ 1 := by
          intro h1; rw [h1] at hdet0
          change (1 : K) * 1 - 0 * 0 = 0 at hdet0
          rw [AssocRing.one_mul', AssocRing.zero_mul, AssocRing.sub_zero] at hdet0
          exact IntegralDomain.one_ne_zero hdet0
        rw [Mat2.mat2Class_proper hn0 hn1] at hcl
        cases hcl)
  invFun := fun i =>
    have hE11_prim : IsPrimitiveIdem (Mat2.E11 : Mat2 K) := by
      rw [Mat2.mat2_isPrimitiveIdem_iff]
      refine ⟨Mat2.isIdem_E11, ?_, ?_⟩
      · change (1 : K) * 0 - 0 * 0 = 0
        rw [AssocRing.mul_zero, AssocRing.zero_mul, AssocRing.sub_self]
      · change (1 : K) + 0 = 1
        exact AssocRing.add_zero' 1
    Quotient.mk (primIdemSetoid (PowRing b (Mat2 K)))
      ⟨⟨fun j => if j = i then Mat2.E11 else 0⟩,
       (powRing_isPrimitiveIdem_iff _).mpr ⟨i, by dsimp only; rw [if_pos rfl]; exact hE11_prim,
         fun j hj => by dsimp only; rw [if_neg hj]⟩⟩
  left_inv := fun s => by
    refine Quotient.inductionOn s (fun e => ?_)
    apply Quotient.sound
    let i₀ := Classical.choose ((powRing_isPrimitiveIdem_iff e.1).mp e.2)
    have hi₀ := Classical.choose_spec ((powRing_isPrimitiveIdem_iff e.1).mp e.2)
    change PolyConn ⟨fun j => if j = i₀ then (Mat2.E11 : Mat2 K) else 0⟩ e.1
    have h1_idem : IsIdem (⟨fun j => if j = i₀ then (Mat2.E11 : Mat2 K) else 0⟩ : PowRing b (Mat2 K)) :=
      PiRing.ext (fun j => by
        rw [PiRing.mul_val]
        dsimp only
        by_cases hj : j = i₀
        · rw [if_pos hj]; exact Mat2.isIdem_E11
        · rw [if_neg hj]; exact isIdem_zero)
    rw [PowRing.polyConn_iff_forall h1_idem e.2.1]
    intro j
    dsimp only
    by_cases hj : j = i₀
    · rw [if_pos hj, hj]
      rcases (Mat2.mat2_isPrimitiveIdem_iff (e.1.val i₀)).mp hi₀.1 with ⟨hEj, hdet, htr⟩
      exact PolyConn.symm (Mat2.polyConn_rank1_to_E11 hEj hdet htr)
    · rw [if_neg hj, hi₀.2 j hj]
      exact PolyConn.refl isIdem_zero
  right_inv := fun i => by
    let e_i : PowRing b (Mat2 K) := ⟨fun j => if j = i then Mat2.E11 else 0⟩
    have hE11_ne : (Mat2.E11 : Mat2 K) ≠ 0 := fun h => IntegralDomain.one_ne_zero (congrArg Mat2.a h)
    have hE11_prim : IsPrimitiveIdem (Mat2.E11 : Mat2 K) := by
      rw [Mat2.mat2_isPrimitiveIdem_iff]
      exact ⟨Mat2.isIdem_E11, by change (1 : K) * 0 - 0 * 0 = 0; rw [AssocRing.mul_zero, AssocRing.zero_mul, AssocRing.sub_self],
             AssocRing.add_zero' 1⟩
    have hp : IsPrimitiveIdem e_i :=
      (powRing_isPrimitiveIdem_iff e_i).mpr ⟨i, by dsimp only [e_i]; rw [if_pos rfl]; exact hE11_prim,
        fun j hj => by dsimp only [e_i]; rw [if_neg hj]⟩
    have hspec := Classical.choose_spec ((powRing_isPrimitiveIdem_iff e_i).mp hp)
    let c := Classical.choose ((powRing_isPrimitiveIdem_iff e_i).mp hp)
    change c = i
    by_cases hci : c = i
    · exact hci
    · exfalso
      have hzero : e_i.val i = 0 := hspec.2 i (fun h => hci h.symm)
      dsimp only [e_i] at hzero
      rw [if_pos rfl] at hzero
      exact hE11_ne hzero

end PrimitiveSalvage

/-! ### Exact Multi-Rank Arithmetic & Complete Sporadic Profile Classification -/

def blockProd : List Nat → Nat
  | [] => 1
  | n :: ns => (n + 1) * blockProd ns

theorem two_pow_gt_self (b : Nat) : b < 2 ^ b := by
  induction b with
  | zero => decide
  | succ k ih =>
    have hp : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
    omega

theorem blockProd_ge_two_pow {dims : List Nat} (hpos : ∀ n, n ∈ dims → 1 ≤ n) :
    2 ^ dims.length ≤ blockProd dims := by
  induction dims with
  | nil => decide
  | cons n ns ih =>
    have hn : 1 ≤ n := hpos n (List.Mem.head ns)
    have ih' : 2 ^ ns.length ≤ blockProd ns := ih (fun m hm => hpos m (List.Mem.tail n hm))
    change 2 ^ (ns.length + 1) ≤ (n + 1) * blockProd ns
    rw [Nat.pow_succ]
    have hmul : 2 ^ ns.length * 2 ≤ 2 * blockProd ns := by omega
    have hmul2 : 2 * blockProd ns ≤ (n + 1) * blockProd ns := Nat.mul_le_mul_right (blockProd ns) (by omega)
    omega

/-- Universal All-Idempotent Failure (`∏(n_i + 1) ≥ 2^b > b`):
    for EVERY nonempty block-size list `dims` with `n_i ≥ 1`, `|π₀(E(A))| > b`! -/
theorem all_idempotents_exceed_block_count {dims : List Nat}
    (hpos : ∀ n, n ∈ dims → 1 ≤ n) :
    dims.length < blockProd dims := by
  have h1 := two_pow_gt_self dims.length
  have h2 := blockProd_ge_two_pow hpos
  omega

theorem two_pow_sub_two_gt_of_ge_three {b : Nat} (hb : 3 ≤ b) : b < 2 ^ b - 2 := by
  induction b with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 2
    · subst hk; decide
    · have hk3 : 3 ≤ k := by omega
      have ih' := ih hk3
      have hp : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
      omega

/-- Complete Sporadic Profile Classification Theorem:
    For ANY nonempty positive block-size profile `dims` (`∀ n ∈ dims, 1 ≤ n`),
    the proper-idempotent bound `∏(n_i + 1) - 2 ≤ b` holds IF AND ONLY IF
    `dims = [1]`, `dims = [2]`, or `dims = [1, 1]`! -/
theorem proper_bound_iff_sporadic {dims : List Nat}
    (hne : dims ≠ []) (hpos : ∀ n, n ∈ dims → 1 ≤ n) :
    blockProd dims - 2 ≤ dims.length ↔
    (∃ n, dims = [n] ∧ 1 ≤ n ∧ n ≤ 2) ∨ dims = [1, 1] := by
  cases dims with
  | nil => exact False.elim (hne rfl)
  | cons n₁ rest =>
    have hn1 : 1 ≤ n₁ := hpos n₁ (List.Mem.head rest)
    cases rest with
    | nil =>
      change (n₁ + 1) * 1 - 2 ≤ 1 ↔ (∃ n, [n₁] = [n] ∧ 1 ≤ n ∧ n ≤ 2) ∨ [n₁] = [1, 1]
      constructor
      · intro hle
        left
        exact ⟨n₁, rfl, hn1, by omega⟩
      · rintro (⟨n, heq, _, hnle⟩ | hc)
        · injection heq with hnn; subst hnn; omega
        · cases hc
    | cons n₂ rest2 =>
      have hn2 : 1 ≤ n₂ := hpos n₂ (List.Mem.tail n₁ (List.Mem.head rest2))
      cases rest2 with
      | nil =>
        change (n₁ + 1) * ((n₂ + 1) * 1) - 2 ≤ 2 ↔
               (∃ n, [n₁, n₂] = [n] ∧ 1 ≤ n ∧ n ≤ 2) ∨ [n₁, n₂] = [1, 1]
        constructor
        · intro hle
          right
          by_cases h1 : n₁ = 1
          · by_cases h2 : n₂ = 1
            · subst h1; subst h2; rfl
            · have h2ge : 2 ≤ n₂ := by omega
              have hprod : 6 ≤ (n₁ + 1) * ((n₂ + 1) * 1) := by
                rw [Nat.mul_one]
                exact Nat.mul_le_mul (by omega : 2 ≤ n₁ + 1) (by omega : 3 ≤ n₂ + 1)
              omega
          · have h1ge : 2 ≤ n₁ := by omega
            have hprod : 6 ≤ (n₁ + 1) * ((n₂ + 1) * 1) := by
              rw [Nat.mul_one]
              exact Nat.mul_le_mul (by omega : 3 ≤ n₁ + 1) (by omega : 2 ≤ n₂ + 1)
            omega
        · rintro (⟨_, hc, _⟩ | heq)
          · cases hc
          · injection heq with h1 h2'
            injection h2' with h2 _
            subst h1; subst h2; decide
      | cons n₃ rest3 =>
        -- Length is `rest3.length + 3 ≥ 3`, so `blockProd ≥ 2^b` and `2^b - 2 > b`!
        have hlen : 3 ≤ (n₁ :: n₂ :: n₃ :: rest3).length := by simp
        have hge := blockProd_ge_two_pow hpos
        have hgt := two_pow_sub_two_gt_of_ge_three hlen
        constructor
        · intro hle; omega
        · rintro (⟨_, hc, _⟩ | hc) <;> cases hc

/-! ### Clause III Formalization & Disproof: Algebra-Isomorphism Class Counting -/

structure RingIso (R : Type u) (S : Type v) [AssocRing R] [AssocRing S] where
  toFun : R → S
  invFun : S → R
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  map_add : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_mul : ∀ x y, toFun (x * y) = toFun x * toFun y
  map_one : toFun 1 = 1

def RingIso.refl (R : Type u) [AssocRing R] : RingIso R R where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add := fun _ _ => rfl
  map_mul := fun _ _ => rfl
  map_one := rfl

/-- `B : Fin b → Type u` has at most `k` ring-isomorphism classes of simple matrix blocks. -/
def HasAtMostKAlgIsoClasses {b : Nat} (B : Fin b → Type u) [∀ i, AssocRing (B i)] (k : Nat) : Prop :=
  ∃ reps : Fin k → Fin b, ∀ i : Fin b, ∃ j : Fin k, Nonempty (RingIso (B i) (B (reps j)))

def ExactAlgIsoClassCount {b : Nat} (B : Fin b → Type u) [∀ i, AssocRing (B i)] (k : Nat) : Prop :=
  HasAtMostKAlgIsoClasses B k ∧ ∀ m : Nat, m < k → ¬ HasAtMostKAlgIsoClasses B m

/-- Universal Reverse Inequality (`c_alg ≤ b`):
    Every `b`-block algebra has AT MOST `b` ring-isomorphism classes of blocks! -/
theorem algIsoClasses_le_blockCount {b : Nat} (B : Fin b → Type u) [∀ i, AssocRing (B i)] :
    HasAtMostKAlgIsoClasses B b :=
  ⟨id, fun i => ⟨i, ⟨RingIso.refl (B i)⟩⟩⟩

/-- Refutation of Clause III (`b ≤ c_alg`):
    For ANY ring `R` and ANY `b ≥ 2` (e.g. `Cl_{1,0}(K) ≅ K × K` or `Cl_{2,1}(K) ≅ M₂(K) × M₂(K)`),
    the homogeneous `b`-block algebra `R^b` has `ExactAlgIsoClassCount = 1`, while `b ≥ 2 > 1`! -/
theorem clause3_refuted_homogeneous {R : Type u} [AssocRing R] {b : Nat} (hb : 2 ≤ b) :
    ExactAlgIsoClassCount (fun _ : Fin b => R) 1 ∧ ¬ (b ≤ 1) := by
  refine ⟨⟨?_, ?_⟩, by omega⟩
  · refine ⟨fun _ => ⟨0, by omega⟩, fun _ => ⟨⟨0, by decide⟩, ⟨RingIso.refl R⟩⟩⟩
  · intro m hm hcov
    have hm0 : m = 0 := by omega
    subst hm0
    rcases hcov with ⟨_, hall⟩
    rcases hall ⟨0, by omega⟩ with ⟨j, _⟩
    exact Fin.elim0 j

/-- Simultaneous Double Reverse Inequality Master Theorem (`|π₀| > b > c_alg`):
    1. On `K × K ≅ Cl_{1,0}(K)` (`b = 2`): `|π₀(E)| = 4 > b = 2 > c_alg = 1`.
    2. On `M₂(K) × M₂(K) ≅ Cl_{2,1}(K)` (`b = 2`): `|π₀(E)| = 9` (`|π₀(E°)| = 7 > b = 2 > c_alg = 1`).
    3. On `K³` (`b = 3`, central idempotents): `|π₀(E(Z))| = 8` (`|π₀(E°(Z))| = 6 > b = 3 > c_alg = 1`). -/
theorem double_reverse_inequality_master {K : Type u} [Field K] :
    Nonempty (EquivBij (IdemSpectrum (PowRing 2 K)) (Fin 2 → Bool)) ∧
    ExactAlgIsoClassCount (fun _ : Fin 2 => K) 1 ∧
    Nonempty (EquivBij (IdemSpectrum (PowRing 2 (Mat2 K))) (Fin 2 → Fin 3)) ∧
    ExactAlgIsoClassCount (fun _ : Fin 2 => Mat2 K) 1 ∧
    Nonempty (EquivBij (IdemSpectrum (PowRing 3 K)) (Fin 3 → Bool)) ∧
    ExactAlgIsoClassCount (fun _ : Fin 3 => K) 1 :=
  ⟨⟨commBlockSpectrumEquiv 2⟩,
   (clause3_refuted_homogeneous (R := K) (b := 2) (by decide)).1,
   ⟨mat2PowSpectrumEquiv 2⟩,
   (clause3_refuted_homogeneous (R := Mat2 K) (b := 2) (by decide)).1,
   ⟨commBlockSpectrumEquiv 3⟩,
   (clause3_refuted_homogeneous (R := K) (b := 3) (by decide)).1⟩

/-! ### Unqualified Clause I Counterexample: Infinite-Dimensional Product `ℤ^ℕ` -/

abbrev InfProdInt : Type := PiRing (fun _ : Nat => Int)

theorem infProdInt_polyConn_eq {e₀ e₁ : InfProdInt} (hc : PolyConn e₀ e₁) : e₀ = e₁ := by
  apply PiRing.ext
  intro m
  exact domain_polyConn_eq (PiRing.polyConn_coord hc m)

def deltaIdem (k : Nat) : IdemSpectrum InfProdInt :=
  Quotient.mk (idemSetoid InfProdInt)
    ⟨⟨fun m => if m = k then 1 else 0⟩,
     PiRing.ext (fun m => by
       change (if m = k then (1 : Int) else 0) * (if m = k then 1 else 0) =
              (if m = k then 1 else 0)
       by_cases hm : m = k
       · rw [if_pos hm]; rfl
       · rw [if_neg hm]; rfl)⟩

theorem deltaIdem_injective : Injective deltaIdem := by
  intro k₁ k₂ heq
  have hconn := Quotient.exact heq
  have hval := infProdInt_polyConn_eq hconn
  have hk := congrArg (fun z => z.val k₁) hval
  change (if k₁ = k₁ then (1 : Int) else 0) = (if k₁ = k₂ then 1 else 0) at hk
  rw [if_pos rfl] at hk
  by_cases h12 : k₁ = k₂
  · exact h12
  · rw [if_neg h12] at hk
    cases hk

private theorem no_inj_nat_to_fin : ∀ (N : Nat) (g : Nat → Fin N), ¬ Injective g
  | 0, g, _ => Fin.elim0 (g 0)
  | N + 1, g, hg => by
    -- Build an injective map `g' : Nat → Fin N` on `k ↦ g (k + 1)` by routing `N` to `g 0`!
    let g' : Nat → Fin N := fun k =>
      if hlt : (g (k + 1)).1 < N then ⟨(g (k + 1)).1, hlt⟩
      else
        have hgk_eq : (g (k + 1)).1 = N := by have := (g (k + 1)).2; omega
        have hne0 : g 0 ≠ g (k + 1) := fun hc => by have := hg 0 (k + 1) hc; omega
        have hg0_lt : (g 0).1 < N := by
          have := (g 0).2
          have hv_ne : (g 0).1 ≠ N := fun hv => hne0 (Fin.ext (hv.trans hgk_eq.symm))
          omega
        ⟨(g 0).1, hg0_lt⟩
    have hg' : Injective g' := by
      intro a b hab
      dsimp only [g'] at hab
      by_cases ha : (g (a + 1)).1 < N
      · rw [dif_pos ha] at hab
        by_cases hb : (g (b + 1)).1 < N
        · rw [dif_pos hb] at hab
          have hv : (g (a + 1)).1 = (g (b + 1)).1 := congrArg (fun x : Fin N => x.1) hab
          have h1 := hg (a + 1) (b + 1) (Fin.ext hv)
          omega
        · rw [dif_neg hb] at hab
          exfalso
          have hv : (g (a + 1)).1 = (g 0).1 := congrArg (fun x : Fin N => x.1) hab
          have h1 := hg (a + 1) 0 (Fin.ext hv)
          omega
      · rw [dif_neg ha] at hab
        by_cases hb : (g (b + 1)).1 < N
        · rw [dif_pos hb] at hab
          exfalso
          have hv : (g 0).1 = (g (b + 1)).1 := congrArg (fun x : Fin N => x.1) hab
          have h1 := hg 0 (b + 1) (Fin.ext hv)
          omega
        · have hgaN : (g (a + 1)).1 = N := by have := (g (a + 1)).2; omega
          have hgbN : (g (b + 1)).1 = N := by have := (g (b + 1)).2; omega
          have hgab : g (a + 1) = g (b + 1) := Fin.ext (hgaN.trans hgbN.symm)
          have h1 := hg (a + 1) (b + 1) hgab
          omega
    exact no_inj_nat_to_fin N g' hg'

/-- Unqualified Clause I Disproof: for the infinite-dimensional commutative ring `ℤ^ℕ`,
    `IdemSpectrum InfProdInt` admits NO injective map into `Fin N` for ANY `N : Nat`! -/
theorem clause1_infinite_counterexample :
    Injective deltaIdem ∧ ∀ (N : Nat) (emb : IdemSpectrum InfProdInt → Fin N), ¬ Injective emb := by
  refine ⟨deltaIdem_injective, fun N emb hemb => ?_⟩
  exact no_inj_nat_to_fin N (fun k => emb (deltaIdem k))
    (fun a b hab => deltaIdem_injective a b (hemb _ _ hab))

/-! ## Concrete Instantiation Witnesses & Axiom Verification -/

/-- Concrete witnesses over both `ℚ` (`QField`, char 0) and `𝔽₂` (`F2`, char 2) confirming
    non-vacuity of every typeclass and main theorem. -/
noncomputable def concreteMat2QEquiv : EquivBij (IdemSpectrum (Mat2 QField)) (Fin 3) :=
  Mat2.mat2IdemSpectrumEquivFin3

noncomputable def concreteMat2F2Equiv : EquivBij (IdemSpectrum (Mat2 F2)) (Fin 3) :=
  Mat2.mat2IdemSpectrumEquivFin3

theorem concreteClifford22Q :
    3 > 1 ∧ ∃ f : Fin 3 → ProperIdemSpectrum (Mat 4 QField), Injective f :=
  Mat.clifford22_proper_three_gt_one (K := QField)

#print axioms leftIdealIso_iff_murrayVonNeumann
#print axioms nilpotent_diff_polyStep
#print axioms UpperTri2.upperTri2_spectrum_left_inv
#print axioms UpperTri2.upperTri2_spectrum_right_inv
#print axioms newtonLiftStep_sub_self
#print axioms Mat2.idempotent_trichotomy
#print axioms Mat2.mat2IdemSpectrumEquivFin3
#print axioms Mat2.mat2ProperSpectrumEquivUnit
#print axioms Mat2.mat2_isPrimitiveIdem_iff
#print axioms Mat.deriv_tr_idem_eq_zero
#print axioms Mat.polyConn_tr_eq
#print axioms Mat.singleBlockAllMap_injective
#print axioms Mat.singleBlockProperMap_injective
#print axioms Mat.clifford22_proper_three_gt_one
#print axioms Mat.split_clifford_unbounded_proper_spectrum
#print axioms multiBlockMap_injective
#print axioms commBlockSpectrumEquiv
#print axioms mat2PowSpectrumEquiv
#print axioms mat2PowPrimSpectrumEquiv
#print axioms all_idempotents_exceed_block_count
#print axioms proper_bound_iff_sporadic
#print axioms algIsoClasses_le_blockCount
#print axioms clause3_refuted_homogeneous
#print axioms double_reverse_inequality_master
#print axioms clause1_infinite_counterexample
#print axioms concreteMat2QEquiv
#print axioms concreteMat2F2Equiv
#print axioms concreteClifford22Q

end Conjecture00000007626




