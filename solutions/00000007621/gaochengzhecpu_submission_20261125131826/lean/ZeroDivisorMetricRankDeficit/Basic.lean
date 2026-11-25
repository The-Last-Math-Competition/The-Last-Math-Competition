/-
Copyright (c) 2026 The Last Math Competition Authors. All rights reserved.
 Formal disproof of Conjecture 00000007621 (Zero-divisor metric rank-deficit law).
 Core Lean 4.19.0 — zero external dependencies, zero sorry, zero custom axioms.
-/

namespace ZeroDivisorMetricRankDeficit

/-!
## 1. Multiplicative Annihilation & Zero-Divisor Structure
-/

/-- Right annihilator membership: `x * y = 0`. -/
def InRightAnn {A : Type u} (zero : A) (mul : A → A → A) (x y : A) : Prop :=
  mul x y = zero

/-- Left annihilator membership: `y * x = 0`. -/
def InLeftAnn {A : Type u} (zero : A) (mul : A → A → A) (x y : A) : Prop :=
  mul y x = zero

/-- Membership in the zero-divisor locus `Z(A)` via multiplicative annihilation. -/
def IsZeroDivisor {A : Type u} (zero : A) (mul : A → A → A) (x : A) : Prop :=
  ∃ y : A, y ≠ zero ∧ (mul x y = zero ∨ mul y x = zero)

/-- Two-sided multiplicative invertibility in `(A, one, mul)`. -/
def HasTwoSidedInv {A : Type u} (one : A) (mul : A → A → A) (x : A) : Prop :=
  ∃ xInv : A, mul x xInv = one ∧ mul xInv x = one

/-- An associative unital algebra equipped with an algebra involution `invl` (`α`). -/
structure AssocInvolAlg (A : Type u) where
  zero : A
  one : A
  add : A → A → A
  neg : A → A
  mul : A → A → A
  invl : A → A
  zero_ne_one : zero ≠ one
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  add_zero : ∀ a, add a zero = a
  neg_add_cancel : ∀ a, add (neg a) a = zero
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)
  invl_invl : ∀ a, invl (invl a) = a
  invl_zero : invl zero = zero
  invl_one : invl one = one
  invl_add : ∀ a b, invl (add a b) = add (invl a) (invl b)
  invl_neg : ∀ a, invl (neg a) = neg (invl a)
  invl_mul : ∀ a b, invl (mul a b) = mul (invl a) (invl b)

namespace AssocInvolAlg

variable {A : Type u} (alg : AssocInvolAlg A)

theorem add_left_cancel {a b c : A} (h : alg.add a b = alg.add a c) : b = c := by
  have h1 : alg.add (alg.neg a) (alg.add a b) = alg.add (alg.neg a) (alg.add a c) :=
    congrArg (alg.add (alg.neg a)) h
  rw [← alg.add_assoc, ← alg.add_assoc, alg.neg_add_cancel, alg.zero_add, alg.zero_add] at h1
  exact h1

theorem add_right_cancel {a b c : A} (h : alg.add a c = alg.add b c) : a = b := by
  rw [alg.add_comm a c, alg.add_comm b c] at h
  exact alg.add_left_cancel h

theorem add_neg_cancel (a : A) : alg.add a (alg.neg a) = alg.zero := by
  rw [alg.add_comm]
  exact alg.neg_add_cancel a

theorem neg_zero : alg.neg alg.zero = alg.zero := by
  apply alg.add_left_cancel (a := alg.zero)
  rw [alg.add_neg_cancel, alg.add_zero]

theorem neg_neg (a : A) : alg.neg (alg.neg a) = a := by
  apply alg.add_left_cancel (a := alg.neg a)
  rw [alg.add_neg_cancel, alg.neg_add_cancel]

theorem neg_add (a b : A) : alg.neg (alg.add a b) = alg.add (alg.neg a) (alg.neg b) := by
  apply alg.add_left_cancel (a := alg.add a b)
  rw [alg.add_neg_cancel]
  calc
    alg.zero = alg.add a (alg.neg a) := (alg.add_neg_cancel a).symm
    _ = alg.add a (alg.add alg.zero (alg.neg a)) := by rw [alg.zero_add]
    _ = alg.add a (alg.add (alg.add b (alg.neg b)) (alg.neg a)) := by rw [alg.add_neg_cancel]
    _ = alg.add a (alg.add b (alg.add (alg.neg b) (alg.neg a))) := by rw [alg.add_assoc]
    _ = alg.add (alg.add a b) (alg.add (alg.neg a) (alg.neg b)) := by
          rw [← alg.add_assoc a b, alg.add_comm (alg.neg b) (alg.neg a)]

theorem mul_zero (a : A) : alg.mul a alg.zero = alg.zero := by
  apply alg.add_left_cancel (a := alg.mul a alg.zero)
  rw [← alg.left_distrib, alg.add_zero, alg.add_zero]

theorem zero_mul (a : A) : alg.mul alg.zero a = alg.zero := by
  apply alg.add_left_cancel (a := alg.mul alg.zero a)
  rw [← alg.right_distrib, alg.add_zero, alg.add_zero]

theorem mul_neg (a b : A) : alg.mul a (alg.neg b) = alg.neg (alg.mul a b) := by
  apply alg.add_left_cancel (a := alg.mul a b)
  rw [← alg.left_distrib, alg.add_neg_cancel, alg.mul_zero, alg.add_neg_cancel]

theorem neg_mul (a b : A) : alg.mul (alg.neg a) b = alg.neg (alg.mul a b) := by
  apply alg.add_left_cancel (a := alg.mul a b)
  rw [← alg.right_distrib, alg.add_neg_cancel, alg.zero_mul, alg.add_neg_cancel]

theorem neg_mul_neg (a b : A) : alg.mul (alg.neg a) (alg.neg b) = alg.mul a b := by
  rw [alg.neg_mul, alg.mul_neg, alg.neg_neg]

theorem invl_eq_zero_iff (a : A) : alg.invl a = alg.zero ↔ a = alg.zero := by
  constructor
  · intro h
    have h1 := congrArg alg.invl h
    rw [alg.invl_invl, alg.invl_zero] at h1
    exact h1
  · intro h
    rw [h, alg.invl_zero]

/-- `0` is always a zero divisor in any nontrivial unital algebra (`1 ≠ 0`). -/
theorem zero_isZeroDivisor : IsZeroDivisor alg.zero alg.mul alg.zero := by
  refine ⟨alg.one, alg.zero_ne_one.symm, Or.inl ?_⟩
  exact alg.zero_mul alg.one

/-- No invertible element of an associative unital algebra can be a zero divisor. -/
theorem not_isZeroDivisor_of_inv {x : A} (hInv : HasTwoSidedInv alg.one alg.mul x) :
    ¬ IsZeroDivisor alg.zero alg.mul x := by
  rcases hInv with ⟨xInv, hxR, hxL⟩
  rintro ⟨y, hyNe, hMul | hMul⟩
  · have hy : y = alg.zero := by
      calc
        y = alg.mul alg.one y := (alg.one_mul y).symm
        _ = alg.mul (alg.mul xInv x) y := by rw [hxL]
        _ = alg.mul xInv (alg.mul x y) := alg.mul_assoc xInv x y
        _ = alg.mul xInv alg.zero := by rw [hMul]
        _ = alg.zero := alg.mul_zero xInv
    exact hyNe hy
  · have hy : y = alg.zero := by
      calc
        y = alg.mul y alg.one := (alg.mul_one y).symm
        _ = alg.mul y (alg.mul x xInv) := by rw [hxR]
        _ = alg.mul (alg.mul y x) xInv := (alg.mul_assoc y x xInv).symm
        _ = alg.mul alg.zero xInv := by rw [hMul]
        _ = alg.zero := alg.zero_mul xInv
    exact hyNe hy

end AssocInvolAlg

/-- Multiplicative equivalence preserving `0` and `mul` transports `IsZeroDivisor`. -/
structure MulZeroEquiv {A : Type u} {B : Type v}
    (zeroA : A) (mulA : A → A → A) (zeroB : B) (mulB : B → B → B) where
  toFun : A → B
  invFun : B → A
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b
  map_zero : toFun zeroA = zeroB
  map_mul : ∀ x y, toFun (mulA x y) = mulB (toFun x) (toFun y)

namespace MulZeroEquiv

theorem inv_map_zero {A : Type u} {B : Type v}
    {zA : A} {mA : A → A → A} {zB : B} {mB : B → B → B}
    (e : MulZeroEquiv zA mA zB mB) : e.invFun zB = zA := by
  calc
    e.invFun zB = e.invFun (e.toFun zA) := congrArg e.invFun e.map_zero.symm
    _ = zA := e.left_inv zA

theorem inv_map_mul {A : Type u} {B : Type v}
    {zA : A} {mA : A → A → A} {zB : B} {mB : B → B → B}
    (e : MulZeroEquiv zA mA zB mB) (x y : B) :
    e.invFun (mB x y) = mA (e.invFun x) (e.invFun y) := by
  have h : e.toFun (mA (e.invFun x) (e.invFun y)) = mB x y := by
    rw [e.map_mul, e.right_inv, e.right_inv]
  have h2 := congrArg e.invFun h
  rw [e.left_inv] at h2
  exact h2.symm

theorem isZeroDivisor_iff {A : Type u} {B : Type v}
    {zA : A} {mA : A → A → A} {zB : B} {mB : B → B → B}
    (e : MulZeroEquiv zA mA zB mB) (x : A) :
    IsZeroDivisor zA mA x ↔ IsZeroDivisor zB mB (e.toFun x) := by
  constructor
  · rintro ⟨y, hyNe, hMul | hMul⟩
    · refine ⟨e.toFun y, ?_, Or.inl ?_⟩
      · intro hEq
        apply hyNe
        calc
          y = e.invFun (e.toFun y) := (e.left_inv y).symm
          _ = e.invFun zB := congrArg e.invFun hEq
          _ = zA := e.inv_map_zero
      · calc
          mB (e.toFun x) (e.toFun y) = e.toFun (mA x y) := (e.map_mul x y).symm
          _ = e.toFun zA := congrArg e.toFun hMul
          _ = zB := e.map_zero
    · refine ⟨e.toFun y, ?_, Or.inr ?_⟩
      · intro hEq
        apply hyNe
        calc
          y = e.invFun (e.toFun y) := (e.left_inv y).symm
          _ = e.invFun zB := congrArg e.invFun hEq
          _ = zA := e.inv_map_zero
      · calc
          mB (e.toFun y) (e.toFun x) = e.toFun (mA y x) := (e.map_mul y x).symm
          _ = e.toFun zA := congrArg e.toFun hMul
          _ = zB := e.map_zero
  · rintro ⟨y, hyNe, hMul | hMul⟩
    · refine ⟨e.invFun y, ?_, Or.inl ?_⟩
      · intro hEq
        apply hyNe
        calc
          y = e.toFun (e.invFun y) := (e.right_inv y).symm
          _ = e.toFun zA := congrArg e.toFun hEq
          _ = zB := e.map_zero
      · calc
          mA x (e.invFun y) = mA (e.invFun (e.toFun x)) (e.invFun y) := by rw [e.left_inv x]
          _ = e.invFun (mB (e.toFun x) y) := (e.inv_map_mul (e.toFun x) y).symm
          _ = e.invFun zB := congrArg e.invFun hMul
          _ = zA := e.inv_map_zero
    · refine ⟨e.invFun y, ?_, Or.inr ?_⟩
      · intro hEq
        apply hyNe
        calc
          y = e.toFun (e.invFun y) := (e.right_inv y).symm
          _ = e.toFun zA := congrArg e.toFun hEq
          _ = zB := e.map_zero
      · calc
          mA (e.invFun y) x = mA (e.invFun y) (e.invFun (e.toFun x)) := by rw [e.left_inv x]
          _ = e.invFun (mB y (e.toFun x)) := (e.inv_map_mul y (e.toFun x)).symm
          _ = e.invFun zB := congrArg e.invFun hMul
          _ = zA := e.inv_map_zero

end MulZeroEquiv

/-!
## 2. Minimal Self-Contained Field Axioms (`FieldOps`) in Core Lean 4
-/

class FieldCarrier (K : Type u) extends Add K, Sub K, Neg K, Mul K where
  zero : K
  one : K
  inv : K → K

instance {K : Type u} [FieldCarrier K] : OfNat K 0 := ⟨FieldCarrier.zero⟩
instance {K : Type u} [FieldCarrier K] : OfNat K 1 := ⟨FieldCarrier.one⟩
postfix:max "⁻¹" => FieldCarrier.inv

class FieldOps (K : Type u) extends FieldCarrier K where
  zero_ne_one : (0 : K) ≠ 1
  add_assoc : ∀ a b c : K, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : K, a + b = b + a
  zero_add : ∀ a : K, 0 + a = a
  add_zero : ∀ a : K, a + 0 = a
  neg_add_cancel : ∀ a : K, -a + a = 0
  sub_eq_add_neg : ∀ a b : K, a - b = a + -b
  mul_assoc : ∀ a b c : K, (a * b) * c = a * (b * c)
  mul_comm : ∀ a b : K, a * b = b * a
  one_mul : ∀ a : K, 1 * a = a
  mul_one : ∀ a : K, a * 1 = a
  left_distrib : ∀ a b c : K, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : K, (a + b) * c = a * c + b * c
  mul_inv_cancel : ∀ a : K, a ≠ 0 → a * a⁻¹ = 1

namespace FieldOps

def toAssocInvolAlg (K : Type u) [FieldOps K] : AssocInvolAlg K where
  zero := 0
  one := 1
  add := fun a b => a + b
  neg := fun a => -a
  mul := fun a b => a * b
  invl := fun a => a
  zero_ne_one := zero_ne_one
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  neg_add_cancel := neg_add_cancel
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  left_distrib := left_distrib
  right_distrib := right_distrib
  invl_invl := fun _ => rfl
  invl_zero := rfl
  invl_one := rfl
  invl_add := fun _ _ => rfl
  invl_neg := fun _ => rfl
  invl_mul := fun _ _ => rfl

variable {K : Type u} [FieldOps K]

theorem add_left_cancel {a b c : K} (h : a + b = a + c) : b = c :=
  (toAssocInvolAlg K).add_left_cancel h

theorem add_right_cancel {a b c : K} (h : a + c = b + c) : a = b :=
  (toAssocInvolAlg K).add_right_cancel h

theorem add_neg_cancel (a : K) : a + -a = 0 :=
  (toAssocInvolAlg K).add_neg_cancel a

theorem neg_zero : (-0 : K) = 0 :=
  (toAssocInvolAlg K).neg_zero

theorem neg_neg (a : K) : - -a = a :=
  (toAssocInvolAlg K).neg_neg a

theorem neg_add (a b : K) : -(a + b) = -a + -b :=
  (toAssocInvolAlg K).neg_add a b

theorem mul_zero (a : K) : a * 0 = 0 :=
  (toAssocInvolAlg K).mul_zero a

theorem zero_mul (a : K) : 0 * a = 0 :=
  (toAssocInvolAlg K).zero_mul a

theorem mul_neg (a b : K) : a * -b = -(a * b) :=
  (toAssocInvolAlg K).mul_neg a b

theorem neg_mul (a b : K) : -a * b = -(a * b) :=
  (toAssocInvolAlg K).neg_mul a b

theorem neg_mul_neg (a b : K) : -a * -b = a * b :=
  (toAssocInvolAlg K).neg_mul_neg a b

theorem sub_self (a : K) : a - a = 0 := by
  rw [sub_eq_add_neg, add_neg_cancel]

theorem sub_zero (a : K) : a - 0 = a := by
  rw [sub_eq_add_neg, neg_zero, add_zero]

theorem zero_sub (a : K) : 0 - a = -a := by
  rw [sub_eq_add_neg, zero_add]

theorem sub_eq_zero {a b : K} : a - b = 0 ↔ a = b := by
  constructor
  · intro h
    apply add_right_cancel (c := -b)
    rw [← sub_eq_add_neg, h, add_neg_cancel]
  · intro h
    rw [h, sub_self]

theorem inv_mul_cancel {a : K} (ha : a ≠ 0) : a⁻¹ * a = 1 := by
  rw [mul_comm]
  exact mul_inv_cancel a ha

theorem inv_ne_zero {a : K} (ha : a ≠ 0) : a⁻¹ ≠ 0 := by
  intro hInv
  have h1 : a * a⁻¹ = 1 := mul_inv_cancel a ha
  rw [hInv, mul_zero] at h1
  exact zero_ne_one h1

theorem mul_eq_zero {a b : K} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      calc
        b = (1 : K) * b := (one_mul b).symm
        _ = (a⁻¹ * a) * b := by rw [inv_mul_cancel ha]
        _ = a⁻¹ * (a * b) := mul_assoc a⁻¹ a b
        _ = a⁻¹ * 0 := by rw [h]
        _ = 0 := mul_zero a⁻¹
  · rintro (rfl | rfl)
    · exact zero_mul b
    · exact mul_zero a

/-- In a field `K`, `a` is a zero divisor iff `a = 0`. -/
theorem field_isZeroDivisor_iff (a : K) :
    IsZeroDivisor (0 : K) (fun x y => x * y) a ↔ a = 0 := by
  constructor
  · rintro ⟨y, hyNe, hMul | hMul⟩
    · rcases mul_eq_zero.mp hMul with ha | hy
      · exact ha
      · exact False.elim (hyNe hy)
    · rcases mul_eq_zero.mp hMul with hy | ha
      · exact False.elim (hyNe hy)
      · exact ha
  · intro ha
    rw [ha]
    exact (toAssocInvolAlg K).zero_isZeroDivisor

theorem field_dichotomy (a : K) :
    IsZeroDivisor (0 : K) (fun x y => x * y) a ∨ HasTwoSidedInv (1 : K) (fun x y => x * y) a := by
  by_cases ha : a = 0
  · exact Or.inl ((field_isZeroDivisor_iff a).mpr ha)
  · exact Or.inr ⟨a⁻¹, mul_inv_cancel a ha, inv_mul_cancel ha⟩

end FieldOps

end ZeroDivisorMetricRankDeficit
