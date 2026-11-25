/-
Copyright (c) 2026. All rights reserved.
Formalization of Conjecture 00000007179 in Core Lean 4.19.0 (zero external dependencies).

Module: Conjecture00000007179.OrderedField
Purpose:
  1. Self-contained axiomatization of a linearly ordered field (`LinearOrderedField F`),
     covering Q, R, and every linearly ordered field, with complete ring, field, order,
     absolute-value, power, finite-sum, vector, and matrix lemmas from first principles.
  2. Explicit constructive instantiation `instance : LinearOrderedField Q` on exact
     rationals `Q` built as a quotient of `Int × {d : Int // 0 < d}`, guaranteeing
     constructive non-vacuity within Core Lean 4.19.0.
-/

namespace Conjecture00000007179

/-- Self-contained `0`, `1`, and `⁻¹` notation classes in Core Lean 4. -/
class HasZero (α : Type u) where
  zero : α

class HasOne (α : Type u) where
  one : α

class HasInv (α : Type u) where
  inv : α → α

instance {α : Type u} [HasZero α] : OfNat α 0 := ⟨HasZero.zero⟩
instance {α : Type u} [HasOne α] : OfNat α 1 := ⟨HasOne.one⟩
postfix:max "⁻¹" => HasInv.inv

/-- Standard linearly ordered field typeclass, self-contained in Core Lean 4. -/
class LinearOrderedField (F : Type u) extends
    HasZero F, HasOne F, Add F, Sub F, Neg F, Mul F, HasInv F, Div F, LE F, LT F where
  add_assoc : ∀ a b c : F, a + b + c = a + (b + c)
  add_comm : ∀ a b : F, a + b = b + a
  zero_add : ∀ a : F, 0 + a = a
  add_zero : ∀ a : F, a + 0 = a
  neg_add_cancel : ∀ a : F, -a + a = 0
  sub_eq_add_neg : ∀ a b : F, a - b = a + -b
  mul_assoc : ∀ a b c : F, a * b * c = a * (b * c)
  mul_comm : ∀ a b : F, a * b = b * a
  one_mul : ∀ a : F, 1 * a = a
  mul_one : ∀ a : F, a * 1 = a
  left_distrib : ∀ a b c : F, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : F, (a + b) * c = a * c + b * c
  zero_ne_one : (0 : F) ≠ 1
  mul_inv_cancel : ∀ a : F, a ≠ 0 → a * a⁻¹ = 1
  inv_zero : (0 : F)⁻¹ = 0
  div_eq_mul_inv : ∀ a b : F, a / b = a * b⁻¹
  le_refl : ∀ a : F, a ≤ a
  le_trans : ∀ {a b c : F}, a ≤ b → b ≤ c → a ≤ c
  le_antisymm : ∀ {a b : F}, a ≤ b → b ≤ a → a = b
  le_total : ∀ a b : F, a ≤ b ∨ b ≤ a
  lt_iff_le_not_le : ∀ a b : F, a < b ↔ a ≤ b ∧ ¬ b ≤ a
  add_le_add_left : ∀ {a b : F}, a ≤ b → ∀ c : F, c + a ≤ c + b
  mul_pos : ∀ {a b : F}, 0 < a → 0 < b → 0 < a * b
  zero_lt_one : (0 : F) < 1

section OrderedFieldLemmas

variable {F : Type u} [LinearOrderedField F]

abbrev lofAddAssoc (a b c : F) := LinearOrderedField.add_assoc a b c
abbrev lofAddComm (a b : F) := LinearOrderedField.add_comm a b
abbrev lofZeroAdd (a : F) : (0 : F) + a = a := LinearOrderedField.zero_add a
abbrev lofAddZero (a : F) : a + 0 = a := LinearOrderedField.add_zero a
abbrev lofNegAddCancel (a : F) : -a + a = 0 := LinearOrderedField.neg_add_cancel a
abbrev lofSubEqAddNeg (a b : F) := LinearOrderedField.sub_eq_add_neg a b
abbrev lofMulAssoc (a b c : F) := LinearOrderedField.mul_assoc a b c
abbrev lofMulComm (a b : F) := LinearOrderedField.mul_comm a b
abbrev lofOneMul (a : F) : (1 : F) * a = a := LinearOrderedField.one_mul a
abbrev lofMulOne (a : F) : a * 1 = a := LinearOrderedField.mul_one a
abbrev lofLeftDistrib (a b c : F) := LinearOrderedField.left_distrib a b c
abbrev lofRightDistrib (a b c : F) := LinearOrderedField.right_distrib a b c
abbrev lofMulInvCancel {a : F} (h : a ≠ 0) : a * a⁻¹ = 1 := LinearOrderedField.mul_inv_cancel a h
abbrev lofDivEqMulInv (a b : F) := LinearOrderedField.div_eq_mul_inv a b

theorem add_neg_cancel (a : F) : a + -a = 0 := by
  rw [lofAddComm, lofNegAddCancel]

theorem add_left_cancel {a b c : F} (h : a + b = a + c) : b = c := by
  have h1 : -a + (a + b) = -a + (a + c) := congrArg (fun x => -a + x) h
  rw [← lofAddAssoc, ← lofAddAssoc, lofNegAddCancel, lofZeroAdd, lofZeroAdd] at h1
  exact h1

theorem add_right_cancel {a b c : F} (h : a + c = b + c) : a = b := by
  apply add_left_cancel (a := c)
  rw [lofAddComm c a, lofAddComm c b]
  exact h

theorem sub_self (a : F) : a - a = 0 := by
  rw [lofSubEqAddNeg, add_neg_cancel]

theorem neg_zero : -(0 : F) = 0 := by
  apply add_left_cancel (a := (0 : F))
  rw [add_neg_cancel, lofAddZero]

theorem sub_zero (a : F) : a - 0 = a := by
  rw [lofSubEqAddNeg, neg_zero, lofAddZero]

theorem zero_sub (a : F) : 0 - a = -a := by
  rw [lofSubEqAddNeg, lofZeroAdd]

theorem neg_neg (a : F) : -(-a) = a := by
  apply add_left_cancel (a := -a)
  rw [add_neg_cancel, lofNegAddCancel]

theorem neg_add_rev (a b : F) : -(a + b) = -a + -b := by
  apply add_left_cancel (a := a + b)
  rw [add_neg_cancel]
  exact (calc
    a + b + (-a + -b) = a + (b + (-b + -a)) := by
      rw [lofAddComm (-a) (-b), lofAddAssoc]
    _ = a + ((b + -b) + -a) := by rw [lofAddAssoc b (-b) (-a)]
    _ = a + (0 + -a) := by rw [add_neg_cancel]
    _ = a + -a := by rw [lofZeroAdd]
    _ = 0 := add_neg_cancel a).symm

theorem neg_sub (a b : F) : -(a - b) = b - a := by
  rw [lofSubEqAddNeg, neg_add_rev, neg_neg, lofAddComm, ← lofSubEqAddNeg]

theorem add_sub_cancel (a b : F) : a + b - b = a := by
  rw [lofSubEqAddNeg, lofAddAssoc, add_neg_cancel, lofAddZero]

theorem sub_add_cancel (a b : F) : a - b + b = a := by
  rw [lofSubEqAddNeg, lofAddAssoc, lofNegAddCancel, lofAddZero]

theorem sub_eq_zero {a b : F} : a - b = 0 ↔ a = b := by
  constructor
  · intro h
    have h1 : a - b + b = 0 + b := congrArg (fun x => x + b) h
    rw [sub_add_cancel, lofZeroAdd] at h1
    exact h1
  · intro h
    rw [h, sub_self]

theorem mul_zero (a : F) : a * 0 = 0 := by
  apply add_left_cancel (a := a * 0)
  rw [← lofLeftDistrib, lofAddZero, lofAddZero]

theorem zero_mul (a : F) : 0 * a = 0 := by
  rw [lofMulComm, mul_zero]

theorem mul_neg (a b : F) : a * -b = -(a * b) := by
  apply add_left_cancel (a := a * b)
  rw [← lofLeftDistrib, add_neg_cancel, mul_zero, add_neg_cancel]

theorem neg_mul (a b : F) : -a * b = -(a * b) := by
  rw [lofMulComm, mul_neg, lofMulComm]

theorem neg_mul_neg (a b : F) : -a * -b = a * b := by
  rw [neg_mul, mul_neg, neg_neg]

theorem neg_one_mul (a : F) : (-1 : F) * a = -a := by
  rw [neg_mul, lofOneMul]

theorem mul_sub (a b c : F) : a * (b - c) = a * b - a * c := by
  rw [lofSubEqAddNeg, lofLeftDistrib, mul_neg, ← lofSubEqAddNeg]

theorem sub_mul (a b c : F) : (a - b) * c = a * c - b * c := by
  rw [lofSubEqAddNeg, lofRightDistrib, neg_mul, ← lofSubEqAddNeg]

theorem inv_mul_cancel {a : F} (ha : a ≠ 0) : a⁻¹ * a = 1 := by
  rw [lofMulComm, lofMulInvCancel ha]

theorem inv_ne_zero {a : F} (ha : a ≠ 0) : a⁻¹ ≠ 0 := by
  intro h
  have h1 : a * a⁻¹ = 1 := lofMulInvCancel ha
  rw [h, mul_zero] at h1
  exact LinearOrderedField.zero_ne_one h1

theorem mul_eq_zero {a b : F} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      calc
        b = 1 * b := (lofOneMul b).symm
        _ = (a⁻¹ * a) * b := by rw [inv_mul_cancel ha]
        _ = a⁻¹ * (a * b) := lofMulAssoc a⁻¹ a b
        _ = a⁻¹ * 0 := by rw [h]
        _ = 0 := mul_zero a⁻¹
  · intro h
    cases h with
    | inl ha => rw [ha, zero_mul]
    | inr hb => rw [hb, mul_zero]

theorem mul_ne_zero {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro h
  rcases mul_eq_zero.mp h with h1 | h2
  · exact ha h1
  · exact hb h2

theorem mul_right_cancel {a b c : F} (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  have h1 : (a * c) * c⁻¹ = (b * c) * c⁻¹ := congrArg (fun x => x * c⁻¹) h
  rw [lofMulAssoc, lofMulAssoc, lofMulInvCancel hc, lofMulOne, lofMulOne] at h1
  exact h1

theorem mul_left_cancel {a b c : F} (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  apply mul_right_cancel ha
  rw [lofMulComm b a, lofMulComm c a]
  exact h

theorem inv_one : (1 : F)⁻¹ = 1 := by
  apply mul_left_cancel (Ne.symm LinearOrderedField.zero_ne_one)
  rw [lofMulInvCancel (Ne.symm LinearOrderedField.zero_ne_one), lofMulOne]

theorem inv_neg (a : F) : (-a)⁻¹ = -(a⁻¹) := by
  by_cases ha : a = 0
  · rw [ha, neg_zero, LinearOrderedField.inv_zero, neg_zero]
  · have hna : -a ≠ 0 := by
      intro h
      have h2 := congrArg Neg.neg h
      rw [neg_neg, neg_zero] at h2
      exact ha h2
    apply mul_left_cancel hna
    rw [lofMulInvCancel hna, neg_mul_neg, lofMulInvCancel ha]

theorem inv_mul_distrib {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  apply mul_left_cancel (mul_ne_zero ha hb)
  rw [lofMulInvCancel (mul_ne_zero ha hb)]
  exact (calc
    (a * b) * (a⁻¹ * b⁻¹) = a * (b * (b⁻¹ * a⁻¹)) := by
      rw [lofMulComm a⁻¹ b⁻¹, lofMulAssoc]
    _ = a * ((b * b⁻¹) * a⁻¹) := by rw [lofMulAssoc b b⁻¹ a⁻¹]
    _ = a * (1 * a⁻¹) := by rw [lofMulInvCancel hb]
    _ = a * a⁻¹ := by rw [lofOneMul]
    _ = 1 := lofMulInvCancel ha).symm

theorem inv_inv (a : F) : (a⁻¹)⁻¹ = a := by
  by_cases ha : a = 0
  · rw [ha, LinearOrderedField.inv_zero, LinearOrderedField.inv_zero]
  · apply mul_left_cancel (inv_ne_zero ha)
    rw [lofMulInvCancel (inv_ne_zero ha), inv_mul_cancel ha]

theorem div_self {a : F} (ha : a ≠ 0) : a / a = 1 := by
  rw [lofDivEqMulInv, lofMulInvCancel ha]

theorem div_one (a : F) : a / 1 = a := by
  rw [lofDivEqMulInv, inv_one, lofMulOne]

theorem zero_div (a : F) : 0 / a = 0 := by
  rw [lofDivEqMulInv, zero_mul]

theorem neg_div (a b : F) : (-a) / b = -(a / b) := by
  rw [lofDivEqMulInv, lofDivEqMulInv, neg_mul]

theorem add_div (a b c : F) : (a + b) / c = a / c + b / c := by
  rw [lofDivEqMulInv, lofDivEqMulInv, lofDivEqMulInv, lofRightDistrib]

theorem sub_div (a b c : F) : (a - b) / c = a / c - b / c := by
  rw [lofDivEqMulInv, lofDivEqMulInv, lofDivEqMulInv, sub_mul]

theorem mul_div_assoc (a b c : F) : a * (b / c) = (a * b) / c := by
  rw [lofDivEqMulInv, lofDivEqMulInv, lofMulAssoc]

theorem div_mul_eq_mul_div (a b c : F) : (a / b) * c = (a * c) / b := by
  rw [lofDivEqMulInv, lofDivEqMulInv, lofMulAssoc, lofMulComm b⁻¹ c, ← lofMulAssoc]

theorem div_mul_cancel (a : F) {b : F} (hb : b ≠ 0) : (a / b) * b = a := by
  rw [lofDivEqMulInv, lofMulAssoc, inv_mul_cancel hb, lofMulOne]

theorem mul_div_cancel_right (a : F) {b : F} (hb : b ≠ 0) : (a * b) / b = a := by
  rw [lofDivEqMulInv, lofMulAssoc, lofMulInvCancel hb, lofMulOne]

theorem mul_div_cancel_left {a : F} (b : F) (ha : a ≠ 0) : (a * b) / a = b := by
  rw [lofMulComm a b, mul_div_cancel_right b ha]

theorem div_mul_div (a b c d : F) (hb : b ≠ 0) (hd : d ≠ 0) :
    (a / b) * (c / d) = (a * c) / (b * d) := by
  rw [lofDivEqMulInv, lofDivEqMulInv, lofDivEqMulInv, inv_mul_distrib hb hd]
  calc
    (a * b⁻¹) * (c * d⁻¹) = a * (b⁻¹ * (c * d⁻¹)) := lofMulAssoc a b⁻¹ (c * d⁻¹)
    _ = a * ((b⁻¹ * c) * d⁻¹) := by rw [lofMulAssoc b⁻¹ c d⁻¹]
    _ = a * ((c * b⁻¹) * d⁻¹) := by rw [lofMulComm b⁻¹ c]
    _ = (a * c) * (b⁻¹ * d⁻¹) := by
      rw [lofMulAssoc c b⁻¹ d⁻¹, ← lofMulAssoc a c (b⁻¹ * d⁻¹)]

theorem div_eq_iff {a b c : F} (hb : b ≠ 0) : a / b = c ↔ a = c * b := by
  constructor
  · intro h
    rw [← h, div_mul_cancel a hb]
  · intro h
    rw [h, mul_div_cancel_right c hb]

/-! ### Order, Absolute Value, Powers, and Numerals -/

theorem lt_irrefl (a : F) : ¬ (a < a) := by
  intro h
  have h1 := (LinearOrderedField.lt_iff_le_not_le a a).mp h
  exact h1.2 h1.1

theorem le_of_lt {a b : F} (h : a < b) : a ≤ b :=
  ((LinearOrderedField.lt_iff_le_not_le a b).mp h).1

theorem ne_of_lt {a b : F} (h : a < b) : a ≠ b := by
  intro heq
  rw [heq] at h
  exact lt_irrefl b h

theorem ne_of_gt {a b : F} (h : b < a) : a ≠ b :=
  Ne.symm (ne_of_lt h)

theorem not_le_of_lt {a b : F} (h : a < b) : ¬ (b ≤ a) :=
  ((LinearOrderedField.lt_iff_le_not_le a b).mp h).2

theorem lt_of_le_of_ne {a b : F} (hle : a ≤ b) (hne : a ≠ b) : a < b := by
  rw [LinearOrderedField.lt_iff_le_not_le]
  refine ⟨hle, ?_⟩
  intro hba
  exact hne (LinearOrderedField.le_antisymm hle hba)

theorem lt_trichotomy (a b : F) : a < b ∨ a = b ∨ b < a := by
  rcases LinearOrderedField.le_total a b with hab | hba
  · by_cases heq : a = b
    · exact Or.inr (Or.inl heq)
    · exact Or.inl (lt_of_le_of_ne hab heq)
  · by_cases heq : a = b
    · exact Or.inr (Or.inl heq)
    · exact Or.inr (Or.inr (lt_of_le_of_ne hba (Ne.symm heq)))

theorem lt_of_lt_of_le {a b c : F} (hab : a < b) (hbc : b ≤ c) : a < c := by
  rw [LinearOrderedField.lt_iff_le_not_le]
  refine ⟨LinearOrderedField.le_trans (le_of_lt hab) hbc, ?_⟩
  intro hca
  exact not_le_of_lt hab (LinearOrderedField.le_trans hbc hca)

theorem lt_of_le_of_lt {a b c : F} (hab : a ≤ b) (hbc : b < c) : a < c := by
  rw [LinearOrderedField.lt_iff_le_not_le]
  refine ⟨LinearOrderedField.le_trans hab (le_of_lt hbc), ?_⟩
  intro hca
  exact not_le_of_lt hbc (LinearOrderedField.le_trans hca hab)

theorem lt_trans {a b c : F} (hab : a < b) (hbc : b < c) : a < c :=
  lt_of_lt_of_le hab (le_of_lt hbc)

theorem add_le_add_right {a b : F} (h : a ≤ b) (c : F) : a + c ≤ b + c := by
  rw [lofAddComm a c, lofAddComm b c]
  exact LinearOrderedField.add_le_add_left h c

theorem add_le_add {a b c d : F} (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d :=
  LinearOrderedField.le_trans (add_le_add_right hab c) (LinearOrderedField.add_le_add_left hcd b)

theorem add_lt_add_left {a b : F} (h : a < b) (c : F) : c + a < c + b := by
  rw [LinearOrderedField.lt_iff_le_not_le]
  refine ⟨LinearOrderedField.add_le_add_left (le_of_lt h) c, ?_⟩
  intro hcb
  have hba : b ≤ a := by
    have h1 := LinearOrderedField.add_le_add_left hcb (-c)
    rw [← lofAddAssoc, ← lofAddAssoc, lofNegAddCancel, lofZeroAdd, lofZeroAdd] at h1
    exact h1
  exact not_le_of_lt h hba

theorem add_lt_add_right {a b : F} (h : a < b) (c : F) : a + c < b + c := by
  rw [lofAddComm a c, lofAddComm b c]
  exact add_lt_add_left h c

theorem add_lt_add_of_lt_of_le {a b c d : F} (hab : a < b) (hcd : c ≤ d) : a + c < b + d :=
  lt_of_lt_of_le (add_lt_add_right hab c) (LinearOrderedField.add_le_add_left hcd b)

theorem add_lt_add {a b c d : F} (hab : a < b) (hcd : c < d) : a + c < b + d :=
  add_lt_add_of_lt_of_le hab (le_of_lt hcd)

theorem sub_nonneg {a b : F} : 0 ≤ a - b ↔ b ≤ a := by
  constructor
  · intro h
    have h1 := add_le_add_right h b
    rw [lofZeroAdd, sub_add_cancel] at h1
    exact h1
  · intro h
    have h1 := add_le_add_right h (-b)
    rw [add_neg_cancel, ← lofSubEqAddNeg] at h1
    exact h1

theorem sub_pos {a b : F} : 0 < a - b ↔ b < a := by
  constructor
  · intro h
    have h1 := add_lt_add_right h b
    rw [lofZeroAdd, sub_add_cancel] at h1
    exact h1
  · intro h
    have h1 := add_lt_add_right h (-b)
    rw [add_neg_cancel, ← lofSubEqAddNeg] at h1
    exact h1

theorem neg_pos {a : F} : 0 < -a ↔ a < 0 := by
  have h := @sub_pos F _ 0 a
  rw [lofSubEqAddNeg, lofZeroAdd] at h
  exact h

theorem neg_nonneg {a : F} : 0 ≤ -a ↔ a ≤ 0 := by
  have h := @sub_nonneg F _ 0 a
  rw [lofSubEqAddNeg, lofZeroAdd] at h
  exact h

theorem neg_le_neg {a b : F} (h : a ≤ b) : -b ≤ -a := by
  have h2 := LinearOrderedField.add_le_add_left h (-a + -b)
  have h3 : (-a + -b) + a = -b := by
    rw [lofAddComm (-a) (-b), lofAddAssoc, lofNegAddCancel, lofAddZero]
  have h4 : (-a + -b) + b = -a := by
    rw [lofAddAssoc, lofNegAddCancel, lofAddZero]
  rw [h3, h4] at h2
  exact h2

theorem mul_nonneg {a b : F} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  by_cases ha0 : a = 0
  · rw [ha0, zero_mul]
    exact LinearOrderedField.le_refl 0
  · by_cases hb0 : b = 0
    · rw [hb0, mul_zero]
      exact LinearOrderedField.le_refl 0
    · exact le_of_lt (LinearOrderedField.mul_pos
        (lt_of_le_of_ne ha (Ne.symm ha0)) (lt_of_le_of_ne hb (Ne.symm hb0)))

theorem mul_le_mul_of_nonneg_left {a b c : F} (hab : a ≤ b) (hc : 0 ≤ c) :
    c * a ≤ c * b := by
  rw [← sub_nonneg, ← mul_sub]
  exact mul_nonneg hc (sub_nonneg.mpr hab)

theorem mul_le_mul_of_nonneg_right {a b c : F} (hab : a ≤ b) (hc : 0 ≤ c) :
    a * c ≤ b * c := by
  rw [lofMulComm a c, lofMulComm b c]
  exact mul_le_mul_of_nonneg_left hab hc

theorem mul_le_mul {a b c d : F} (hab : a ≤ b) (hcd : c ≤ d) (hc : 0 ≤ c) (hb : 0 ≤ b) :
    a * c ≤ b * d :=
  LinearOrderedField.le_trans (mul_le_mul_of_nonneg_right hab hc)
    (mul_le_mul_of_nonneg_left hcd hb)

theorem mul_lt_mul_of_pos_left {a b c : F} (hab : a < b) (hc : 0 < c) :
    c * a < c * b := by
  rw [← sub_pos, ← mul_sub]
  exact LinearOrderedField.mul_pos hc (sub_pos.mpr hab)

theorem mul_lt_mul_of_pos_right {a b c : F} (hab : a < b) (hc : 0 < c) :
    a * c < b * c := by
  rw [lofMulComm a c, lofMulComm b c]
  exact mul_lt_mul_of_pos_left hab hc

theorem sq_nonneg (a : F) : 0 ≤ a * a := by
  rcases LinearOrderedField.le_total 0 a with ha | ha
  · exact mul_nonneg ha ha
  · rw [← neg_mul_neg]
    exact mul_nonneg (neg_nonneg.mpr ha) (neg_nonneg.mpr ha)

theorem inv_pos_of_pos {a : F} (ha : 0 < a) : 0 < a⁻¹ := by
  rcases lt_trichotomy 0 a⁻¹ with hpos | heq | hneg
  · exact hpos
  · exact False.elim (inv_ne_zero (ne_of_gt ha) heq.symm)
  · have h1 : 0 < -(a⁻¹) := neg_pos.mpr hneg
    have h2 : 0 < a * -(a⁻¹) := LinearOrderedField.mul_pos ha h1
    rw [mul_neg, lofMulInvCancel (ne_of_gt ha)] at h2
    have h3 : (1 : F) < 0 := neg_pos.mp h2
    exact False.elim (lt_irrefl 0 (lt_trans LinearOrderedField.zero_lt_one h3))

theorem inv_nonneg_of_nonneg {a : F} (ha : 0 ≤ a) : 0 ≤ a⁻¹ := by
  by_cases ha0 : a = 0
  · rw [ha0, LinearOrderedField.inv_zero]
    exact LinearOrderedField.le_refl 0
  · exact le_of_lt (inv_pos_of_pos (lt_of_le_of_ne ha (Ne.symm ha0)))

theorem inv_le_inv_of_pos {a b : F} (ha : 0 < a) (hab : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 : b⁻¹ * a ≤ b⁻¹ * b := mul_le_mul_of_nonneg_left hab (le_of_lt (inv_pos_of_pos hb))
  rw [inv_mul_cancel (ne_of_gt hb)] at h1
  have h2 : (b⁻¹ * a) * a⁻¹ ≤ 1 * a⁻¹ :=
    mul_le_mul_of_nonneg_right h1 (le_of_lt (inv_pos_of_pos ha))
  rw [lofMulAssoc, lofMulInvCancel (ne_of_gt ha), lofMulOne, lofOneMul] at h2
  exact h2

theorem div_pos {a b : F} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [lofDivEqMulInv]
  exact LinearOrderedField.mul_pos ha (inv_pos_of_pos hb)

theorem div_nonneg {a b : F} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by
  rw [lofDivEqMulInv]
  exact mul_nonneg ha (inv_nonneg_of_nonneg hb)

theorem div_le_div_of_nonneg_right {a b c : F} (hab : a ≤ b) (hc : 0 ≤ c) :
    a / c ≤ b / c := by
  rw [lofDivEqMulInv, lofDivEqMulInv]
  exact mul_le_mul_of_nonneg_right hab (inv_nonneg_of_nonneg hc)

/-- Small canonical positive numerals in any `LinearOrderedField F`. -/
def twoF : F := (1 : F) + 1
def threeF : F := twoF + 1
def fourF : F := twoF + twoF
def fiveF : F := fourF + 1
def eightF : F := fourF + fourF

theorem one_nonneg : (0 : F) ≤ 1 := le_of_lt LinearOrderedField.zero_lt_one
theorem one_ne_zero : (1 : F) ≠ 0 := Ne.symm LinearOrderedField.zero_ne_one

theorem twoF_pos : (0 : F) < twoF := by
  unfold twoF
  have h := add_lt_add (LinearOrderedField.zero_lt_one (F := F))
    (LinearOrderedField.zero_lt_one (F := F))
  rw [lofAddZero] at h
  exact h

theorem threeF_pos : (0 : F) < threeF := by
  unfold threeF
  have h := add_lt_add (twoF_pos (F := F)) (LinearOrderedField.zero_lt_one (F := F))
  rw [lofAddZero] at h
  exact h

theorem fourF_pos : (0 : F) < fourF := by
  unfold fourF
  have h := add_lt_add (twoF_pos (F := F)) (twoF_pos (F := F))
  rw [lofAddZero] at h
  exact h

theorem fiveF_pos : (0 : F) < fiveF := by
  unfold fiveF
  have h := add_lt_add (fourF_pos (F := F)) (LinearOrderedField.zero_lt_one (F := F))
  rw [lofAddZero] at h
  exact h

theorem eightF_pos : (0 : F) < eightF := by
  unfold eightF
  have h := add_lt_add (fourF_pos (F := F)) (fourF_pos (F := F))
  rw [lofAddZero] at h
  exact h

theorem twoF_ne_zero : (twoF : F) ≠ 0 := ne_of_gt twoF_pos
theorem fourF_ne_zero : (fourF : F) ≠ 0 := ne_of_gt fourF_pos
theorem fiveF_ne_zero : (fiveF : F) ≠ 0 := ne_of_gt fiveF_pos
theorem eightF_ne_zero : (eightF : F) ≠ 0 := ne_of_gt eightF_pos

theorem twoF_mul (a : F) : (twoF : F) * a = a + a := by
  unfold twoF
  rw [lofRightDistrib, lofOneMul]

theorem fourF_eq_two_mul_two : (fourF : F) = twoF * twoF := by
  unfold fourF
  rw [twoF_mul]

theorem eightF_eq_two_mul_four : (eightF : F) = twoF * fourF := by
  unfold eightF
  rw [twoF_mul]

theorem two_mul_le_sq_add_sq (a b : F) : (twoF : F) * (a * b) ≤ a * a + b * b := by
  have h0 : 0 ≤ (a - b) * (a - b) := sq_nonneg (a - b)
  have hexp : (a - b) * (a - b) = (a * a + b * b) - (twoF : F) * (a * b) := by
    rw [sub_mul, mul_sub, mul_sub, lofMulComm b a, twoF_mul]
    rw [lofSubEqAddNeg, lofSubEqAddNeg, lofSubEqAddNeg, neg_add_rev, neg_neg]
    rw [lofAddAssoc (a * a) (-(a * b)) (-(a * b) + b * b)]
    rw [← lofAddAssoc (-(a * b)) (-(a * b)) (b * b)]
    rw [lofAddComm (-(a * b) + -(a * b)) (b * b)]
    rw [← lofAddAssoc (a * a) (b * b) (-(a * b) + -(a * b))]
    rw [← neg_add_rev (a * b) (a * b), ← lofSubEqAddNeg]
  rw [hexp] at h0
  exact sub_nonneg.mp h0

/-- Canonical natural-number embedding `Nat → F`. -/
def natCastF : Nat → F
  | 0 => 0
  | n + 1 => natCastF n + 1

theorem natCastF_zero : (natCastF 0 : F) = 0 := rfl
theorem natCastF_succ (n : Nat) : (natCastF (n + 1) : F) = natCastF n + 1 := rfl

theorem natCastF_one : (natCastF 1 : F) = 1 := by
  unfold natCastF
  exact lofZeroAdd 1

theorem natCastF_two : (natCastF 2 : F) = twoF := by
  change natCastF 1 + 1 = twoF
  rw [natCastF_one]
  rfl

theorem natCastF_add (m n : Nat) : (natCastF (m + n) : F) = natCastF m + natCastF n := by
  induction n with
  | zero =>
    change natCastF m = natCastF m + 0
    exact (lofAddZero _).symm
  | succ k ih =>
    rw [Nat.add_succ, natCastF_succ, natCastF_succ, ih, lofAddAssoc]

theorem natCastF_nonneg (n : Nat) : (0 : F) ≤ natCastF n := by
  induction n with
  | zero => exact LinearOrderedField.le_refl 0
  | succ k ih =>
    rw [natCastF_succ]
    have h := add_le_add ih (one_nonneg (F := F))
    rw [lofAddZero] at h
    exact h

theorem natCastF_pos_of_pos {n : Nat} (hn : 0 < n) : (0 : F) < natCastF n := by
  cases n with
  | zero => omega
  | succ k =>
    rw [natCastF_succ]
    have h := add_lt_add_of_lt_of_le (LinearOrderedField.zero_lt_one (F := F))
      (natCastF_nonneg (F := F) k)
    rw [lofAddZero, lofAddComm] at h
    exact h

theorem natCastF_le_of_le {m n : Nat} (h : m ≤ n) : (natCastF m : F) ≤ natCastF n := by
  have hd : n = m + (n - m) := by omega
  rw [hd, natCastF_add]
  have h1 := LinearOrderedField.add_le_add_left (natCastF_nonneg (F := F) (n - m)) (natCastF m)
  rw [lofAddZero] at h1
  exact h1

/-- Natural-number power `powF a k = a^k`. -/
def powF (a : F) : Nat → F
  | 0 => 1
  | k + 1 => powF a k * a

theorem powF_zero (a : F) : powF a 0 = 1 := rfl
theorem powF_succ (a : F) (k : Nat) : powF a (k + 1) = powF a k * a := rfl

theorem powF_one (a : F) : powF a 1 = a := by
  unfold powF
  exact lofOneMul a

theorem powF_add (a : F) (m n : Nat) : powF a (m + n) = powF a m * powF a n := by
  induction n with
  | zero =>
    change powF a m = powF a m * 1
    exact (lofMulOne _).symm
  | succ k ih =>
    rw [Nat.add_succ, powF_succ, powF_succ, ih, lofMulAssoc]

theorem powF_pos {a : F} (ha : 0 < a) (k : Nat) : 0 < powF a k := by
  induction k with
  | zero => exact LinearOrderedField.zero_lt_one
  | succ m ih => exact LinearOrderedField.mul_pos ih ha

theorem powF_nonneg {a : F} (ha : 0 ≤ a) (k : Nat) : 0 ≤ powF a k := by
  induction k with
  | zero => exact one_nonneg
  | succ m ih => exact mul_nonneg ih ha

theorem powF_le_powF {a b : F} (ha : 0 ≤ a) (hab : a ≤ b) (k : Nat) :
    powF a k ≤ powF b k := by
  induction k with
  | zero => exact LinearOrderedField.le_refl 1
  | succ m ih =>
    exact mul_le_mul ih hab ha (powF_nonneg (LinearOrderedField.le_trans ha hab) m)

theorem powF_mul_inv_cancel {a : F} (ha : a ≠ 0) (k : Nat) :
    powF a k * powF (a⁻¹) k = 1 := by
  induction k with
  | zero => exact lofOneMul 1
  | succ m ih =>
    calc
      (powF a m * a) * (powF (a⁻¹) m * a⁻¹)
        = powF a m * (powF (a⁻¹) m * (a * a⁻¹)) := by
          rw [lofMulComm (powF (a⁻¹) m) a⁻¹, lofMulAssoc (powF a m) a _,
              ← lofMulAssoc a a⁻¹ (powF (a⁻¹) m), lofMulComm (a * a⁻¹) (powF (a⁻¹) m)]
      _ = powF a m * (powF (a⁻¹) m * 1) := by rw [lofMulInvCancel ha]
      _ = powF a m * powF (a⁻¹) m := by rw [lofMulOne]
      _ = 1 := ih

/-- Absolute value `|a|` in a `LinearOrderedField F`. -/
noncomputable def absF (a : F) : F :=
  @ite _ (0 ≤ a) (Classical.propDecidable (0 ≤ a)) a (-a)

theorem absF_of_nonneg {a : F} (h : 0 ≤ a) : absF a = a := by
  unfold absF
  exact if_pos h

theorem absF_of_neg {a : F} (h : a < 0) : absF a = -a := by
  unfold absF
  exact if_neg (not_le_of_lt h)

theorem absF_zero : absF (0 : F) = 0 :=
  absF_of_nonneg (LinearOrderedField.le_refl 0)

theorem absF_nonneg (a : F) : 0 ≤ absF a := by
  rcases LinearOrderedField.le_total 0 a with h | h
  · rw [absF_of_nonneg h]
    exact h
  · by_cases ha0 : a = 0
    · rw [ha0, absF_zero]
      exact LinearOrderedField.le_refl 0
    · rw [absF_of_neg (lt_of_le_of_ne h ha0)]
      exact neg_nonneg.mpr h

theorem absF_pos_of_ne_zero {a : F} (ha : a ≠ 0) : 0 < absF a := by
  rcases lt_trichotomy 0 a with hp | heq | hn
  · rw [absF_of_nonneg (le_of_lt hp)]
    exact hp
  · exact False.elim (ha heq.symm)
  · rw [absF_of_neg hn]
    exact neg_pos.mpr hn

theorem absF_neg (a : F) : absF (-a) = absF a := by
  rcases lt_trichotomy 0 a with hp | heq | hn
  · have hna : -a < 0 := by
      have h1 := add_lt_add_right hp (-a)
      rw [lofZeroAdd, add_neg_cancel] at h1
      exact h1
    rw [absF_of_nonneg (le_of_lt hp), absF_of_neg hna, neg_neg]
  · rw [← heq, neg_zero]
  · have hna : 0 < -a := neg_pos.mpr hn
    rw [absF_of_neg hn, absF_of_nonneg (le_of_lt hna)]

theorem le_absF_self (a : F) : a ≤ absF a := by
  rcases LinearOrderedField.le_total 0 a with h | h
  · rw [absF_of_nonneg h]
    exact LinearOrderedField.le_refl a
  · exact LinearOrderedField.le_trans h (absF_nonneg a)

theorem neg_le_absF_self (a : F) : -a ≤ absF a := by
  rw [← absF_neg a]
  exact le_absF_self (-a)

theorem absF_le_iff {a b : F} : absF a ≤ b ↔ -b ≤ a ∧ a ≤ b := by
  constructor
  · intro h
    refine ⟨?_, LinearOrderedField.le_trans (le_absF_self a) h⟩
    have h1 : -a ≤ b := LinearOrderedField.le_trans (neg_le_absF_self a) h
    have h2 := neg_le_neg h1
    rw [neg_neg] at h2
    exact h2
  · intro ⟨h1, h2⟩
    rcases LinearOrderedField.le_total 0 a with hp | hn
    · rw [absF_of_nonneg hp]
      exact h2
    · by_cases ha0 : a = 0
      · rw [ha0, absF_zero]
        rw [ha0] at h2
        exact h2
      · rw [absF_of_neg (lt_of_le_of_ne hn ha0)]
        have h3 := neg_le_neg h1
        rw [neg_neg] at h3
        exact h3

theorem absF_add (a b : F) : absF (a + b) ≤ absF a + absF b := by
  apply absF_le_iff.mpr
  refine ⟨?_, add_le_add (le_absF_self a) (le_absF_self b)⟩
  rw [neg_add_rev]
  have h1 := neg_le_neg (neg_le_absF_self a)
  have h2 := neg_le_neg (neg_le_absF_self b)
  rw [neg_neg] at h1 h2
  exact add_le_add h1 h2

theorem absF_mul (a b : F) : absF (a * b) = absF a * absF b := by
  rcases LinearOrderedField.le_total 0 a with ha | ha
  · rcases LinearOrderedField.le_total 0 b with hb | hb
    · rw [absF_of_nonneg ha, absF_of_nonneg hb, absF_of_nonneg (mul_nonneg ha hb)]
    · by_cases hb0 : b = 0
      · rw [hb0, mul_zero, absF_zero, mul_zero]
      · have hbn : b < 0 := lt_of_le_of_ne hb hb0
        have hab_ge : 0 ≤ a * -b := mul_nonneg ha (neg_nonneg.mpr hb)
        rw [← absF_neg (a * b), ← mul_neg, absF_of_nonneg hab_ge,
            absF_of_nonneg ha, absF_of_neg hbn]
  · by_cases ha0 : a = 0
    · rw [ha0, zero_mul, absF_zero, zero_mul]
    · have han : a < 0 := lt_of_le_of_ne ha ha0
      rcases LinearOrderedField.le_total 0 b with hb | hb
      · have hab_ge : 0 ≤ -a * b := mul_nonneg (neg_nonneg.mpr ha) hb
        rw [← absF_neg (a * b), ← neg_mul, absF_of_nonneg hab_ge,
            absF_of_neg han, absF_of_nonneg hb]
      · by_cases hb0 : b = 0
        · rw [hb0, mul_zero, absF_zero, mul_zero]
        · have hbn : b < 0 := lt_of_le_of_ne hb hb0
          have hab_ge : 0 ≤ a * b := by
            rw [← neg_mul_neg]
            exact mul_nonneg (neg_nonneg.mpr ha) (neg_nonneg.mpr hb)
          rw [absF_of_neg han, absF_of_neg hbn, absF_of_nonneg hab_ge, neg_mul_neg]

theorem absF_inv (a : F) : absF (a⁻¹) = (absF a)⁻¹ := by
  by_cases ha : a = 0
  · rw [ha, LinearOrderedField.inv_zero, absF_zero, LinearOrderedField.inv_zero]
  · apply mul_left_cancel (ne_of_gt (absF_pos_of_ne_zero ha))
    rw [← absF_mul, lofMulInvCancel ha,
        absF_of_nonneg (one_nonneg (F := F)),
        lofMulInvCancel (ne_of_gt (absF_pos_of_ne_zero ha))]

theorem absF_div (a b : F) : absF (a / b) = absF a / absF b := by
  rw [lofDivEqMulInv, lofDivEqMulInv, absF_mul, absF_inv]

theorem absF_powF (a : F) (k : Nat) : absF (powF a k) = powF (absF a) k := by
  induction k with
  | zero => exact absF_of_nonneg one_nonneg
  | succ m ih => rw [powF_succ, powF_succ, absF_mul, ih]

/-! ### Finite Sums, Vectors, and Matrices -/

/-- Sum over `a, a + 1, ..., a + len - 1`. -/
def sumRange (a : Nat) : Nat → (Nat → F) → F
  | 0, _ => 0
  | len + 1, f => sumRange a len f + f (a + len)

theorem sumRange_zero (a : Nat) (f : Nat → F) : sumRange a 0 f = 0 := rfl
theorem sumRange_succ (a len : Nat) (f : Nat → F) :
    sumRange a (len + 1) f = sumRange a len f + f (a + len) := rfl

theorem sumRange_congr (a len : Nat) {f g : Nat → F}
    (h : ∀ j, a ≤ j → j < a + len → f j = g j) :
    sumRange a len f = sumRange a len g := by
  induction len with
  | zero => rfl
  | succ k ih =>
    rw [sumRange_succ, sumRange_succ,
        ih (fun j h1 h2 => h j h1 (by omega)),
        h (a + k) (by omega) (by omega)]

theorem sumRange_add (a len : Nat) (f g : Nat → F) :
    sumRange a len (fun j => f j + g j) = sumRange a len f + sumRange a len g := by
  induction len with
  | zero => exact (lofAddZero 0).symm
  | succ k ih =>
    rw [sumRange_succ, sumRange_succ, sumRange_succ, ih]
    rw [lofAddAssoc (sumRange a k f) (sumRange a k g) (f (a + k) + g (a + k))]
    rw [← lofAddAssoc (sumRange a k g) (f (a + k)) (g (a + k))]
    rw [lofAddComm (sumRange a k g) (f (a + k))]
    rw [lofAddAssoc (f (a + k)) (sumRange a k g) (g (a + k))]
    rw [← lofAddAssoc (sumRange a k f) (f (a + k)) _]

theorem sumRange_mul_left (c : F) (a len : Nat) (f : Nat → F) :
    c * sumRange a len f = sumRange a len (fun j => c * f j) := by
  induction len with
  | zero => exact mul_zero c
  | succ k ih => rw [sumRange_succ, sumRange_succ, lofLeftDistrib, ih]

theorem sumRange_mul_right (c : F) (a len : Nat) (f : Nat → F) :
    sumRange a len f * c = sumRange a len (fun j => f j * c) := by
  induction len with
  | zero => exact zero_mul c
  | succ k ih => rw [sumRange_succ, sumRange_succ, lofRightDistrib, ih]

theorem sumRange_nonneg (a len : Nat) {f : Nat → F}
    (hf : ∀ j, a ≤ j → j < a + len → 0 ≤ f j) :
    0 ≤ sumRange a len f := by
  induction len with
  | zero => exact LinearOrderedField.le_refl 0
  | succ k ih =>
    rw [sumRange_succ]
    have h1 := ih (fun j hj1 hj2 => hf j hj1 (by omega))
    have h2 := hf (a + k) (by omega) (by omega)
    have h := add_le_add h1 h2
    rw [lofAddZero] at h
    exact h

theorem sumRange_le_sumRange (a len : Nat) {f g : Nat → F}
    (h : ∀ j, a ≤ j → j < a + len → f j ≤ g j) :
    sumRange a len f ≤ sumRange a len g := by
  induction len with
  | zero => exact LinearOrderedField.le_refl 0
  | succ k ih =>
    rw [sumRange_succ, sumRange_succ]
    exact add_le_add (ih (fun j h1 h2 => h j h1 (by omega))) (h (a + k) (by omega) (by omega))

theorem absF_sumRange_le (a len : Nat) (f : Nat → F) :
    absF (sumRange a len f) ≤ sumRange a len (fun j => absF (f j)) := by
  induction len with
  | zero =>
    rw [sumRange_zero, sumRange_zero, absF_zero]
    exact LinearOrderedField.le_refl 0
  | succ k ih =>
    rw [sumRange_succ, sumRange_succ]
    exact LinearOrderedField.le_trans (absF_add _ _) (add_le_add ih (LinearOrderedField.le_refl _))

theorem sumRange_head (a len : Nat) (f : Nat → F) :
    sumRange a (len + 1) f = f a + sumRange (a + 1) len f := by
  induction len with
  | zero =>
    rw [sumRange_succ, sumRange_zero, sumRange_zero, lofZeroAdd, lofAddZero]
    rfl
  | succ k ih =>
    rw [sumRange_succ a (k + 1), ih, sumRange_succ (a + 1) k, lofAddAssoc]
    have heq : a + (k + 1) = (a + 1) + k := by omega
    rw [heq]

theorem sumRange_shift (a len : Nat) (f : Nat → F) :
    sumRange (a + 1) len f = sumRange a len (fun j => f (j + 1)) := by
  induction len with
  | zero => rfl
  | succ k ih =>
    rw [sumRange_succ, sumRange_succ, ih]
    have heq : (a + 1) + k = (a + k) + 1 := by omega
    rw [heq]

theorem sumRange_one_reflect (k : Nat) (f : Nat → F) :
    sumRange 1 k (fun j => f (k + 1 - j)) = sumRange 1 k f := by
  induction k with
  | zero => rfl
  | succ m ih =>
    rw [sumRange_head 1 m (fun j => f (m + 2 - j))]
    rw [sumRange_shift 1 m (fun j => f (m + 2 - j))]
    have hsub1 : m + 2 - 1 = m + 1 := by omega
    have hcongr : sumRange 1 m (fun j => f (m + 2 - (j + 1))) =
        sumRange 1 m (fun j => f (m + 1 - j)) := by
      apply sumRange_congr
      intro j _ _
      have he : m + 2 - (j + 1) = m + 1 - j := by omega
      rw [he]
    rw [hsub1, hcongr, ih, lofAddComm]
    have he2 : m + 1 = 1 + m := by omega
    calc
      sumRange 1 m f + f (m + 1) = sumRange 1 m f + f (1 + m) := by rw [he2]
      _ = sumRange 1 (m + 1) f := (sumRange_succ 1 m f).symm

theorem sumRange_telescoping (a len : Nat) (g : Nat → F) :
    sumRange a len (fun j => g j - g (j + 1)) = g a - g (a + len) := by
  induction len with
  | zero =>
    rw [sumRange_zero, Nat.add_zero, sub_self]
  | succ k ih =>
    rw [sumRange_succ, ih]
    calc
      (g a - g (a + k)) + (g (a + k) - g (a + k + 1))
        = g a + (-g (a + k) + (g (a + k) + -g (a + (k + 1)))) := by
          have he : a + k + 1 = a + (k + 1) := by omega
          rw [he, lofSubEqAddNeg, lofSubEqAddNeg, lofAddAssoc]
      _ = g a + ((-g (a + k) + g (a + k)) + -g (a + (k + 1))) := by
          rw [← lofAddAssoc (-g (a + k)) (g (a + k)) _]
      _ = g a - g (a + (k + 1)) := by
          rw [lofNegAddCancel, lofZeroAdd, ← lofSubEqAddNeg]

/-- Sum over `Fin n`: `finSum n g = g 0 + g 1 + ... + g (n - 1)`. -/
def finSum : (n : Nat) → (Fin n → F) → F
  | 0, _ => 0
  | n + 1, g =>
    finSum n (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + g ⟨n, Nat.lt_succ_self n⟩

theorem finSum_zero (g : Fin 0 → F) : finSum 0 g = 0 := rfl

theorem finSum_succ (n : Nat) (g : Fin (n + 1) → F) :
    finSum (n + 1) g =
      finSum n (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + g ⟨n, Nat.lt_succ_self n⟩ := rfl

theorem finSum_zero_fn (n : Nat) : finSum n (fun _ : Fin n => (0 : F)) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [finSum_succ, ih, lofAddZero]

theorem finSum_congr {n : Nat} {f g : Fin n → F} (h : ∀ i, f i = g i) :
    finSum n f = finSum n g := by
  have hfg : f = g := funext h
  rw [hfg]

theorem finSum_add (n : Nat) (f g : Fin n → F) :
    finSum n (fun i => f i + g i) = finSum n f + finSum n g := by
  induction n with
  | zero => exact (lofAddZero 0).symm
  | succ k ih =>
    rw [finSum_succ, finSum_succ, finSum_succ, ih]
    rw [lofAddAssoc (finSum k _) (finSum k _) _]
    rw [← lofAddAssoc (finSum k (fun i => g _)) (f _) (g _)]
    rw [lofAddComm (finSum k (fun i => g _)) (f _)]
    rw [lofAddAssoc (f _) (finSum k (fun i => g _)) (g _)]
    rw [← lofAddAssoc]

theorem finSum_neg (n : Nat) (f : Fin n → F) :
    finSum n (fun i => - f i) = - finSum n f := by
  induction n with
  | zero => exact neg_zero.symm
  | succ k ih =>
    rw [finSum_succ, finSum_succ, ih, neg_add_rev]

theorem finSum_sub (n : Nat) (f g : Fin n → F) :
    finSum n (fun i => f i - g i) = finSum n f - finSum n g := by
  have h1 : (fun i => f i - g i) = (fun i => f i + - g i) :=
    funext (fun i => lofSubEqAddNeg (f i) (g i))
  rw [h1, finSum_add, finSum_neg, ← lofSubEqAddNeg]

theorem finSum_mul_left (c : F) (n : Nat) (f : Fin n → F) :
    c * finSum n f = finSum n (fun i => c * f i) := by
  induction n with
  | zero => exact mul_zero c
  | succ k ih =>
    rw [finSum_succ, finSum_succ, lofLeftDistrib, ih]

theorem finSum_mul_right (c : F) (n : Nat) (f : Fin n → F) :
    finSum n f * c = finSum n (fun i => f i * c) := by
  induction n with
  | zero => exact zero_mul c
  | succ k ih =>
    rw [finSum_succ, finSum_succ, lofRightDistrib, ih]

theorem finSum_comm (m n : Nat) (h : Fin m → Fin n → F) :
    finSum m (fun i => finSum n (fun j => h i j)) =
    finSum n (fun j => finSum m (fun i => h i j)) := by
  induction m with
  | zero =>
    rw [finSum_zero]
    exact (finSum_zero_fn n).symm
  | succ k ih =>
    rw [finSum_succ, ih]
    have hr : (fun j => finSum (k + 1) (fun i => h i j)) =
        (fun j => finSum k (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ j) +
          h ⟨k, Nat.lt_succ_self k⟩ j) :=
      funext (fun j => finSum_succ k (fun i => h i j))
    rw [hr, finSum_add]

theorem finSum_eq_single (n : Nat) (i₀ : Fin n) (f : Fin n → F)
    (h0 : ∀ i : Fin n, i ≠ i₀ → f i = 0) :
    finSum n f = f i₀ := by
  induction n with
  | zero => exact Fin.elim0 i₀
  | succ k ih =>
    rw [finSum_succ]
    by_cases htop : i₀.val = k
    · have hz : finSum k (fun i : Fin k => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) = 0 := by
        have hfn : (fun i : Fin k => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) = (fun _ => 0) := by
          funext i
          apply h0
          intro heq
          have hv := congrArg Fin.val heq
          have hi := i.isLt
          dsimp only at hv
          omega
        rw [hfn, finSum_zero_fn]
      have hi0 : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = i₀ := Fin.ext htop.symm
      rw [hz, lofZeroAdd, hi0]
    · have hlt : i₀.val < k := by
        have hi := i₀.isLt
        omega
      let i₀' : Fin k := ⟨i₀.val, hlt⟩
      have hlast : f ⟨k, Nat.lt_succ_self k⟩ = 0 := by
        apply h0
        intro heq
        exact htop (congrArg Fin.val heq).symm
      have hrec := ih i₀' (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) (by
        intro i hne
        apply h0
        intro heq
        apply hne
        have hv : i.val = i₀'.val := congrArg (@Fin.val (k + 1)) heq
        exact Fin.ext hv)
      rw [hrec, hlast, lofAddZero]

theorem finSum_nonneg (n : Nat) {f : Fin n → F} (hf : ∀ i, 0 ≤ f i) :
    0 ≤ finSum n f := by
  induction n with
  | zero => exact LinearOrderedField.le_refl 0
  | succ k ih =>
    rw [finSum_succ]
    have h1 : 0 ≤ finSum k (fun i : Fin k => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) :=
      ih (fun i => hf ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    have h2 : 0 ≤ f ⟨k, Nat.lt_succ_self k⟩ := hf ⟨k, Nat.lt_succ_self k⟩
    have h := add_le_add h1 h2
    rw [lofAddZero] at h
    exact h

theorem finSum_le_finSum (n : Nat) {f g : Fin n → F} (h : ∀ i, f i ≤ g i) :
    finSum n f ≤ finSum n g := by
  induction n with
  | zero => exact LinearOrderedField.le_refl 0
  | succ k ih =>
    rw [finSum_succ, finSum_succ]
    exact add_le_add (ih (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
      (h ⟨k, Nat.lt_succ_self k⟩)

theorem absF_finSum_le (n : Nat) (f : Fin n → F) :
    absF (finSum n f) ≤ finSum n (fun i => absF (f i)) := by
  induction n with
  | zero =>
    rw [finSum_zero, finSum_zero, absF_zero]
    exact LinearOrderedField.le_refl 0
  | succ k ih =>
    rw [finSum_succ, finSum_succ]
    exact LinearOrderedField.le_trans (absF_add _ _)
      (add_le_add (ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
        (LinearOrderedField.le_refl _))

/-- `n`-dimensional vectors and `n × n` matrices over `F`. -/
abbrev Vec (n : Nat) (F : Type u) := Fin n → F
abbrev Mat (n : Nat) (F : Type u) := Fin n → Fin n → F

def vecZero (n : Nat) : Vec n F := fun _ => 0
def vecAdd {n : Nat} (u v : Vec n F) : Vec n F := fun i => u i + v i
def vecSub {n : Nat} (u v : Vec n F) : Vec n F := fun i => u i - v i
def vecNeg {n : Nat} (u : Vec n F) : Vec n F := fun i => - u i
def vecSmul {n : Nat} (c : F) (u : Vec n F) : Vec n F := fun i => c * u i
def vecDot {n : Nat} (u v : Vec n F) : F := finSum n (fun i => u i * v i)

def matZero (n : Nat) : Mat n F := fun _ _ => 0
def matId (n : Nat) : Mat n F := fun i j => if i = j then 1 else 0
def matAdd {n : Nat} (A B : Mat n F) : Mat n F := fun i j => A i j + B i j
def matSub {n : Nat} (A B : Mat n F) : Mat n F := fun i j => A i j - B i j
def matNeg {n : Nat} (A : Mat n F) : Mat n F := fun i j => - A i j
def matSmul {n : Nat} (c : F) (A : Mat n F) : Mat n F := fun i j => c * A i j
def matTranspose {n : Nat} (A : Mat n F) : Mat n F := fun i j => A j i
def matVec {n : Nat} (A : Mat n F) (v : Vec n F) : Vec n F :=
  fun i => finSum n (fun j => A i j * v j)
def matMul {n : Nat} (A B : Mat n F) : Mat n F :=
  fun i j => finSum n (fun k => A i k * B k j)
def matTrace {n : Nat} (A : Mat n F) : F := finSum n (fun i => A i i)

/-- Rank-one outer-product matrix `(v w^T) / d`. -/
def rankOneProj {n : Nat} (v w : Vec n F) (d : F) : Mat n F :=
  fun i j => (v i * w j) / d

/-- Vector `ℓ₁` norm `‖v‖₁ = ∑_i |v_i|` and matrix entry-sum norm `‖A‖_sum = ∑_{i,j} |A_{ij}|`. -/
noncomputable def vecNorm1 {n : Nat} (v : Vec n F) : F :=
  finSum n (fun i => absF (v i))

noncomputable def matNormSum {n : Nat} (A : Mat n F) : F :=
  finSum n (fun i => finSum n (fun j => absF (A i j)))

/-! ### Core Vector and Matrix Algebraic Identities -/

theorem vecAdd_comm {n : Nat} (u v : Vec n F) : vecAdd u v = vecAdd v u :=
  funext (fun i => lofAddComm (u i) (v i))

theorem vecAdd_assoc {n : Nat} (u v w : Vec n F) :
    vecAdd (vecAdd u v) w = vecAdd u (vecAdd v w) :=
  funext (fun i => lofAddAssoc (u i) (v i) (w i))

theorem vecAdd_zero {n : Nat} (u : Vec n F) : vecAdd u (vecZero n) = u :=
  funext (fun i => lofAddZero (u i))

theorem zero_vecAdd {n : Nat} (u : Vec n F) : vecAdd (vecZero n) u = u :=
  funext (fun i => lofZeroAdd (u i))

theorem vecSub_self {n : Nat} (u : Vec n F) : vecSub u u = vecZero n :=
  funext (fun i => sub_self (u i))

theorem matVec_zero {n : Nat} (A : Mat n F) : matVec A (vecZero n) = vecZero n := by
  funext i
  unfold matVec vecZero
  have h : (fun j : Fin n => A i j * 0) = (fun _ => 0) := funext (fun j => mul_zero (A i j))
  rw [h, finSum_zero_fn]

theorem zero_matVec {n : Nat} (v : Vec n F) : matVec (matZero n) v = vecZero n := by
  funext i
  unfold matVec matZero vecZero
  have h : (fun j : Fin n => (0 : F) * v j) = (fun _ => 0) := funext (fun j => zero_mul (v j))
  rw [h, finSum_zero_fn]

theorem matVec_id {n : Nat} (v : Vec n F) : matVec (matId n) v = v := by
  funext i
  unfold matVec matId
  rw [finSum_eq_single n i _ (fun j hne => by
    have hij : i ≠ j := Ne.symm hne
    rw [if_neg hij, zero_mul])]
  rw [if_pos rfl, lofOneMul]

theorem matVec_add {n : Nat} (A : Mat n F) (u v : Vec n F) :
    matVec A (vecAdd u v) = vecAdd (matVec A u) (matVec A v) := by
  funext i
  unfold matVec vecAdd
  have h : (fun j => A i j * (u j + v j)) = (fun j => A i j * u j + A i j * v j) :=
    funext (fun j => lofLeftDistrib (A i j) (u j) (v j))
  rw [h, finSum_add]

theorem matVec_sub {n : Nat} (A : Mat n F) (u v : Vec n F) :
    matVec A (vecSub u v) = vecSub (matVec A u) (matVec A v) := by
  funext i
  unfold matVec vecSub
  have h : (fun j => A i j * (u j - v j)) = (fun j => A i j * u j - A i j * v j) :=
    funext (fun j => mul_sub (A i j) (u j) (v j))
  rw [h, finSum_sub]

theorem matVec_neg {n : Nat} (A : Mat n F) (u : Vec n F) :
    matVec A (vecNeg u) = vecNeg (matVec A u) := by
  funext i
  unfold matVec vecNeg
  have h : (fun j => A i j * - u j) = (fun j => - (A i j * u j)) :=
    funext (fun j => mul_neg (A i j) (u j))
  rw [h, finSum_neg]

theorem matVec_smul {n : Nat} (A : Mat n F) (c : F) (u : Vec n F) :
    matVec A (vecSmul c u) = vecSmul c (matVec A u) := by
  funext i
  unfold matVec vecSmul
  rw [finSum_mul_left]
  apply finSum_congr
  intro j
  rw [← lofMulAssoc, lofMulComm (A i j) c, lofMulAssoc]

theorem add_matVec {n : Nat} (A B : Mat n F) (v : Vec n F) :
    matVec (matAdd A B) v = vecAdd (matVec A v) (matVec B v) := by
  funext i
  unfold matVec matAdd vecAdd
  have h : (fun j => (A i j + B i j) * v j) = (fun j => A i j * v j + B i j * v j) :=
    funext (fun j => lofRightDistrib (A i j) (B i j) (v j))
  rw [h, finSum_add]

theorem sub_matVec {n : Nat} (A B : Mat n F) (v : Vec n F) :
    matVec (matSub A B) v = vecSub (matVec A v) (matVec B v) := by
  funext i
  unfold matVec matSub vecSub
  have h : (fun j => (A i j - B i j) * v j) = (fun j => A i j * v j - B i j * v j) :=
    funext (fun j => sub_mul (A i j) (B i j) (v j))
  rw [h, finSum_sub]

theorem smul_matVec {n : Nat} (c : F) (A : Mat n F) (v : Vec n F) :
    matVec (matSmul c A) v = vecSmul c (matVec A v) := by
  funext i
  unfold matVec matSmul vecSmul
  rw [finSum_mul_left]
  apply finSum_congr
  intro j
  exact lofMulAssoc c (A i j) (v j)

theorem matVec_matVec {n : Nat} (A B : Mat n F) (v : Vec n F) :
    matVec A (matVec B v) = matVec (matMul A B) v := by
  funext i
  unfold matVec matMul
  have h1 : (fun j => A i j * finSum n (fun k => B j k * v k)) =
      (fun j => finSum n (fun k => (A i j * B j k) * v k)) := by
    funext j
    rw [finSum_mul_left]
    exact finSum_congr (fun k => (lofMulAssoc (A i j) (B j k) (v k)).symm)
  rw [h1, finSum_comm]
  exact finSum_congr (fun k => (finSum_mul_right (v k) n (fun j => A i j * B j k)).symm)

theorem vecDot_zero_right {n : Nat} (u : Vec n F) : vecDot u (vecZero n) = 0 := by
  unfold vecDot vecZero
  have h : (fun i : Fin n => u i * 0) = (fun _ => 0) := funext (fun i => mul_zero (u i))
  rw [h, finSum_zero_fn]

theorem vecDot_add_right {n : Nat} (w u v : Vec n F) :
    vecDot w (vecAdd u v) = vecDot w u + vecDot w v := by
  unfold vecDot vecAdd
  have h : (fun i => w i * (u i + v i)) = (fun i => w i * u i + w i * v i) :=
    funext (fun i => lofLeftDistrib (w i) (u i) (v i))
  rw [h, finSum_add]

theorem vecDot_sub_right {n : Nat} (w u v : Vec n F) :
    vecDot w (vecSub u v) = vecDot w u - vecDot w v := by
  unfold vecDot vecSub
  have h : (fun i => w i * (u i - v i)) = (fun i => w i * u i - w i * v i) :=
    funext (fun i => mul_sub (w i) (u i) (v i))
  rw [h, finSum_sub]

theorem vecDot_smul_right {n : Nat} (w : Vec n F) (c : F) (v : Vec n F) :
    vecDot w (vecSmul c v) = c * vecDot w v := by
  unfold vecDot vecSmul
  rw [finSum_mul_left]
  apply finSum_congr
  intro i
  rw [← lofMulAssoc, lofMulComm (w i) c, lofMulAssoc]

theorem vecDot_matVec {n : Nat} (w : Vec n F) (A : Mat n F) (v : Vec n F) :
    vecDot w (matVec A v) = vecDot (matVec (matTranspose A) w) v := by
  unfold vecDot matVec matTranspose
  have h1 : (fun i => w i * finSum n (fun j => A i j * v j)) =
      (fun i => finSum n (fun j => (A i j * w i) * v j)) := by
    funext i
    rw [finSum_mul_left]
    apply finSum_congr
    intro j
    rw [← lofMulAssoc, lofMulComm (w i) (A i j)]
  rw [h1, finSum_comm]
  exact finSum_congr (fun j => (finSum_mul_right (v j) n (fun i => A i j * w i)).symm)

theorem matMul_assoc {n : Nat} (A B C : Mat n F) :
    matMul (matMul A B) C = matMul A (matMul B C) := by
  funext i j
  unfold matMul
  have h1 : (fun k => finSum n (fun m => A i m * B m k) * C k j) =
      (fun k => finSum n (fun m => A i m * (B m k * C k j))) := by
    funext k
    rw [finSum_mul_right]
    exact finSum_congr (fun m => lofMulAssoc (A i m) (B m k) (C k j))
  rw [h1, finSum_comm]
  exact finSum_congr (fun m => (finSum_mul_left (A i m) n (fun k => B m k * C k j)).symm)

theorem matMul_id_right {n : Nat} (A : Mat n F) : matMul A (matId n) = A := by
  funext i j
  unfold matMul matId
  rw [finSum_eq_single n j _ (fun k hne => by rw [if_neg hne, mul_zero])]
  rw [if_pos rfl, lofMulOne]

theorem matMul_id_left {n : Nat} (A : Mat n F) : matMul (matId n) A = A := by
  funext i j
  unfold matMul matId
  rw [finSum_eq_single n i _ (fun k hne => by
    have hik : i ≠ k := Ne.symm hne
    rw [if_neg hik, zero_mul])]
  rw [if_pos rfl, lofOneMul]

theorem matMul_zero_right {n : Nat} (A : Mat n F) : matMul A (matZero n) = matZero n := by
  funext i j
  unfold matMul matZero
  have h : (fun k : Fin n => A i k * 0) = (fun _ => 0) := funext (fun k => mul_zero (A i k))
  rw [h, finSum_zero_fn]

theorem matMul_zero_left {n : Nat} (A : Mat n F) : matMul (matZero n) A = matZero n := by
  funext i j
  unfold matMul matZero
  have h : (fun k : Fin n => (0 : F) * A k j) = (fun _ => 0) := funext (fun k => zero_mul (A k j))
  rw [h, finSum_zero_fn]

theorem matMul_add_right {n : Nat} (A B C : Mat n F) :
    matMul A (matAdd B C) = matAdd (matMul A B) (matMul A C) := by
  funext i j
  unfold matMul matAdd
  have h : (fun k => A i k * (B k j + C k j)) = (fun k => A i k * B k j + A i k * C k j) :=
    funext (fun k => lofLeftDistrib _ _ _)
  rw [h, finSum_add]

theorem matMul_add_left {n : Nat} (A B C : Mat n F) :
    matMul (matAdd A B) C = matAdd (matMul A C) (matMul B C) := by
  funext i j
  unfold matMul matAdd
  have h : (fun k => (A i k + B i k) * C k j) = (fun k => A i k * C k j + B i k * C k j) :=
    funext (fun k => lofRightDistrib _ _ _)
  rw [h, finSum_add]

theorem matMul_sub_right {n : Nat} (A B C : Mat n F) :
    matMul A (matSub B C) = matSub (matMul A B) (matMul A C) := by
  funext i j
  unfold matMul matSub
  have h : (fun k => A i k * (B k j - C k j)) = (fun k => A i k * B k j - A i k * C k j) :=
    funext (fun k => mul_sub _ _ _)
  rw [h, finSum_sub]

theorem matMul_sub_left {n : Nat} (A B C : Mat n F) :
    matMul (matSub A B) C = matSub (matMul A C) (matMul B C) := by
  funext i j
  unfold matMul matSub
  have h : (fun k => (A i k - B i k) * C k j) = (fun k => A i k * C k j - B i k * C k j) :=
    funext (fun k => sub_mul _ _ _)
  rw [h, finSum_sub]

theorem matMul_smul_left {n : Nat} (c : F) (A B : Mat n F) :
    matMul (matSmul c A) B = matSmul c (matMul A B) := by
  funext i j
  unfold matMul matSmul
  rw [finSum_mul_left]
  exact finSum_congr (fun k => lofMulAssoc c (A i k) (B k j))

theorem matMul_smul_right {n : Nat} (c : F) (A B : Mat n F) :
    matMul A (matSmul c B) = matSmul c (matMul A B) := by
  funext i j
  unfold matMul matSmul
  rw [finSum_mul_left]
  apply finSum_congr
  intro k
  rw [← lofMulAssoc, lofMulComm (A i k) c, lofMulAssoc]

theorem matTrace_comm {n : Nat} (A B : Mat n F) :
    matTrace (matMul A B) = matTrace (matMul B A) := by
  unfold matTrace matMul
  rw [finSum_comm]
  apply finSum_congr
  intro k
  apply finSum_congr
  intro i
  exact lofMulComm (A i k) (B k i)

theorem matTrace_rankOneProj_mul {n : Nat} (v w : Vec n F) (d : F) (A : Mat n F) :
    matTrace (matMul (rankOneProj v w d) A) = vecDot w (matVec A v) / d := by
  unfold matTrace matMul rankOneProj vecDot matVec
  rw [lofDivEqMulInv]
  rw [finSum_mul_right]
  have h1 : (fun i => finSum n (fun k => ((v i * w k) / d) * A k i)) =
      (fun i => finSum n (fun k => ((w k * (A k i * v i)) * d⁻¹))) := by
    funext i
    apply finSum_congr
    intro k
    rw [lofDivEqMulInv]
    calc
      ((v i * w k) * d⁻¹) * A k i = (v i * w k) * (d⁻¹ * A k i) := lofMulAssoc _ _ _
      _ = (v i * w k) * (A k i * d⁻¹) := by rw [lofMulComm d⁻¹ (A k i)]
      _ = ((v i * w k) * A k i) * d⁻¹ := (lofMulAssoc _ _ _).symm
      _ = (w k * (A k i * v i)) * d⁻¹ := by
        congr 1
        rw [lofMulComm (v i) (w k), lofMulAssoc, lofMulComm (v i) (A k i)]
  rw [h1, finSum_comm]
  apply finSum_congr
  intro k
  rw [← finSum_mul_right, ← finSum_mul_left]

/-! ### Submultiplicative Norm Inequalities -/

theorem vecNorm1_nonneg {n : Nat} (v : Vec n F) : 0 ≤ vecNorm1 v :=
  finSum_nonneg n (fun i => absF_nonneg (v i))

theorem matNormSum_nonneg {n : Nat} (A : Mat n F) : 0 ≤ matNormSum A :=
  finSum_nonneg n (fun i => finSum_nonneg n (fun j => absF_nonneg (A i j)))

theorem vecNorm1_zero (n : Nat) : vecNorm1 (vecZero n : Vec n F) = 0 := by
  unfold vecNorm1 vecZero
  have h : (fun _ : Fin n => absF (0 : F)) = (fun _ => 0) := funext (fun _ => absF_zero)
  rw [h, finSum_zero_fn]

theorem vecNorm1_neg {n : Nat} (v : Vec n F) : vecNorm1 (vecNeg v) = vecNorm1 v := by
  unfold vecNorm1 vecNeg
  exact finSum_congr (fun i => absF_neg (v i))

theorem vecNorm1_smul {n : Nat} (c : F) (v : Vec n F) :
    vecNorm1 (vecSmul c v) = absF c * vecNorm1 v := by
  unfold vecNorm1 vecSmul
  rw [finSum_mul_left]
  exact finSum_congr (fun i => absF_mul c (v i))

theorem vecNorm1_add_le {n : Nat} (u v : Vec n F) :
    vecNorm1 (vecAdd u v) ≤ vecNorm1 u + vecNorm1 v := by
  unfold vecNorm1 vecAdd
  rw [← finSum_add]
  exact finSum_le_finSum n (fun i => absF_add (u i) (v i))

theorem absF_entry_le_vecNorm1 {n : Nat} (v : Vec n F) (j : Fin n) :
    absF (v j) ≤ vecNorm1 v := by
  unfold vecNorm1
  have hsingle : absF (v j) = finSum n (fun k => if k = j then absF (v k) else 0) := by
    rw [finSum_eq_single n j _ (fun k hne => if_neg hne)]
    exact (if_pos rfl).symm
  rw [hsingle]
  apply finSum_le_finSum
  intro k
  by_cases hkj : k = j
  · rw [if_pos hkj]
    exact LinearOrderedField.le_refl _
  · rw [if_neg hkj]
    exact absF_nonneg (v k)

theorem absF_vecDot_le {n : Nat} (w v : Vec n F) :
    absF (vecDot w v) ≤ vecNorm1 w * vecNorm1 v := by
  unfold vecDot
  apply LinearOrderedField.le_trans (absF_finSum_le n _)
  unfold vecNorm1
  rw [finSum_mul_right]
  apply finSum_le_finSum
  intro i
  rw [absF_mul]
  exact mul_le_mul_of_nonneg_left (absF_entry_le_vecNorm1 v i) (absF_nonneg (w i))

theorem vecNorm1_matVec_le {n : Nat} (A : Mat n F) (v : Vec n F) :
    vecNorm1 (matVec A v) ≤ matNormSum A * vecNorm1 v := by
  unfold vecNorm1 matVec matNormSum
  rw [finSum_mul_right]
  apply finSum_le_finSum
  intro i
  apply LinearOrderedField.le_trans (absF_finSum_le n _)
  rw [finSum_mul_right]
  apply finSum_le_finSum
  intro j
  rw [absF_mul]
  exact mul_le_mul_of_nonneg_left (absF_entry_le_vecNorm1 v j) (absF_nonneg (A i j))

end OrderedFieldLemmas

/-!
### Constructive Exact Rational Field `Q`
-/

structure RawQ where
  num : Int
  den : Int
  den_pos : 0 < den

namespace RawQ

def eqv (x y : RawQ) : Prop := x.num * y.den = y.num * x.den

theorem eqv_refl (x : RawQ) : eqv x x := rfl
theorem eqv_symm {x y : RawQ} (h : eqv x y) : eqv y x := h.symm

theorem eqv_trans {x y z : RawQ} (hxy : eqv x y) (hyz : eqv y z) : eqv x z := by
  unfold eqv at *
  have hyd_ne : y.den ≠ 0 := by
    have hp := y.den_pos
    omega
  apply Int.eq_of_mul_eq_mul_right hyd_ne
  calc
    x.num * z.den * y.den = (x.num * y.den) * z.den := by
      rw [Int.mul_assoc, Int.mul_comm z.den y.den, ← Int.mul_assoc]
    _ = (y.num * x.den) * z.den := by rw [hxy]
    _ = (y.num * z.den) * x.den := by
      rw [Int.mul_assoc, Int.mul_comm x.den z.den, ← Int.mul_assoc]
    _ = (z.num * y.den) * x.den := by rw [hyz]
    _ = z.num * x.den * y.den := by
      rw [Int.mul_assoc, Int.mul_comm y.den x.den, ← Int.mul_assoc]

instance setoid : Setoid RawQ where
  r := eqv
  iseqv := ⟨eqv_refl, eqv_symm, eqv_trans⟩

def zero : RawQ := ⟨0, 1, by decide⟩
def one : RawQ := ⟨1, 1, by decide⟩

def add (x y : RawQ) : RawQ :=
  ⟨x.num * y.den + y.num * x.den, x.den * y.den, Int.mul_pos x.den_pos y.den_pos⟩

def neg (x : RawQ) : RawQ :=
  ⟨-x.num, x.den, x.den_pos⟩

def mul (x y : RawQ) : RawQ :=
  ⟨x.num * y.num, x.den * y.den, Int.mul_pos x.den_pos y.den_pos⟩

def inv (x : RawQ) : RawQ :=
  if hpos : 0 < x.num then
    ⟨x.den, x.num, hpos⟩
  else if hneg : x.num < 0 then
    ⟨-x.den, -x.num, by omega⟩
  else
    ⟨0, 1, by decide⟩

def le (x y : RawQ) : Prop := x.num * y.den ≤ y.num * x.den
def lt (x y : RawQ) : Prop := x.num * y.den < y.num * x.den

theorem add_resp {x₁ x₂ y₁ y₂ : RawQ} (hx : eqv x₁ x₂) (hy : eqv y₁ y₂) :
    eqv (add x₁ y₁) (add x₂ y₂) := by
  unfold eqv add at *
  dsimp only
  calc
    (x₁.num * y₁.den + y₁.num * x₁.den) * (x₂.den * y₂.den)
      = (x₁.num * x₂.den) * (y₁.den * y₂.den) + (y₁.num * y₂.den) * (x₁.den * x₂.den) := by
        rw [Int.add_mul]
        congr 1
        · rw [Int.mul_assoc, ← Int.mul_assoc y₁.den x₂.den y₂.den,
              Int.mul_comm y₁.den x₂.den, Int.mul_assoc x₂.den y₁.den y₂.den, ← Int.mul_assoc]
        · rw [Int.mul_assoc, ← Int.mul_assoc x₁.den x₂.den y₂.den,
              Int.mul_comm (x₁.den * x₂.den) y₂.den, ← Int.mul_assoc]
    _ = (x₂.num * x₁.den) * (y₁.den * y₂.den) + (y₂.num * y₁.den) * (x₁.den * x₂.den) := by
        rw [hx, hy]
    _ = (x₂.num * y₂.den + y₂.num * x₂.den) * (x₁.den * y₁.den) := by
        rw [Int.add_mul]
        congr 1
        · rw [Int.mul_assoc, ← Int.mul_assoc x₁.den y₁.den y₂.den,
              Int.mul_comm (x₁.den * y₁.den) y₂.den, ← Int.mul_assoc]
        · calc
            y₂.num * y₁.den * (x₁.den * x₂.den)
              = y₂.num * (y₁.den * (x₁.den * x₂.den)) := Int.mul_assoc _ _ _
            _ = y₂.num * (x₂.den * (x₁.den * y₁.den)) := by
                congr 1
                rw [Int.mul_comm x₁.den x₂.den, ← Int.mul_assoc y₁.den x₂.den x₁.den,
                    Int.mul_comm y₁.den x₂.den, Int.mul_assoc x₂.den y₁.den x₁.den,
                    Int.mul_comm y₁.den x₁.den]
            _ = y₂.num * x₂.den * (x₁.den * y₁.den) := (Int.mul_assoc _ _ _).symm

theorem neg_resp {x₁ x₂ : RawQ} (hx : eqv x₁ x₂) : eqv (neg x₁) (neg x₂) := by
  unfold eqv neg at *
  dsimp only
  rw [Int.neg_mul, Int.neg_mul, hx]

theorem mul_resp {x₁ x₂ y₁ y₂ : RawQ} (hx : eqv x₁ x₂) (hy : eqv y₁ y₂) :
    eqv (mul x₁ y₁) (mul x₂ y₂) := by
  unfold eqv mul at *
  dsimp only
  calc
    (x₁.num * y₁.num) * (x₂.den * y₂.den)
      = (x₁.num * x₂.den) * (y₁.num * y₂.den) := by
        rw [Int.mul_assoc, ← Int.mul_assoc y₁.num x₂.den y₂.den,
            Int.mul_comm y₁.num x₂.den, Int.mul_assoc x₂.den y₁.num y₂.den, ← Int.mul_assoc]
    _ = (x₂.num * x₁.den) * (y₂.num * y₁.den) := by rw [hx, hy]
    _ = (x₂.num * y₂.num) * (x₁.den * y₁.den) := by
        rw [Int.mul_assoc, ← Int.mul_assoc x₁.den y₂.num y₁.den,
            Int.mul_comm x₁.den y₂.num, Int.mul_assoc y₂.num x₁.den y₁.den, ← Int.mul_assoc]

theorem sign_pos_iff {x₁ x₂ : RawQ} (hx : eqv x₁ x₂) : 0 < x₁.num ↔ 0 < x₂.num := by
  unfold eqv at hx
  have hd1 := x₁.den_pos
  have hd2 := x₂.den_pos
  constructor
  · intro h1
    have hp : 0 < x₁.num * x₂.den := Int.mul_pos h1 hd2
    rw [hx] at hp
    by_cases h2 : 0 < x₂.num
    · exact h2
    · have hle : x₂.num ≤ 0 := by omega
      have hnp : x₂.num * x₁.den ≤ 0 * x₁.den :=
        Int.mul_le_mul_of_nonneg_right hle (by omega)
      omega
  · intro h2
    have hp : 0 < x₂.num * x₁.den := Int.mul_pos h2 hd1
    rw [← hx] at hp
    by_cases h1 : 0 < x₁.num
    · exact h1
    · have hle : x₁.num ≤ 0 := by omega
      have hnp : x₁.num * x₂.den ≤ 0 * x₂.den :=
        Int.mul_le_mul_of_nonneg_right hle (by omega)
      omega

theorem sign_neg_iff {x₁ x₂ : RawQ} (hx : eqv x₁ x₂) : x₁.num < 0 ↔ x₂.num < 0 := by
  have hx' : eqv (neg x₁) (neg x₂) := neg_resp hx
  have h := sign_pos_iff hx'
  unfold neg at h
  dsimp only at h
  omega

theorem inv_resp {x₁ x₂ : RawQ} (hx : eqv x₁ x₂) : eqv (inv x₁) (inv x₂) := by
  unfold inv
  by_cases hp1 : 0 < x₁.num
  · have hp2 : 0 < x₂.num := (sign_pos_iff hx).mp hp1
    rw [dif_pos hp1, dif_pos hp2]
    unfold eqv at *
    dsimp only
    rw [Int.mul_comm x₁.den x₂.num, ← hx, Int.mul_comm x₁.num x₂.den]
  · rw [dif_neg hp1]
    have hp2 : ¬ (0 < x₂.num) := fun h => hp1 ((sign_pos_iff hx).mpr h)
    rw [dif_neg hp2]
    by_cases hn1 : x₁.num < 0
    · have hn2 : x₂.num < 0 := (sign_neg_iff hx).mp hn1
      rw [dif_pos hn1, dif_pos hn2]
      unfold eqv at *
      dsimp only
      rw [Int.neg_mul, Int.mul_neg, Int.neg_mul, Int.mul_neg,
          Int.mul_comm x₁.den x₂.num, ← hx, Int.mul_comm x₁.num x₂.den]
    · have hn2 : ¬ (x₂.num < 0) := fun h => hn1 ((sign_neg_iff hx).mpr h)
      rw [dif_neg hn1, dif_neg hn2]
      rfl

theorem le_iff_of_eqv {x₁ x₂ y₁ y₂ : RawQ} (hx : eqv x₁ x₂) (hy : eqv y₁ y₂) :
    le x₁ y₁ ↔ le x₂ y₂ := by
  unfold le eqv at *
  have hd1 := x₁.den_pos
  have hd2 := x₂.den_pos
  have he1 := y₁.den_pos
  have he2 := y₂.den_pos
  have hprod : (x₁.num * y₁.den) * (x₂.den * y₂.den) = (x₂.num * y₂.den) * (x₁.den * y₁.den) := by
    calc
      (x₁.num * y₁.den) * (x₂.den * y₂.den)
        = (x₁.num * x₂.den) * (y₁.den * y₂.den) := by
          rw [Int.mul_assoc, ← Int.mul_assoc y₁.den x₂.den y₂.den,
              Int.mul_comm y₁.den x₂.den, Int.mul_assoc x₂.den y₁.den y₂.den, ← Int.mul_assoc]
      _ = (x₂.num * x₁.den) * (y₁.den * y₂.den) := by rw [hx]
      _ = (x₂.num * y₂.den) * (x₁.den * y₁.den) := by
          rw [Int.mul_assoc, ← Int.mul_assoc x₁.den y₁.den y₂.den,
              Int.mul_comm (x₁.den * y₁.den) y₂.den, ← Int.mul_assoc]
  have hprod2 : (y₁.num * x₁.den) * (x₂.den * y₂.den) = (y₂.num * x₂.den) * (x₁.den * y₁.den) := by
    calc
      (y₁.num * x₁.den) * (x₂.den * y₂.den)
        = (y₁.num * y₂.den) * (x₁.den * x₂.den) := by
          rw [Int.mul_assoc, ← Int.mul_assoc x₁.den x₂.den y₂.den,
              Int.mul_comm (x₁.den * x₂.den) y₂.den, ← Int.mul_assoc]
      _ = (y₂.num * y₁.den) * (x₁.den * x₂.den) := by rw [hy]
      _ = (y₂.num * x₂.den) * (x₁.den * y₁.den) := by
          calc
            y₂.num * y₁.den * (x₁.den * x₂.den)
              = y₂.num * (y₁.den * (x₁.den * x₂.den)) := Int.mul_assoc _ _ _
            _ = y₂.num * (x₂.den * (x₁.den * y₁.den)) := by
                congr 1
                rw [Int.mul_comm x₁.den x₂.den, ← Int.mul_assoc y₁.den x₂.den x₁.den,
                    Int.mul_comm y₁.den x₂.den, Int.mul_assoc x₂.den y₁.den x₁.den,
                    Int.mul_comm y₁.den x₁.den]
            _ = y₂.num * x₂.den * (x₁.den * y₁.den) := (Int.mul_assoc _ _ _).symm
  have hp1 : 0 < x₁.den * y₁.den := Int.mul_pos hd1 he1
  have hp2 : 0 < x₂.den * y₂.den := Int.mul_pos hd2 he2
  constructor
  · intro h
    have hm := Int.mul_le_mul_of_nonneg_right h (by omega : 0 ≤ x₂.den * y₂.den)
    rw [hprod, hprod2] at hm
    by_cases hgoal : x₂.num * y₂.den ≤ y₂.num * x₂.den
    · exact hgoal
    · have hgt : y₂.num * x₂.den + 1 ≤ x₂.num * y₂.den := by omega
      have hm2 := Int.mul_le_mul_of_nonneg_right hgt (by omega : 0 ≤ x₁.den * y₁.den)
      rw [Int.add_mul, Int.one_mul] at hm2
      omega
  · intro h
    have hm := Int.mul_le_mul_of_nonneg_right h (by omega : 0 ≤ x₁.den * y₁.den)
    rw [← hprod, ← hprod2] at hm
    by_cases hgoal : x₁.num * y₁.den ≤ y₁.num * x₁.den
    · exact hgoal
    · have hgt : y₁.num * x₁.den + 1 ≤ x₁.num * y₁.den := by omega
      have hm2 := Int.mul_le_mul_of_nonneg_right hgt (by omega : 0 ≤ x₂.den * y₂.den)
      rw [Int.add_mul, Int.one_mul] at hm2
      omega

theorem lt_iff_le_not_le_raw (x y : RawQ) : lt x y ↔ le x y ∧ ¬ le y x := by
  unfold lt le
  omega

end RawQ

/-- Constructive exact rational numbers `Q` in Core Lean 4. -/
def Q : Type := Quotient RawQ.setoid

namespace Q

def mk (x : RawQ) : Q := Quotient.mk RawQ.setoid x

instance : Add Q where
  add := Quotient.lift₂ (fun a b => mk (RawQ.add a b))
    (fun _ _ _ _ ha hb => Quotient.sound (RawQ.add_resp ha hb))

instance : Neg Q where
  neg := Quotient.lift (fun a => mk (RawQ.neg a))
    (fun _ _ ha => Quotient.sound (RawQ.neg_resp ha))

instance : Sub Q where
  sub a b := a + -b

instance : Mul Q where
  mul := Quotient.lift₂ (fun a b => mk (RawQ.mul a b))
    (fun _ _ _ _ ha hb => Quotient.sound (RawQ.mul_resp ha hb))

instance : HasInv Q where
  inv := Quotient.lift (fun a => mk (RawQ.inv a))
    (fun _ _ ha => Quotient.sound (RawQ.inv_resp ha))

instance : Div Q where
  div a b := a * b⁻¹

instance : LE Q where
  le := Quotient.lift₂ RawQ.le
    (fun _ _ _ _ ha hb => propext (RawQ.le_iff_of_eqv ha hb))

instance : LT Q where
  lt a b := a ≤ b ∧ ¬ b ≤ a

private theorem int_add_assoc_4 (a b c : RawQ) :
    RawQ.eqv (RawQ.add (RawQ.add a b) c) (RawQ.add a (RawQ.add b c)) := by
  unfold RawQ.eqv RawQ.add
  dsimp only
  congr 1
  · rw [Int.add_mul, Int.add_mul, Int.add_assoc]
    congr 1
    · rw [Int.mul_assoc]
    · congr 1
      · rw [Int.mul_assoc b.num a.den c.den, Int.mul_comm a.den c.den,
            ← Int.mul_assoc b.num c.den a.den]
      · rw [Int.mul_comm a.den b.den, ← Int.mul_assoc c.num b.den a.den]
  · rw [Int.mul_assoc]

instance : HasZero Q := ⟨mk RawQ.zero⟩
instance : HasOne Q := ⟨mk RawQ.one⟩

instance : LinearOrderedField Q where
  add_assoc := fun a b c =>
    Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound (int_add_assoc_4 x y z))
  add_comm := fun a b =>
    Quotient.inductionOn₂ a b (fun x y => Quotient.sound (by
      change RawQ.eqv (RawQ.add x y) (RawQ.add y x)
      unfold RawQ.eqv RawQ.add; dsimp only
      rw [Int.add_comm (x.num * y.den) (y.num * x.den), Int.mul_comm x.den y.den]))
  zero_add := fun a =>
    Quotient.inductionOn a (fun x => Quotient.sound (by
      change RawQ.eqv (RawQ.add RawQ.zero x) x
      unfold RawQ.eqv RawQ.add RawQ.zero; dsimp only
      rw [Int.zero_mul, Int.zero_add, Int.mul_one, Int.one_mul]))
  add_zero := fun a =>
    Quotient.inductionOn a (fun x => Quotient.sound (by
      change RawQ.eqv (RawQ.add x RawQ.zero) x
      unfold RawQ.eqv RawQ.add RawQ.zero; dsimp only
      rw [Int.mul_one, Int.zero_mul, Int.add_zero, Int.mul_one]))
  neg_add_cancel := fun a =>
    Quotient.inductionOn a (fun x => Quotient.sound (by
      change RawQ.eqv (RawQ.add (RawQ.neg x) x) RawQ.zero
      unfold RawQ.eqv RawQ.add RawQ.neg RawQ.zero; dsimp only
      rw [Int.mul_one, Int.zero_mul, Int.neg_mul]
      omega))
  sub_eq_add_neg := fun _ _ => rfl
  mul_assoc := fun a b c =>
    Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound (by
      change RawQ.eqv (RawQ.mul (RawQ.mul x y) z) (RawQ.mul x (RawQ.mul y z))
      unfold RawQ.eqv RawQ.mul; dsimp only
      rw [Int.mul_assoc x.num y.num z.num, Int.mul_assoc x.den y.den z.den]))
  mul_comm := fun a b =>
    Quotient.inductionOn₂ a b (fun x y => Quotient.sound (by
      change RawQ.eqv (RawQ.mul x y) (RawQ.mul y x)
      unfold RawQ.eqv RawQ.mul; dsimp only
      rw [Int.mul_comm x.num y.num, Int.mul_comm x.den y.den]))
  one_mul := fun a =>
    Quotient.inductionOn a (fun x => Quotient.sound (by
      change RawQ.eqv (RawQ.mul RawQ.one x) x
      unfold RawQ.eqv RawQ.mul RawQ.one; dsimp only
      rw [Int.one_mul, Int.one_mul]))
  mul_one := fun a =>
    Quotient.inductionOn a (fun x => Quotient.sound (by
      change RawQ.eqv (RawQ.mul x RawQ.one) x
      unfold RawQ.eqv RawQ.mul RawQ.one; dsimp only
      rw [Int.mul_one, Int.mul_one]))
  left_distrib := fun a b c =>
    Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound (by
      change RawQ.eqv (RawQ.mul x (RawQ.add y z)) (RawQ.add (RawQ.mul x y) (RawQ.mul x z))
      unfold RawQ.eqv RawQ.mul RawQ.add; dsimp only
      calc
        x.num * (y.num * z.den + z.num * y.den) * (x.den * y.den * (x.den * z.den))
          = (x.num * y.num * z.den + x.num * z.num * y.den) *
            (x.den * (x.den * (y.den * z.den))) := by
              congr 1
              · rw [Int.mul_add, Int.mul_assoc x.num y.num z.den,
                    Int.mul_assoc x.num z.num y.den]
              · rw [Int.mul_assoc x.den y.den (x.den * z.den),
                    ← Int.mul_assoc y.den x.den z.den,
                    Int.mul_comm y.den x.den,
                    Int.mul_assoc x.den y.den z.den]
        _ = (x.num * y.num * (x.den * z.den) + x.num * z.num * (x.den * y.den)) *
            (x.den * (y.den * z.den)) := by
              rw [Int.add_mul, Int.add_mul]
              congr 1
              · rw [Int.mul_assoc (x.num * y.num) z.den _,
                    Int.mul_assoc (x.num * y.num) (x.den * z.den) _,
                    ← Int.mul_assoc z.den x.den _,
                    Int.mul_comm z.den x.den,
                    Int.mul_assoc x.den z.den _]
              · rw [Int.mul_assoc (x.num * z.num) y.den _,
                    Int.mul_assoc (x.num * z.num) (x.den * y.den) _,
                    ← Int.mul_assoc y.den x.den _,
                    Int.mul_comm y.den x.den,
                    Int.mul_assoc x.den y.den _]))
  right_distrib := fun a b c =>
    Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound (by
      change RawQ.eqv (RawQ.mul (RawQ.add x y) z) (RawQ.add (RawQ.mul x z) (RawQ.mul y z))
      unfold RawQ.eqv RawQ.mul RawQ.add; dsimp only
      calc
        (x.num * y.den + y.num * x.den) * z.num * (x.den * z.den * (y.den * z.den))
          = ((x.num * y.den) * z.num + (y.num * x.den) * z.num) *
            ((x.den * y.den) * (z.den * z.den)) := by
              congr 1
              · rw [Int.add_mul]
              · rw [Int.mul_assoc x.den z.den (y.den * z.den),
                    ← Int.mul_assoc z.den y.den z.den,
                    Int.mul_comm z.den y.den,
                    Int.mul_assoc y.den z.den z.den,
                    ← Int.mul_assoc x.den y.den (z.den * z.den)]
        _ = ((x.num * y.den) * z.num) * ((x.den * y.den) * (z.den * z.den)) +
            ((y.num * x.den) * z.num) * ((x.den * y.den) * (z.den * z.den)) := by
              rw [Int.add_mul]
        _ = ((x.num * z.num) * (y.den * z.den)) * ((x.den * y.den) * z.den) +
            ((y.num * z.num) * (x.den * z.den)) * ((x.den * y.den) * z.den) := by
              congr 1
              · calc
                  ((x.num * y.den) * z.num) * ((x.den * y.den) * (z.den * z.den))
                    = ((x.num * z.num) * y.den) * ((x.den * y.den) * (z.den * z.den)) := by
                      rw [Int.mul_assoc x.num y.den z.num, Int.mul_comm y.den z.num,
                          ← Int.mul_assoc x.num z.num y.den]
                  _ = (x.num * z.num) * (y.den * ((x.den * y.den) * (z.den * z.den))) := by
                      rw [Int.mul_assoc]
                  _ = (x.num * z.num) * ((y.den * z.den) * ((x.den * y.den) * z.den)) := by
                      congr 1
                      rw [← Int.mul_assoc (x.den * y.den) z.den z.den,
                          Int.mul_comm (x.den * y.den) z.den,
                          Int.mul_assoc z.den (x.den * y.den) z.den,
                          ← Int.mul_assoc y.den z.den ((x.den * y.den) * z.den),
                          Int.mul_comm (x.den * y.den) z.den]
                  _ = ((x.num * z.num) * (y.den * z.den)) * ((x.den * y.den) * z.den) := by
                      rw [← Int.mul_assoc]
              · calc
                  ((y.num * x.den) * z.num) * ((x.den * y.den) * (z.den * z.den))
                    = ((y.num * z.num) * x.den) * ((x.den * y.den) * (z.den * z.den)) := by
                      rw [Int.mul_assoc y.num x.den z.num, Int.mul_comm x.den z.num,
                          ← Int.mul_assoc y.num z.num x.den]
                  _ = (y.num * z.num) * (x.den * ((x.den * y.den) * (z.den * z.den))) := by
                      rw [Int.mul_assoc]
                  _ = (y.num * z.num) * ((x.den * z.den) * ((x.den * y.den) * z.den)) := by
                      congr 1
                      rw [← Int.mul_assoc (x.den * y.den) z.den z.den,
                          Int.mul_comm (x.den * y.den) z.den,
                          Int.mul_assoc z.den (x.den * y.den) z.den,
                          ← Int.mul_assoc x.den z.den ((x.den * y.den) * z.den),
                          Int.mul_comm (x.den * y.den) z.den]
                  _ = ((y.num * z.num) * (x.den * z.den)) * ((x.den * y.den) * z.den) := by
                      rw [← Int.mul_assoc]
        _ = (x.num * z.num * (y.den * z.den) + y.num * z.num * (x.den * z.den)) *
            (x.den * y.den * z.den) := by
              rw [← Int.add_mul]))
  zero_ne_one := by
    intro h
    have heqv : RawQ.eqv RawQ.zero RawQ.one := Quotient.exact h
    unfold RawQ.eqv RawQ.zero RawQ.one at heqv
    dsimp only at heqv
    omega
  mul_inv_cancel := fun a ha =>
    Quotient.inductionOn a (fun x hx => Quotient.sound (by
      change RawQ.eqv (RawQ.mul x (RawQ.inv x)) RawQ.one
      unfold RawQ.inv
      by_cases hp : 0 < x.num
      · rw [dif_pos hp]
        unfold RawQ.eqv RawQ.mul RawQ.one; dsimp only
        rw [Int.mul_one, Int.one_mul, Int.mul_comm]
      · rw [dif_neg hp]
        by_cases hn : x.num < 0
        · rw [dif_pos hn]
          unfold RawQ.eqv RawQ.mul RawQ.one; dsimp only
          rw [Int.mul_one, Int.one_mul, Int.mul_neg, Int.mul_neg, Int.mul_comm]
        · exfalso
          apply hx
          apply Quotient.sound
          change RawQ.eqv x RawQ.zero
          unfold RawQ.eqv RawQ.zero; dsimp only
          have hz : x.num = 0 := by omega
          rw [hz, Int.zero_mul, Int.zero_mul])) ha
  inv_zero := Quotient.sound (by
    change RawQ.eqv (RawQ.inv RawQ.zero) RawQ.zero
    unfold RawQ.inv RawQ.zero
    dsimp only
    rw [dif_neg (by decide), dif_neg (by decide)]
    rfl)
  div_eq_mul_inv := fun _ _ => rfl
  le_refl := fun a =>
    Quotient.inductionOn a (fun x => Int.le_refl (x.num * x.den))
  le_trans := fun {a b c} =>
    Quotient.inductionOn₃ a b c (fun x y z hxy hyz => by
      change RawQ.le x y at hxy
      change RawQ.le y z at hyz
      change RawQ.le x z
      unfold RawQ.le at *
      have hx := x.den_pos
      have hy := y.den_pos
      have hz := z.den_pos
      have h1 := Int.mul_le_mul_of_nonneg_right hxy (by omega : 0 ≤ z.den)
      have h2 := Int.mul_le_mul_of_nonneg_right hyz (by omega : 0 ≤ x.den)
      have h3 : x.num * z.den * y.den ≤ z.num * x.den * y.den := by
        calc
          x.num * z.den * y.den = x.num * y.den * z.den := by
            rw [Int.mul_assoc, Int.mul_comm z.den y.den, ← Int.mul_assoc]
          _ ≤ y.num * x.den * z.den := h1
          _ = y.num * z.den * x.den := by
            rw [Int.mul_assoc, Int.mul_comm x.den z.den, ← Int.mul_assoc]
          _ ≤ z.num * y.den * x.den := h2
          _ = z.num * x.den * y.den := by
            rw [Int.mul_assoc, Int.mul_comm y.den x.den, ← Int.mul_assoc]
      by_cases hgoal : x.num * z.den ≤ z.num * x.den
      · exact hgoal
      · have hgt : z.num * x.den + 1 ≤ x.num * z.den := by omega
        have hm := Int.mul_le_mul_of_nonneg_right hgt (by omega : 0 ≤ y.den)
        rw [Int.add_mul, Int.one_mul] at hm
        omega)
  le_antisymm := fun {a b} =>
    Quotient.inductionOn₂ a b (fun x y hab hba => Quotient.sound (by
      change RawQ.le x y at hab
      change RawQ.le y x at hba
      change RawQ.eqv x y
      unfold RawQ.le RawQ.eqv at *
      omega))
  le_total := fun a b =>
    Quotient.inductionOn₂ a b (fun x y => Int.le_total (x.num * y.den) (y.num * x.den))
  lt_iff_le_not_le := fun _ _ => Iff.rfl
  add_le_add_left := fun {a b} hab c =>
    Quotient.inductionOn₃ a b c (fun x y z (hxy : RawQ.le x y) => by
      change RawQ.le (RawQ.add z x) (RawQ.add z y)
      unfold RawQ.le RawQ.add at *
      dsimp only
      have hz := z.den_pos
      have hz2p : 0 < z.den * z.den := Int.mul_pos hz hz
      have hm := Int.mul_le_mul_of_nonneg_right hxy (by omega : 0 ≤ z.den * z.den)
      have hleft :
          (z.num * x.den + x.num * z.den) * (z.den * y.den) =
          z.num * z.den * (x.den * y.den) + (x.num * y.den) * (z.den * z.den) := by
        rw [Int.add_mul]
        congr 1
        · rw [Int.mul_assoc z.num x.den (z.den * y.den),
              ← Int.mul_assoc x.den z.den y.den,
              Int.mul_comm x.den z.den,
              Int.mul_assoc z.den x.den y.den,
              ← Int.mul_assoc z.num z.den (x.den * y.den)]
        · rw [Int.mul_assoc x.num z.den (z.den * y.den),
              ← Int.mul_assoc z.den z.den y.den,
              Int.mul_comm (z.den * z.den) y.den,
              ← Int.mul_assoc x.num y.den (z.den * z.den)]
      have hright :
          (z.num * y.den + y.num * z.den) * (z.den * x.den) =
          z.num * z.den * (x.den * y.den) + (y.num * x.den) * (z.den * z.den) := by
        rw [Int.add_mul]
        congr 1
        · rw [Int.mul_assoc z.num y.den (z.den * x.den),
              ← Int.mul_assoc y.den z.den x.den,
              Int.mul_comm y.den z.den,
              Int.mul_assoc z.den y.den x.den,
              Int.mul_comm y.den x.den,
              ← Int.mul_assoc z.num z.den (x.den * y.den)]
        · rw [Int.mul_assoc y.num z.den (z.den * x.den),
              ← Int.mul_assoc z.den z.den x.den,
              Int.mul_comm (z.den * z.den) x.den,
              ← Int.mul_assoc y.num x.den (z.den * z.den)]
      rw [hleft, hright]
      omega) hab
  mul_pos := fun {a b} =>
    Quotient.inductionOn₂ a b (fun x y hx hy => by
      have hx' : RawQ.lt RawQ.zero x := (RawQ.lt_iff_le_not_le_raw RawQ.zero x).mpr hx
      have hy' : RawQ.lt RawQ.zero y := (RawQ.lt_iff_le_not_le_raw RawQ.zero y).mpr hy
      unfold RawQ.lt RawQ.zero at hx' hy'
      dsimp only at hx' hy'
      have hxn : 0 < x.num := by omega
      have hyn : 0 < y.num := by omega
      apply (RawQ.lt_iff_le_not_le_raw RawQ.zero (RawQ.mul x y)).mp
      unfold RawQ.lt RawQ.zero RawQ.mul
      dsimp only
      rw [Int.zero_mul, Int.mul_one]
      exact Int.mul_pos hxn hyn)
  zero_lt_one := by
    apply (RawQ.lt_iff_le_not_le_raw RawQ.zero RawQ.one).mp
    unfold RawQ.lt RawQ.zero RawQ.one
    decide

end Q

end Conjecture00000007179
