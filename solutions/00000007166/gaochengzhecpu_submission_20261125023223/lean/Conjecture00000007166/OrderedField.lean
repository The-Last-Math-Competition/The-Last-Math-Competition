/-
Copyright (c) 2026. All rights reserved.
Formalization of Conjecture 00000007166 in Core Lean 4.19.0 (zero external dependencies).

Module: Conjecture00000007166.OrderedField
Purpose:
  1. Self-contained axiomatization of a linearly ordered field (`LinearOrderedField F`),
     covering both the rationals Q and the reals R (and every ordered field), together
     with complete algebraic and inequality lemmas from first principles.
  2. Explicit constructive instantiation `instance : LinearOrderedField Q` on exact
     rationals `Q` built as a quotient of `Int × {d : Int // 0 < d}`, guaranteeing
     non-vacuity of all field hypotheses within Core Lean 4.19.0.
-/

namespace Conjecture00000007166

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

theorem sub_zero (a : F) : a - 0 = a := by
  have h0 : -(0 : F) = 0 := by
    apply add_left_cancel (a := (0 : F))
    rw [add_neg_cancel, lofAddZero]
  rw [lofSubEqAddNeg, h0, lofAddZero]

theorem neg_zero : -(0 : F) = 0 := by
  apply add_left_cancel (a := (0 : F))
  rw [add_neg_cancel, lofAddZero]

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

theorem mul_sub (a b c : F) : a * (b - c) = a * b - a * c := by
  rw [lofSubEqAddNeg, lofLeftDistrib, mul_neg, ← lofSubEqAddNeg]

theorem sub_mul (a b c : F) : (a - b) * c = a * c - b * c := by
  rw [lofSubEqAddNeg, lofRightDistrib, neg_mul, ← lofSubEqAddNeg]

theorem sub_sub (a b c : F) : a - b - c = a - (b + c) := by
  rw [lofSubEqAddNeg, lofSubEqAddNeg, lofSubEqAddNeg, neg_add_rev, lofAddAssoc]

theorem sub_sub_eq_add_sub (a b c : F) : a - (b - c) = a + c - b := by
  rw [lofSubEqAddNeg, lofSubEqAddNeg, neg_add_rev, neg_neg,
      lofAddComm (-b) c, ← lofAddAssoc a c (-b), ← lofSubEqAddNeg]

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
  have h1 : (1 : F)⁻¹ = 1 := by
    apply mul_left_cancel (Ne.symm LinearOrderedField.zero_ne_one)
    rw [lofMulInvCancel (Ne.symm LinearOrderedField.zero_ne_one), lofMulOne]
  rw [lofDivEqMulInv, h1, lofMulOne]

theorem zero_div (a : F) : 0 / a = 0 := by
  rw [lofDivEqMulInv, zero_mul]

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

theorem inv_div {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : (a / b)⁻¹ = b / a := by
  rw [lofDivEqMulInv, lofDivEqMulInv, inv_mul_distrib ha (inv_ne_zero hb), inv_inv, lofMulComm]

theorem div_div_div_eq (a b c d : F) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    (a / b) / (c / d) = (a * d) / (b * c) := by
  rw [lofDivEqMulInv (a / b) (c / d), inv_div hc hd, div_mul_div a b d c hb hc]

theorem div_eq_iff {a b c : F} (hb : b ≠ 0) : a / b = c ↔ a = c * b := by
  constructor
  · intro h
    rw [← h, div_mul_cancel a hb]
  · intro h
    rw [h, mul_div_cancel_right c hb]

theorem eq_div_iff {a b c : F} (hc : c ≠ 0) : a = b / c ↔ a * c = b := by
  constructor
  · intro h
    rw [h, div_mul_cancel b hc]
  · intro h
    rw [← h, mul_div_cancel_right a hc]

theorem div_eq_div_iff {a b c d : F} (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b = c / d ↔ a * d = c * b := by
  rw [div_eq_iff hb, div_mul_eq_mul_div, eq_div_iff hd]

/-! ### Order Lemmas -/

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

theorem lt_of_not_ge {a b : F} (h : ¬ b ≤ a) : a < b := by
  rcases LinearOrderedField.le_total a b with hab | hba
  · exact (LinearOrderedField.lt_iff_le_not_le a b).mpr ⟨hab, h⟩
  · exact False.elim (h hba)

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

theorem add_lt_add_of_le_of_lt {a b c d : F} (hab : a ≤ b) (hcd : c < d) : a + c < b + d :=
  lt_of_le_of_lt (add_le_add_right hab c) (add_lt_add_left hcd b)

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

theorem mul_lt_mul_of_pos_left {a b c : F} (hab : a < b) (hc : 0 < c) :
    c * a < c * b := by
  rw [← sub_pos, ← mul_sub]
  exact LinearOrderedField.mul_pos hc (sub_pos.mpr hab)

theorem mul_lt_mul_of_pos_right {a b c : F} (hab : a < b) (hc : 0 < c) :
    a * c < b * c := by
  rw [lofMulComm a c, lofMulComm b c]
  exact mul_lt_mul_of_pos_left hab hc

theorem le_of_mul_le_mul_left {a b c : F} (hc : 0 < c) (h : c * a ≤ c * b) : a ≤ b := by
  rcases LinearOrderedField.le_total a b with hab | hba
  · exact hab
  · by_cases heq : a = b
    · rw [heq]
      exact LinearOrderedField.le_refl b
    · have hlt : b < a := lt_of_le_of_ne hba (Ne.symm heq)
      exact False.elim (not_le_of_lt (mul_lt_mul_of_pos_left hlt hc) h)

theorem sq_nonneg (a : F) : 0 ≤ a * a := by
  rcases LinearOrderedField.le_total 0 a with ha | ha
  · exact mul_nonneg ha ha
  · rw [← neg_mul_neg]
    exact mul_nonneg (neg_nonneg.mpr ha) (neg_nonneg.mpr ha)

theorem sq_pos_of_ne_zero {a : F} (ha : a ≠ 0) : 0 < a * a :=
  lt_of_le_of_ne (sq_nonneg a) (Ne.symm (mul_ne_zero ha ha))

theorem sq_eq_zero_iff {a : F} : a * a = 0 ↔ a = 0 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with ha | ha <;> exact ha
  · intro h
    rw [h, zero_mul]

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

theorem div_pos {a b : F} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [lofDivEqMulInv]
  exact LinearOrderedField.mul_pos ha (inv_pos_of_pos hb)

theorem div_nonneg {a b : F} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by
  rw [lofDivEqMulInv]
  exact mul_nonneg ha (inv_nonneg_of_nonneg hb)

theorem le_div_iff_of_pos {a b c : F} (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := by
  constructor
  · intro h
    have h1 := mul_le_mul_of_nonneg_right h (le_of_lt hc)
    rw [div_mul_cancel b (ne_of_gt hc)] at h1
    exact h1
  · intro h
    have h1 := mul_le_mul_of_nonneg_right h (le_of_lt (inv_pos_of_pos hc))
    rw [lofMulAssoc, lofMulInvCancel (ne_of_gt hc), lofMulOne, ← lofDivEqMulInv] at h1
    exact h1

theorem div_le_iff_of_pos {a b c : F} (hb : 0 < b) : a / b ≤ c ↔ a ≤ c * b := by
  constructor
  · intro h
    have h1 := mul_le_mul_of_nonneg_right h (le_of_lt hb)
    rw [div_mul_cancel a (ne_of_gt hb)] at h1
    exact h1
  · intro h
    have h1 := mul_le_mul_of_nonneg_right h (le_of_lt (inv_pos_of_pos hb))
    rw [← lofDivEqMulInv, lofMulAssoc, lofMulInvCancel (ne_of_gt hb), lofMulOne] at h1
    exact h1

theorem div_lt_iff_of_pos {a b c : F} (hb : 0 < b) : a / b < c ↔ a < c * b := by
  constructor
  · intro h
    have h1 := mul_lt_mul_of_pos_right h hb
    rw [div_mul_cancel a (ne_of_gt hb)] at h1
    exact h1
  · intro h
    have h1 := mul_lt_mul_of_pos_right h (inv_pos_of_pos hb)
    rw [← lofDivEqMulInv, lofMulAssoc, lofMulInvCancel (ne_of_gt hb), lofMulOne] at h1
    exact h1

theorem lt_div_iff_of_pos {a b c : F} (hc : 0 < c) : a < b / c ↔ a * c < b := by
  constructor
  · intro h
    have h1 := mul_lt_mul_of_pos_right h hc
    rw [div_mul_cancel b (ne_of_gt hc)] at h1
    exact h1
  · intro h
    have h1 := mul_lt_mul_of_pos_right h (inv_pos_of_pos hc)
    rw [lofMulAssoc, lofMulInvCancel (ne_of_gt hc), lofMulOne, ← lofDivEqMulInv] at h1
    exact h1

theorem div_lt_div_iff_of_pos {a b c d : F} (hb : 0 < b) (hd : 0 < d) :
    a / b < c / d ↔ a * d < c * b := by
  rw [div_lt_iff_of_pos hb, div_mul_eq_mul_div, lt_div_iff_of_pos hd]

theorem inv_lt_inv_of_pos {a b : F} (ha : 0 < a) (hab : a < b) : b⁻¹ < a⁻¹ := by
  have hb : 0 < b := lt_trans ha hab
  have h1 : b⁻¹ * a < b⁻¹ * b := mul_lt_mul_of_pos_left hab (inv_pos_of_pos hb)
  rw [inv_mul_cancel (ne_of_gt hb)] at h1
  have h2 : (b⁻¹ * a) * a⁻¹ < 1 * a⁻¹ := mul_lt_mul_of_pos_right h1 (inv_pos_of_pos ha)
  rw [lofMulAssoc, lofMulInvCancel (ne_of_gt ha), lofMulOne, lofOneMul] at h2
  exact h2

/-- Small canonical positive numerals `2, 3, 4` in any `LinearOrderedField F`. -/
def twoF : F := (1 : F) + 1
def threeF : F := twoF + 1
def fourF : F := twoF + twoF

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

theorem twoF_ne_zero : (twoF : F) ≠ 0 := ne_of_gt twoF_pos
theorem threeF_ne_zero : (threeF : F) ≠ 0 := ne_of_gt threeF_pos
theorem fourF_ne_zero : (fourF : F) ≠ 0 := ne_of_gt fourF_pos

theorem twoF_mul (a : F) : (twoF : F) * a = a + a := by
  unfold twoF
  rw [lofRightDistrib, lofOneMul]

theorem fourF_eq_two_mul_two : (fourF : F) = twoF * twoF := by
  unfold fourF
  rw [twoF_mul]

end OrderedFieldLemmas

/-!
### Constructive Exact Rational Field `Q`
We construct `Q` from Core Lean `Int` via positive-denominator fractions and prove
`instance : LinearOrderedField Q` so that all ordered-field theorems are constructively
inhabited and specialize unconditionally to exact rationals.
-/

/-- Unreduced fraction `num / den` with `0 < den`. -/
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

end Conjecture00000007166
