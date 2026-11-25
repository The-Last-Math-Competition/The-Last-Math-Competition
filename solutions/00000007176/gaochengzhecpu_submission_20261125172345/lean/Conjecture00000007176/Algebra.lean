/-
Copyright (c) 2026 The Last Math Competition Contributors. All rights reserved.
Self-contained algebraic hierarchy in Core Lean 4.19.0 (zero external dependencies)
for Conjecture 00000007176: commutative rings, integral domains, linearly ordered
domains, complexification `ComplexOver R`, Pascal/Vandermonde binomial combinatorics,
and concrete `Int` and `RatField` (`ℚ`) instances.
-/

namespace Conjecture00000007176

/-- A commutative unital ring equipped with standard arithmetic operations. -/
class CommRing (R : Type u) extends Add R, Mul R, Neg R, Sub R where
  zero : R
  one : R
  add_assoc : ∀ a b c : R, a + b + c = a + (b + c)
  add_comm : ∀ a b : R, a + b = b + a
  zero_add : ∀ a : R, zero + a = a
  add_zero : ∀ a : R, a + zero = a
  neg_add_cancel : ∀ a : R, -a + a = zero
  sub_eq_add_neg : ∀ a b : R, a - b = a + -b
  mul_assoc : ∀ a b c : R, a * b * c = a * (b * c)
  mul_comm : ∀ a b : R, a * b = b * a
  one_mul : ∀ a : R, one * a = a
  mul_one : ∀ a : R, a * one = a
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

instance (priority := 100) [CommRing R] : OfNat R 0 := ⟨CommRing.zero⟩
instance (priority := 100) [CommRing R] : OfNat R 1 := ⟨CommRing.one⟩

@[simp] theorem CommRing.ofNat_zero [CommRing R] : (0 : R) = CommRing.zero := rfl
@[simp] theorem CommRing.ofNat_one [CommRing R] : (1 : R) = CommRing.one := rfl

/-- An integral domain: nontrivial commutative ring with no zero divisors. -/
class IntegralDomain (R : Type u) extends CommRing R where
  zero_ne_one : (0 : R) ≠ 1
  mul_eq_zero : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0

/-- A linearly ordered integral domain specified via its non-negative cone `NonNeg`.
    Simultaneously abstracts `ℤ`, `ℚ`, real algebraic fields, and `ℝ`. -/
class OrderedDomain (R : Type u) extends IntegralDomain R where
  NonNeg : R → Prop
  nonneg_zero : NonNeg 0
  nonneg_one : NonNeg 1
  nonneg_add : ∀ {a b : R}, NonNeg a → NonNeg b → NonNeg (a + b)
  nonneg_mul : ∀ {a b : R}, NonNeg a → NonNeg b → NonNeg (a * b)
  nonneg_antisymm : ∀ {a : R}, NonNeg a → NonNeg (-a) → a = 0
  nonneg_total : ∀ a : R, NonNeg a ∨ NonNeg (-a)

/-! ### Basic Commutative Ring & Power Lemmas -/

section CommRingLemmas

variable {R : Type u} [CommRing R]

theorem zero_add_eq (a : R) : 0 + a = a := CommRing.zero_add a
theorem add_zero_eq (a : R) : a + 0 = a := CommRing.add_zero a
theorem neg_add_cancel_eq (a : R) : -a + a = 0 := CommRing.neg_add_cancel a
theorem one_mul_eq (a : R) : 1 * a = a := CommRing.one_mul a
theorem mul_one_eq (a : R) : a * 1 = a := CommRing.mul_one a

theorem add_neg_cancel (a : R) : a + -a = 0 := by
  rw [CommRing.add_comm, neg_add_cancel_eq]

theorem add_left_comm_eq (a b c : R) : a + (b + c) = b + (a + c) := by
  rw [← CommRing.add_assoc, CommRing.add_comm a b, CommRing.add_assoc]

theorem add_right_comm_eq (a b c : R) : a + b + c = a + c + b := by
  rw [CommRing.add_assoc, CommRing.add_comm b c, ← CommRing.add_assoc]

theorem mul_left_comm_eq (a b c : R) : a * (b * c) = b * (a * c) := by
  rw [← CommRing.mul_assoc, CommRing.mul_comm a b, CommRing.mul_assoc]

theorem mul_right_comm_eq (a b c : R) : a * b * c = a * c * b := by
  rw [CommRing.mul_assoc, CommRing.mul_comm b c, ← CommRing.mul_assoc]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  have h1 : -a + (a + b) = -a + (a + c) := congrArg (fun x => -a + x) h
  rw [← CommRing.add_assoc, ← CommRing.add_assoc, neg_add_cancel_eq,
      zero_add_eq, zero_add_eq] at h1
  exact h1

theorem add_right_cancel {a b c : R} (h : b + a = c + a) : b = c := by
  apply add_left_cancel (a := a)
  rw [CommRing.add_comm a b, CommRing.add_comm a c]
  exact h

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  apply add_left_cancel (a := a)
  rw [add_neg_cancel, h]

theorem neg_zero_eq : -(0 : R) = 0 :=
  neg_eq_of_add_eq_zero (zero_add_eq 0)

theorem neg_neg_eq (a : R) : -(-a) = a :=
  neg_eq_of_add_eq_zero (neg_add_cancel_eq a)

theorem neg_add_distrib (a b : R) : -(a + b) = -a + -b := by
  apply neg_eq_of_add_eq_zero
  calc
    (a + b) + (-a + -b) = a + (b + (-a + -b)) := CommRing.add_assoc a b (-a + -b)
    _ = a + (-a + (b + -b)) := by rw [add_left_comm_eq b (-a) (-b)]
    _ = a + (-a + 0) := by rw [add_neg_cancel]
    _ = a + -a := by rw [add_zero_eq]
    _ = 0 := add_neg_cancel a

theorem neg_sub_eq (a b : R) : -(a - b) = b - a := by
  rw [CommRing.sub_eq_add_neg, neg_add_distrib, neg_neg_eq, CommRing.add_comm,
      ← CommRing.sub_eq_add_neg]

theorem sub_self_eq_zero (a : R) : a - a = 0 := by
  rw [CommRing.sub_eq_add_neg, add_neg_cancel]

theorem sub_zero_eq (a : R) : a - 0 = a := by
  rw [CommRing.sub_eq_add_neg, neg_zero_eq, add_zero_eq]

theorem zero_sub_eq (a : R) : 0 - a = -a := by
  rw [CommRing.sub_eq_add_neg, zero_add_eq]

theorem sub_eq_zero_iff {a b : R} : a - b = 0 ↔ a = b := by
  constructor
  · intro h
    apply add_right_cancel (a := -b)
    rw [← CommRing.sub_eq_add_neg, h, add_neg_cancel]
  · intro h
    rw [h, sub_self_eq_zero]

theorem mul_zero_eq (a : R) : a * 0 = 0 := by
  apply add_left_cancel (a := a * 0)
  calc
    a * 0 + a * 0 = a * (0 + 0) := (CommRing.left_distrib a 0 0).symm
    _ = a * 0 := by rw [add_zero_eq]
    _ = a * 0 + 0 := (add_zero_eq (a * 0)).symm

theorem zero_mul_eq (a : R) : 0 * a = 0 := by
  rw [CommRing.mul_comm, mul_zero_eq]

theorem mul_neg_eq (a b : R) : a * (-b) = -(a * b) := by
  symm
  apply neg_eq_of_add_eq_zero
  calc
    a * b + a * (-b) = a * (b + -b) := (CommRing.left_distrib a b (-b)).symm
    _ = a * 0 := by rw [add_neg_cancel]
    _ = 0 := mul_zero_eq a

theorem neg_mul_eq (a b : R) : (-a) * b = -(a * b) := by
  rw [CommRing.mul_comm, mul_neg_eq, CommRing.mul_comm]

theorem neg_mul_neg (a b : R) : (-a) * (-b) = a * b := by
  rw [neg_mul_eq, mul_neg_eq, neg_neg_eq]

theorem mul_sub_distrib (a b c : R) : a * (b - c) = a * b - a * c := by
  rw [CommRing.sub_eq_add_neg, CommRing.left_distrib, mul_neg_eq, ← CommRing.sub_eq_add_neg]

theorem sub_mul_distrib (a b c : R) : (a - b) * c = a * c - b * c := by
  rw [CommRing.sub_eq_add_neg, CommRing.right_distrib, neg_mul_eq, ← CommRing.sub_eq_add_neg]

theorem diff_sq_eq (a b : R) : (a - b) * (a + b) = a * a - b * b := by
  calc
    (a - b) * (a + b) = (a - b) * a + (a - b) * b := CommRing.left_distrib _ a b
    _ = (a * a - b * a) + (a * b - b * b) := by rw [sub_mul_distrib, sub_mul_distrib]
    _ = (a * a + -(a * b)) + (a * b + -(b * b)) := by
        rw [CommRing.mul_comm b a, CommRing.sub_eq_add_neg, CommRing.sub_eq_add_neg]
    _ = a * a + (-(a * b) + (a * b + -(b * b))) := CommRing.add_assoc _ _ _
    _ = a * a + ((-(a * b) + a * b) + -(b * b)) := by rw [← CommRing.add_assoc (-(a * b))]
    _ = a * a + (0 + -(b * b)) := by rw [neg_add_cancel_eq]
    _ = a * a - b * b := by rw [zero_add_eq, ← CommRing.sub_eq_add_neg]

theorem sub_sq_eq (a b : R) : (a - b) * (a - b) = a * a + b * b - (a * b + a * b) := by
  calc
    (a - b) * (a - b) = (a - b) * a - (a - b) * b := mul_sub_distrib _ a b
    _ = (a * a - b * a) - (a * b - b * b) := by rw [sub_mul_distrib, sub_mul_distrib]
    _ = (a * a + -(a * b)) + (-(a * b) + b * b) := by
        rw [CommRing.mul_comm b a, CommRing.sub_eq_add_neg, CommRing.sub_eq_add_neg,
            CommRing.sub_eq_add_neg, neg_add_distrib, neg_neg_eq]
    _ = a * a + (-(a * b) + (b * b + -(a * b))) := by
        rw [CommRing.add_comm (-(a * b)) (b * b), CommRing.add_assoc]
    _ = a * a + (b * b + (-(a * b) + -(a * b))) := by
        rw [add_left_comm_eq (-(a * b)) (b * b) (-(a * b))]
    _ = (a * a + b * b) + -(a * b + a * b) := by
        rw [← neg_add_distrib, ← CommRing.add_assoc]
    _ = a * a + b * b - (a * b + a * b) := by rw [← CommRing.sub_eq_add_neg]

/-- Monoid power in any commutative unital ring. -/
def rpow (x : R) : Nat → R
  | 0 => 1
  | k + 1 => rpow x k * x

@[simp] theorem rpow_zero (x : R) : rpow x 0 = 1 := rfl
@[simp] theorem rpow_succ (x : R) (k : Nat) : rpow x (k + 1) = rpow x k * x := rfl

theorem rpow_one (x : R) : rpow x 1 = x := one_mul_eq x

theorem rpow_two (x : R) : rpow x 2 = x * x := by
  change (1 * x) * x = x * x
  rw [one_mul_eq]

theorem rpow_one_base : ∀ k : Nat, rpow (1 : R) k = 1
  | 0 => rfl
  | k + 1 => by rw [rpow_succ, rpow_one_base k, mul_one_eq]

theorem rpow_zero_base : ∀ {k : Nat}, k ≥ 1 → rpow (0 : R) k = 0
  | 0, hk => by omega
  | k + 1, _ => by rw [rpow_succ, mul_zero_eq]

theorem rpow_add (x : R) (m : Nat) : ∀ n : Nat, rpow x (m + n) = rpow x m * rpow x n
  | 0 => (mul_one_eq (rpow x m)).symm
  | n + 1 => by rw [Nat.add_succ, rpow_succ, rpow_succ, rpow_add x m n, CommRing.mul_assoc]

theorem rpow_mul_distrib (x y : R) : ∀ k : Nat, rpow (x * y) k = rpow x k * rpow y k
  | 0 => (mul_one_eq 1).symm
  | k + 1 => by
    rw [rpow_succ, rpow_succ, rpow_succ, rpow_mul_distrib x y k]
    calc
      rpow x k * rpow y k * (x * y) = rpow x k * (rpow y k * (x * y)) := CommRing.mul_assoc _ _ _
      _ = rpow x k * (x * (rpow y k * y)) := by rw [mul_left_comm_eq (rpow y k) x y]
      _ = (rpow x k * x) * (rpow y k * y) := (CommRing.mul_assoc _ _ _).symm

theorem rpow_mul_exp (x : R) (a : Nat) : ∀ b : Nat, rpow x (a * b) = rpow (rpow x a) b
  | 0 => rfl
  | b + 1 => by rw [Nat.mul_succ, rpow_add, rpow_succ, rpow_mul_exp x a b]

theorem rpow_neg_even (x : R) : ∀ k : Nat, rpow (-x) (2 * k) = rpow x (2 * k)
  | 0 => rfl
  | k + 1 => by
    have hstep : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [hstep, rpow_add, rpow_add, rpow_neg_even x k, rpow_two, rpow_two, neg_mul_neg]

theorem rpow_neg_odd (x : R) (k : Nat) : rpow (-x) (2 * k + 1) = -(rpow x (2 * k + 1)) := by
  rw [rpow_succ, rpow_neg_even, mul_neg_eq, ← rpow_succ]

/-- Canonical natural-number embedding `Nat → R`. -/
def natCastR : Nat → R
  | 0 => 0
  | n + 1 => natCastR n + 1

@[simp] theorem natCastR_zero : (natCastR 0 : R) = 0 := rfl
@[simp] theorem natCastR_succ (n : Nat) : (natCastR (n + 1) : R) = natCastR n + 1 := rfl

theorem natCastR_one : (natCastR 1 : R) = 1 := zero_add_eq 1

theorem natCastR_two : (natCastR 2 : R) = 1 + 1 := by
  rw [natCastR_succ, natCastR_one]

theorem natCastR_add (m : Nat) : ∀ n : Nat, (natCastR (m + n) : R) = natCastR m + natCastR n
  | 0 => (add_zero_eq _).symm
  | n + 1 => by rw [Nat.add_succ, natCastR_succ, natCastR_succ, natCastR_add m n, CommRing.add_assoc]

theorem natCastR_mul (m : Nat) : ∀ n : Nat, (natCastR (m * n) : R) = natCastR m * natCastR n
  | 0 => (mul_zero_eq _).symm
  | n + 1 => by
    rw [Nat.mul_succ, natCastR_add, natCastR_succ, natCastR_mul m n,
        CommRing.left_distrib, mul_one_eq]

theorem natCastR_pow (m : Nat) : ∀ k : Nat, (natCastR (m ^ k) : R) = rpow (natCastR m) k
  | 0 => natCastR_one
  | k + 1 => by rw [Nat.pow_succ, natCastR_mul, rpow_succ, natCastR_pow m k]

end CommRingLemmas

/-! ### Integral Domain & Linearly Ordered Domain Lemmas -/

section OrderedDomainLemmas

variable {R : Type u} [OrderedDomain R]

/-- `leR a b` means `0 ≤ b - a` in `R`. -/
def leR (a b : R) : Prop := OrderedDomain.NonNeg (b - a)

/-- `ltR a b` means `a ≤ b` and `a ≠ b` in `R`. -/
def ltR (a b : R) : Prop := leR a b ∧ a ≠ b

/-- Classical absolute value `|a|` in `R`. -/
noncomputable def absR (a : R) : R :=
  haveI := Classical.propDecidable (OrderedDomain.NonNeg a)
  if OrderedDomain.NonNeg a then a else -a

theorem nonneg_iff_leR (a : R) : OrderedDomain.NonNeg a ↔ leR 0 a := by
  unfold leR
  rw [sub_zero_eq]

theorem leR_refl (a : R) : leR a a := by
  unfold leR
  rw [sub_self_eq_zero]
  exact OrderedDomain.nonneg_zero

theorem leR_antisymm {a b : R} (hab : leR a b) (hba : leR b a) : a = b := by
  unfold leR at hab hba
  have hneg : OrderedDomain.NonNeg (-(b - a)) := by
    rw [neg_sub_eq]
    exact hba
  have h0 : b - a = 0 := OrderedDomain.nonneg_antisymm hab hneg
  exact (sub_eq_zero_iff.mp h0).symm

theorem leR_trans {a b c : R} (hab : leR a b) (hbc : leR b c) : leR a c := by
  unfold leR at *
  have hsum : (c - b) + (b - a) = c - a := by
    calc
      (c - b) + (b - a) = c + (-b + (b + -a)) := by
        rw [CommRing.sub_eq_add_neg, CommRing.sub_eq_add_neg, CommRing.add_assoc]
      _ = c + ((-b + b) + -a) := by rw [← CommRing.add_assoc (-b) b (-a)]
      _ = c - a := by rw [neg_add_cancel_eq, zero_add_eq, ← CommRing.sub_eq_add_neg]
  rw [← hsum]
  exact OrderedDomain.nonneg_add hbc hab

theorem leR_total (a b : R) : leR a b ∨ leR b a := by
  cases OrderedDomain.nonneg_total (b - a) with
  | inl h => exact Or.inl h
  | inr h =>
    rw [neg_sub_eq] at h
    exact Or.inr h

theorem ltR_irrefl (a : R) : ¬ ltR a a := fun ⟨_, hne⟩ => hne rfl

theorem not_leR_of_ltR {a b : R} (h : ltR a b) : ¬ leR b a := by
  intro hba
  exact h.2 (leR_antisymm h.1 hba)

theorem ltR_of_not_leR {a b : R} (h : ¬ leR b a) : ltR a b := by
  cases leR_total a b with
  | inl hab =>
    refine ⟨hab, ?_⟩
    intro heq
    subst heq
    exact h (leR_refl a)
  | inr hba => exact False.elim (h hba)

theorem ltR_of_ltR_of_leR {a b c : R} (hab : ltR a b) (hbc : leR b c) : ltR a c := by
  refine ⟨leR_trans hab.1 hbc, ?_⟩
  intro hac
  subst hac
  exact hab.2 (leR_antisymm hab.1 hbc)

theorem ltR_of_leR_of_ltR {a b c : R} (hab : leR a b) (hbc : ltR b c) : ltR a c := by
  refine ⟨leR_trans hab hbc.1, ?_⟩
  intro hac
  subst hac
  exact hbc.2 (leR_antisymm hbc.1 hab)

theorem ltR_trans {a b c : R} (hab : ltR a b) (hbc : ltR b c) : ltR a c :=
  ltR_of_ltR_of_leR hab hbc.1

theorem zero_ltR_one : ltR (0 : R) 1 := by
  refine ⟨?_, IntegralDomain.zero_ne_one⟩
  rw [← nonneg_iff_leR]
  exact OrderedDomain.nonneg_one

theorem sq_nonneg (a : R) : leR 0 (a * a) := by
  rw [← nonneg_iff_leR]
  cases OrderedDomain.nonneg_total a with
  | inl ha => exact OrderedDomain.nonneg_mul ha ha
  | inr hna =>
    rw [← neg_mul_neg a a]
    exact OrderedDomain.nonneg_mul hna hna

theorem sq_eq_zero_iff (a : R) : a * a = 0 ↔ a = 0 := by
  constructor
  · intro h
    cases IntegralDomain.mul_eq_zero a a h with
    | inl h1 => exact h1
    | inr h2 => exact h2
  · intro h
    rw [h, mul_zero_eq]

theorem sq_pos_of_ne_zero {a : R} (ha : a ≠ 0) : ltR 0 (a * a) := by
  refine ⟨sq_nonneg a, ?_⟩
  intro h0
  exact ha ((sq_eq_zero_iff a).mp h0.symm)

theorem add_leR_add {a b c d : R} (hab : leR a b) (hcd : leR c d) : leR (a + c) (b + d) := by
  unfold leR at *
  have heq : (b + d) - (a + c) = (b - a) + (d - c) := by
    calc
      (b + d) - (a + c) = (b + d) + (-a + -c) := by
        rw [CommRing.sub_eq_add_neg, neg_add_distrib]
      _ = b + (d + (-a + -c)) := CommRing.add_assoc _ _ _
      _ = b + (-a + (d + -c)) := by rw [add_left_comm_eq d (-a) (-c)]
      _ = (b - a) + (d - c) := by
        rw [← CommRing.add_assoc, ← CommRing.sub_eq_add_neg, ← CommRing.sub_eq_add_neg]
  rw [heq]
  exact OrderedDomain.nonneg_add hab hcd

theorem add_ltR_add_of_ltR_of_leR {a b c d : R} (hab : ltR a b) (hcd : leR c d) :
    ltR (a + c) (b + d) := by
  refine ⟨add_leR_add hab.1 hcd, ?_⟩
  intro heq
  have hsum0 : (b - a) + (d - c) = 0 := by
    have h1 : (b + d) - (a + c) = 0 := sub_eq_zero_iff.mpr heq.symm
    have h2 : (b + d) - (a + c) = (b - a) + (d - c) := by
      calc
        (b + d) - (a + c) = (b + d) + (-a + -c) := by
          rw [CommRing.sub_eq_add_neg, neg_add_distrib]
        _ = b + (d + (-a + -c)) := CommRing.add_assoc _ _ _
        _ = b + (-a + (d + -c)) := by rw [add_left_comm_eq d (-a) (-c)]
        _ = (b - a) + (d - c) := by
          rw [← CommRing.add_assoc, ← CommRing.sub_eq_add_neg, ← CommRing.sub_eq_add_neg]
    rw [← h2]
    exact h1
  have hna : OrderedDomain.NonNeg (-(b - a)) := by
    have hn : -(b - a) = d - c := neg_eq_of_add_eq_zero hsum0
    rw [hn]
    exact hcd
  have hba0 : b - a = 0 := OrderedDomain.nonneg_antisymm hab.1 hna
  exact hab.2 (sub_eq_zero_iff.mp hba0).symm

theorem eq_zero_of_add_nonneg_eq_zero {a b : R}
    (ha : leR 0 a) (hb : leR 0 b) (hab : a + b = 0) : a = 0 ∧ b = 0 := by
  rw [← nonneg_iff_leR] at ha hb
  have hneg : -a = b := neg_eq_of_add_eq_zero hab
  have ha0 : a = 0 := OrderedDomain.nonneg_antisymm ha (hneg ▸ hb)
  subst ha0
  rw [zero_add_eq] at hab
  exact ⟨rfl, hab⟩

theorem mul_nonneg_leR {a b : R} (ha : leR 0 a) (hb : leR 0 b) : leR 0 (a * b) := by
  rw [← nonneg_iff_leR] at *
  exact OrderedDomain.nonneg_mul ha hb

theorem mul_pos_ltR {a b : R} (ha : ltR 0 a) (hb : ltR 0 b) : ltR 0 (a * b) := by
  refine ⟨mul_nonneg_leR ha.1 hb.1, ?_⟩
  intro h0
  cases IntegralDomain.mul_eq_zero a b h0.symm with
  | inl ha0 => exact ha.2 ha0.symm
  | inr hb0 => exact hb.2 hb0.symm

theorem mul_leR_mul_of_nonneg_left {a b c : R} (hc : leR 0 c) (hab : leR a b) :
    leR (c * a) (c * b) := by
  unfold leR at *
  rw [sub_zero_eq] at hc
  rw [← mul_sub_distrib]
  exact OrderedDomain.nonneg_mul hc hab

theorem mul_leR_mul_of_nonneg_right {a b c : R} (hc : leR 0 c) (hab : leR a b) :
    leR (a * c) (b * c) := by
  rw [CommRing.mul_comm a c, CommRing.mul_comm b c]
  exact mul_leR_mul_of_nonneg_left hc hab

theorem mul_leR_mul_nonneg {a b c d : R}
    (ha : leR 0 a) (hc : leR 0 c) (hab : leR a b) (hcd : leR c d) :
    leR (a * c) (b * d) := by
  have hb : leR 0 b := leR_trans ha hab
  exact leR_trans (mul_leR_mul_of_nonneg_right hc hab) (mul_leR_mul_of_nonneg_left hb hcd)

theorem leR_of_mul_leR_mul_pos_left {a b c : R} (hc : ltR 0 c) (h : leR (c * a) (c * b)) :
    leR a b := by
  cases leR_total a b with
  | inl hab => exact hab
  | inr hba =>
    by_cases heq : a = b
    · subst heq; exact leR_refl a
    · have hlt : ltR b a := ⟨hba, fun h' => heq h'.symm⟩
      have hprod : ltR 0 (c * (a - b)) := by
        apply mul_pos_ltR hc
        have hba0 : leR 0 (a - b) := by
          unfold leR at hba ⊢
          rw [sub_zero_eq]
          exact hba
        refine ⟨hba0, ?_⟩
        intro h0
        exact hlt.2 (sub_eq_zero_iff.mp h0.symm).symm
      rw [mul_sub_distrib] at hprod
      have hle : leR (c * a) (c * b) := h
      unfold leR at hle
      have hneg : OrderedDomain.NonNeg (-(c * a - c * b)) := by
        rw [neg_sub_eq]
        exact hle
      have hzero : c * a - c * b = 0 := by
        have hpos_nn : OrderedDomain.NonNeg (c * a - c * b) := by
          have := hprod.1
          unfold leR at this
          rw [sub_zero_eq] at this
          exact this
        exact OrderedDomain.nonneg_antisymm hpos_nn hneg
      exact False.elim (hprod.2 hzero.symm)

theorem leR_of_mul_leR_mul_pos_right {a b c : R} (hc : ltR 0 c) (h : leR (a * c) (b * c)) :
    leR a b := by
  apply leR_of_mul_leR_mul_pos_left hc
  rw [CommRing.mul_comm c a, CommRing.mul_comm c b]
  exact h

theorem eq_of_mul_eq_mul_ne_zero_left {a b c : R} (hc : c ≠ 0) (h : c * a = c * b) : a = b := by
  have hsub : c * (a - b) = 0 := by
    rw [mul_sub_distrib, h, sub_self_eq_zero]
  cases IntegralDomain.mul_eq_zero c (a - b) hsub with
  | inl hc0 => exact False.elim (hc hc0)
  | inr hab0 => exact sub_eq_zero_iff.mp hab0

theorem rpow_nonneg {a : R} (ha : leR 0 a) : ∀ k : Nat, leR 0 (rpow a k)
  | 0 => zero_ltR_one.1
  | k + 1 => mul_nonneg_leR (rpow_nonneg ha k) ha

theorem rpow_pos {a : R} (ha : ltR 0 a) : ∀ k : Nat, ltR 0 (rpow a k)
  | 0 => zero_ltR_one
  | k + 1 => mul_pos_ltR (rpow_pos ha k) ha

theorem rpow_ne_zero {a : R} (ha : a ≠ 0) : ∀ k : Nat, rpow a k ≠ 0
  | 0 => IntegralDomain.zero_ne_one.symm
  | k + 1 => fun h => by
    cases IntegralDomain.mul_eq_zero _ _ h with
    | inl h1 => exact rpow_ne_zero ha k h1
    | inr h2 => exact ha h2

theorem rpow_leR_rpow_of_nonneg {a b : R} (ha : leR 0 a) (hab : leR a b) :
    ∀ k : Nat, leR (rpow a k) (rpow b k)
  | 0 => leR_refl 1
  | k + 1 => mul_leR_mul_nonneg (rpow_nonneg ha k) ha (rpow_leR_rpow_of_nonneg ha hab k) hab

theorem rpow_ltR_rpow_of_nonneg {a b : R} (ha : leR 0 a) (hab : ltR a b) :
    ∀ {k : Nat}, k ≥ 1 → ltR (rpow a k) (rpow b k)
  | 0, hk => by omega
  | 1, _ => by rw [rpow_one, rpow_one]; exact hab
  | k + 2, _ => by
    have hb_pos : ltR 0 b := ltR_of_leR_of_ltR ha hab
    have ih := rpow_ltR_rpow_of_nonneg ha hab (k := k + 1) (by omega)
    rw [rpow_succ a (k + 1), rpow_succ b (k + 1)]
    have h1 : leR (rpow a (k + 1) * a) (rpow b (k + 1) * a) :=
      mul_leR_mul_of_nonneg_right ha ih.1
    have h2 : ltR (rpow b (k + 1) * a) (rpow b (k + 1) * b) := by
      have hbpow : ltR 0 (rpow b (k + 1)) := rpow_pos hb_pos (k + 1)
      refine ⟨mul_leR_mul_of_nonneg_left hbpow.1 hab.1, ?_⟩
      intro heq
      exact hab.2 (eq_of_mul_eq_mul_ne_zero_left hbpow.2.symm heq)
    exact ltR_of_leR_of_ltR h1 h2

theorem natCastR_nonneg : ∀ n : Nat, leR (0 : R) (natCastR n)
  | 0 => leR_refl 0
  | n + 1 => by
    rw [natCastR_succ]
    have h := add_leR_add (natCastR_nonneg n) zero_ltR_one.1
    rw [zero_add_eq] at h
    exact h

theorem natCastR_pos {n : Nat} (hn : n ≥ 1) : ltR (0 : R) (natCastR n) := by
  cases n with
  | zero => omega
  | succ k =>
    rw [natCastR_succ]
    have h := add_ltR_add_of_ltR_of_leR (zero_ltR_one (R := R)) (natCastR_nonneg k)
    rw [zero_add_eq, CommRing.add_comm] at h
    exact h

theorem natCastR_ltR_of_lt {m n : Nat} (h : m < n) : ltR (natCastR m : R) (natCastR n) := by
  have hd : n = m + (n - m) := (Nat.add_sub_of_le (Nat.le_of_lt h)).symm
  rw [hd, natCastR_add]
  have hpos : ltR (0 : R) (natCastR (n - m)) := natCastR_pos (by omega)
  have hlt := add_ltR_add_of_ltR_of_leR hpos (leR_refl (natCastR m))
  rw [zero_add_eq, CommRing.add_comm (natCastR (n - m))] at hlt
  exact hlt

theorem natCastR_leR_of_le {m n : Nat} (h : m ≤ n) : leR (natCastR m : R) (natCastR n) := by
  by_cases heq : m = n
  · subst heq; exact leR_refl _
  · exact (natCastR_ltR_of_lt (by omega)).1

theorem two_pos : ltR (0 : R) (natCastR 2) := natCastR_pos (by omega)

/-! ### Absolute Value Lemmas -/

theorem absR_of_nonneg {a : R} (ha : leR 0 a) : absR a = a := by
  unfold absR
  rw [← nonneg_iff_leR] at ha
  simp [ha]

theorem absR_of_nonpos {a : R} (ha : leR a 0) : absR a = -a := by
  by_cases h0 : OrderedDomain.NonNeg a
  · unfold absR
    simp [h0]
    unfold leR at ha
    rw [zero_sub_eq] at ha
    have heq : a = 0 := OrderedDomain.nonneg_antisymm h0 ha
    rw [heq, neg_zero_eq]
  · unfold absR
    simp [h0]

theorem absR_nonneg (a : R) : leR 0 (absR a) := by
  cases leR_total 0 a with
  | inl ha => rw [absR_of_nonneg ha]; exact ha
  | inr ha =>
    rw [absR_of_nonpos ha]
    unfold leR at ha ⊢
    rw [zero_sub_eq] at ha
    rw [sub_zero_eq]
    exact ha

theorem absR_neg (a : R) : absR (-a) = absR a := by
  cases leR_total 0 a with
  | inl ha =>
    have hna : leR (-a) 0 := by
      unfold leR at ha ⊢
      rw [sub_zero_eq] at ha
      rw [zero_sub_eq, neg_neg_eq]
      exact ha
    rw [absR_of_nonneg ha, absR_of_nonpos hna, neg_neg_eq]
  | inr ha =>
    have hna : leR 0 (-a) := by
      unfold leR at ha ⊢
      rw [zero_sub_eq] at ha
      rw [sub_zero_eq]
      exact ha
    rw [absR_of_nonpos ha, absR_of_nonneg hna]

theorem absR_sq (a : R) : absR a * absR a = a * a := by
  cases leR_total 0 a with
  | inl ha => rw [absR_of_nonneg ha]
  | inr ha => rw [absR_of_nonpos ha, neg_mul_neg]

theorem absR_eq_zero_iff (a : R) : absR a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have hsq : absR a * absR a = 0 := by rw [h, mul_zero_eq]
    rw [absR_sq] at hsq
    exact (sq_eq_zero_iff a).mp hsq
  · intro h
    subst h
    exact absR_of_nonneg (leR_refl 0)

theorem leR_absR_self (a : R) : leR a (absR a) := by
  cases leR_total 0 a with
  | inl ha => rw [absR_of_nonneg ha]; exact leR_refl a
  | inr ha =>
    rw [absR_of_nonpos ha]
    unfold leR at ha ⊢
    rw [zero_sub_eq] at ha
    rw [CommRing.sub_eq_add_neg]
    exact OrderedDomain.nonneg_add ha ha

theorem neg_leR_absR_self (a : R) : leR (-a) (absR a) := by
  rw [← absR_neg a]
  exact leR_absR_self (-a)

theorem absR_leR_iff {a b : R} : leR (absR a) b ↔ (leR a b ∧ leR (-a) b) := by
  constructor
  · intro h
    exact ⟨leR_trans (leR_absR_self a) h, leR_trans (neg_leR_absR_self a) h⟩
  · intro ⟨h1, h2⟩
    cases leR_total 0 a with
    | inl ha => rw [absR_of_nonneg ha]; exact h1
    | inr ha => rw [absR_of_nonpos ha]; exact h2

theorem absR_add_leR (a b : R) : leR (absR (a + b)) (absR a + absR b) := by
  rw [absR_leR_iff]
  refine ⟨add_leR_add (leR_absR_self a) (leR_absR_self b), ?_⟩
  rw [neg_add_distrib]
  exact add_leR_add (neg_leR_absR_self a) (neg_leR_absR_self b)

theorem absR_mul (a b : R) : absR (a * b) = absR a * absR b := by
  cases leR_total 0 a with
  | inl ha =>
    cases leR_total 0 b with
    | inl hb =>
      rw [absR_of_nonneg ha, absR_of_nonneg hb, absR_of_nonneg (mul_nonneg_leR ha hb)]
    | inr hb =>
      have hab : leR (a * b) 0 := by
        have h := mul_leR_mul_of_nonneg_left ha hb
        rw [mul_zero_eq] at h
        exact h
      rw [absR_of_nonneg ha, absR_of_nonpos hb, absR_of_nonpos hab, mul_neg_eq]
  | inr ha =>
    cases leR_total 0 b with
    | inl hb =>
      have hab : leR (a * b) 0 := by
        have h := mul_leR_mul_of_nonneg_right hb ha
        rw [zero_mul_eq] at h
        exact h
      rw [absR_of_nonpos ha, absR_of_nonneg hb, absR_of_nonpos hab, neg_mul_eq]
    | inr hb =>
      have hna : leR 0 (-a) := by rw [← absR_of_nonpos ha]; exact absR_nonneg a
      have hnb : leR 0 (-b) := by rw [← absR_of_nonpos hb]; exact absR_nonneg b
      have hab : leR 0 (a * b) := by
        rw [← neg_mul_neg a b]
        exact mul_nonneg_leR hna hnb
      rw [absR_of_nonpos ha, absR_of_nonpos hb, absR_of_nonneg hab, neg_mul_neg]

theorem absR_rpow (a : R) : ∀ k : Nat, absR (rpow a k) = rpow (absR a) k
  | 0 => absR_of_nonneg zero_ltR_one.1
  | k + 1 => by rw [rpow_succ, rpow_succ, absR_mul, absR_rpow a k]

theorem sq_leR_sq_iff_absR_leR {a b : R} (hb : leR 0 b) :
    leR (a * a) (b * b) ↔ leR (absR a) b := by
  constructor
  · intro h
    cases leR_total (absR a) b with
    | inl hle => exact hle
    | inr hge =>
      by_cases heq : absR a = b
      · rw [heq]; exact leR_refl b
      · have hlt : ltR b (absR a) := ⟨hge, fun h' => heq h'.symm⟩
        have hsum_pos : ltR 0 (absR a + b) := by
          have ha_pos : ltR 0 (absR a) := ltR_of_leR_of_ltR hb hlt
          have h1 := add_ltR_add_of_ltR_of_leR ha_pos hb
          rw [zero_add_eq] at h1
          exact h1
        have hdiff_pos : ltR 0 (absR a - b) := by
          have hd_nn : leR 0 (absR a - b) := by
            have := hlt.1
            unfold leR at this ⊢
            rw [sub_zero_eq]
            exact this
          refine ⟨hd_nn, ?_⟩
          intro h0
          exact heq (sub_eq_zero_iff.mp h0.symm)
        have hprod := mul_pos_ltR hdiff_pos hsum_pos
        rw [diff_sq_eq, absR_sq] at hprod
        unfold leR at h
        have hneg : OrderedDomain.NonNeg (-(a * a - b * b)) := by
          rw [neg_sub_eq]
          exact h
        have hpos_nn : OrderedDomain.NonNeg (a * a - b * b) := by
          have := hprod.1
          unfold leR at this
          rw [sub_zero_eq] at this
          exact this
        exact False.elim (hprod.2 (OrderedDomain.nonneg_antisymm hpos_nn hneg).symm)
  · intro h
    rw [← absR_sq a]
    exact mul_leR_mul_nonneg (absR_nonneg a) (absR_nonneg a) h h

theorem sq_eq_sq_iff_absR_eq {a b : R} (hb : leR 0 b) :
    a * a = b * b ↔ absR a = b := by
  constructor
  · intro h
    apply leR_antisymm
    · exact (sq_leR_sq_iff_absR_leR hb).mp (by rw [h]; exact leR_refl _)
    · rw [← absR_sq a] at h
      have h' : leR (b * b) (absR a * absR a) := by rw [h]; exact leR_refl _
      have := (sq_leR_sq_iff_absR_leR (absR_nonneg a)).mp h'
      rw [absR_of_nonneg hb] at this
      exact this
  · intro h
    rw [← h, absR_sq]

end OrderedDomainLemmas

/-! ### Complexification `ComplexOver R` (`R[i]`) -/

/-- Algebraic complexification `R[i] = {re + im * i : re, im ∈ R}` over any ring `R`. -/
structure ComplexOver (R : Type u) where
  re : R
  im : R

namespace ComplexOver

@[ext]
theorem ext {R : Type u} {z w : ComplexOver R} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z; cases w; simp_all

section CommRingComplex

variable {R : Type u} [CommRing R]

def ofReal (r : R) : ComplexOver R := ⟨r, 0⟩
def iUnit : ComplexOver R := ⟨0, 1⟩
def conj (z : ComplexOver R) : ComplexOver R := ⟨z.re, -z.im⟩
def normSq (z : ComplexOver R) : R := z.re * z.re + z.im * z.im

instance : CommRing (ComplexOver R) where
  zero := ⟨0, 0⟩
  one := ⟨1, 0⟩
  add z w := ⟨z.re + w.re, z.im + w.im⟩
  neg z := ⟨-z.re, -z.im⟩
  sub z w := ⟨z.re - w.re, z.im - w.im⟩
  mul z w := ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩
  add_assoc a b c := ext (CommRing.add_assoc _ _ _) (CommRing.add_assoc _ _ _)
  add_comm a b := ext (CommRing.add_comm _ _) (CommRing.add_comm _ _)
  zero_add a := ext (zero_add_eq _) (zero_add_eq _)
  add_zero a := ext (add_zero_eq _) (add_zero_eq _)
  neg_add_cancel a := ext (neg_add_cancel_eq _) (neg_add_cancel_eq _)
  sub_eq_add_neg a b := ext (CommRing.sub_eq_add_neg _ _) (CommRing.sub_eq_add_neg _ _)
  mul_assoc a b c := by
    apply ext
    · change (a.re * b.re - a.im * b.im) * c.re - (a.re * b.im + a.im * b.re) * c.im =
        a.re * (b.re * c.re - b.im * c.im) - a.im * (b.re * c.im + b.im * c.re)
      rw [sub_mul_distrib, CommRing.right_distrib, mul_sub_distrib, CommRing.left_distrib,
          CommRing.mul_assoc, CommRing.mul_assoc, CommRing.mul_assoc, CommRing.mul_assoc,
          CommRing.sub_eq_add_neg, CommRing.sub_eq_add_neg, CommRing.sub_eq_add_neg,
          CommRing.sub_eq_add_neg, neg_add_distrib, neg_add_distrib]
      rw [CommRing.add_assoc, CommRing.add_assoc,
          add_left_comm_eq (-(a.im * (b.im * c.re))) (-(a.re * (b.im * c.im))),
          CommRing.add_comm (-(a.im * (b.im * c.re))) (-(a.im * (b.re * c.im)))]
    · change (a.re * b.re - a.im * b.im) * c.im + (a.re * b.im + a.im * b.re) * c.re =
        a.re * (b.re * c.im + b.im * c.re) + a.im * (b.re * c.re - b.im * c.im)
      rw [sub_mul_distrib, CommRing.right_distrib, CommRing.left_distrib, mul_sub_distrib,
          CommRing.mul_assoc, CommRing.mul_assoc, CommRing.mul_assoc, CommRing.mul_assoc,
          CommRing.sub_eq_add_neg, CommRing.sub_eq_add_neg]
      rw [CommRing.add_assoc, CommRing.add_assoc,
          add_left_comm_eq (-(a.im * (b.im * c.im))) (a.re * (b.im * c.re)),
          CommRing.add_comm (-(a.im * (b.im * c.im))) (a.im * (b.re * c.re))]
  mul_comm a b := by
    apply ext
    · change a.re * b.re - a.im * b.im = b.re * a.re - b.im * a.im
      rw [CommRing.mul_comm a.re b.re, CommRing.mul_comm a.im b.im]
    · change a.re * b.im + a.im * b.re = b.re * a.im + b.im * a.re
      rw [CommRing.mul_comm a.re b.im, CommRing.mul_comm a.im b.re, CommRing.add_comm]
  one_mul a := by
    apply ext
    · change 1 * a.re - 0 * a.im = a.re
      rw [one_mul_eq, zero_mul_eq, sub_zero_eq]
    · change 1 * a.im + 0 * a.re = a.im
      rw [one_mul_eq, zero_mul_eq, add_zero_eq]
  mul_one a := by
    apply ext
    · change a.re * 1 - a.im * 0 = a.re
      rw [mul_one_eq, mul_zero_eq, sub_zero_eq]
    · change a.re * 0 + a.im * 1 = a.im
      rw [mul_zero_eq, mul_one_eq, zero_add_eq]
  left_distrib a b c := by
    apply ext
    · change a.re * (b.re + c.re) - a.im * (b.im + c.im) =
        (a.re * b.re - a.im * b.im) + (a.re * c.re - a.im * c.im)
      rw [CommRing.left_distrib, CommRing.left_distrib,
          CommRing.sub_eq_add_neg, CommRing.sub_eq_add_neg, CommRing.sub_eq_add_neg,
          neg_add_distrib, CommRing.add_assoc, CommRing.add_assoc,
          add_left_comm_eq (a.re * c.re) (-(a.im * b.im)) (-(a.im * c.im))]
    · change a.re * (b.im + c.im) + a.im * (b.re + c.re) =
        (a.re * b.im + a.im * b.re) + (a.re * c.im + a.im * c.re)
      rw [CommRing.left_distrib, CommRing.left_distrib, CommRing.add_assoc, CommRing.add_assoc,
          add_left_comm_eq (a.re * c.im) (a.im * b.re) (a.im * c.re)]
  right_distrib a b c := by
    apply ext
    · change (a.re + b.re) * c.re - (a.im + b.im) * c.im =
        (a.re * c.re - a.im * c.im) + (b.re * c.re - b.im * c.im)
      rw [CommRing.right_distrib, CommRing.right_distrib,
          CommRing.sub_eq_add_neg, CommRing.sub_eq_add_neg, CommRing.sub_eq_add_neg,
          neg_add_distrib, CommRing.add_assoc, CommRing.add_assoc,
          add_left_comm_eq (b.re * c.re) (-(a.im * c.im)) (-(b.im * c.im))]
    · change (a.re + b.re) * c.im + (a.im + b.im) * c.re =
        (a.re * c.im + a.im * c.re) + (b.re * c.im + b.im * c.re)
      rw [CommRing.right_distrib, CommRing.right_distrib, CommRing.add_assoc, CommRing.add_assoc,
          add_left_comm_eq (b.re * c.im) (a.im * c.re) (b.im * c.re)]

@[simp] theorem zero_re : (0 : ComplexOver R).re = 0 := rfl
@[simp] theorem zero_im : (0 : ComplexOver R).im = 0 := rfl
@[simp] theorem one_re : (1 : ComplexOver R).re = 1 := rfl
@[simp] theorem one_im : (1 : ComplexOver R).im = 0 := rfl
@[simp] theorem add_re (z w : ComplexOver R) : (z + w).re = z.re + w.re := rfl
@[simp] theorem add_im (z w : ComplexOver R) : (z + w).im = z.im + w.im := rfl
@[simp] theorem neg_re (z : ComplexOver R) : (-z).re = -z.re := rfl
@[simp] theorem neg_im (z : ComplexOver R) : (-z).im = -z.im := rfl
@[simp] theorem sub_re (z w : ComplexOver R) : (z - w).re = z.re - w.re := rfl
@[simp] theorem sub_im (z w : ComplexOver R) : (z - w).im = z.im - w.im := rfl
@[simp] theorem mul_re (z w : ComplexOver R) : (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] theorem mul_im (z w : ComplexOver R) : (z * w).im = z.re * w.im + z.im * w.re := rfl

theorem ofReal_zero : (ofReal 0 : ComplexOver R) = 0 := rfl
theorem ofReal_one : (ofReal 1 : ComplexOver R) = 1 := rfl

theorem ofReal_add (a b : R) : ofReal (a + b) = ofReal a + ofReal b :=
  ext rfl (add_zero_eq 0).symm

theorem ofReal_sub (a b : R) : ofReal (a - b) = ofReal a - ofReal b :=
  ext rfl (sub_self_eq_zero 0).symm

theorem ofReal_mul (a b : R) : ofReal (a * b) = ofReal a * ofReal b := by
  apply ext
  · change a * b = a * b - 0 * 0
    rw [mul_zero_eq, sub_zero_eq]
  · change 0 = a * 0 + 0 * b
    rw [mul_zero_eq, zero_mul_eq, add_zero_eq]

theorem ofReal_rpow (a : R) : ∀ k : Nat, ofReal (rpow a k) = rpow (ofReal a) k
  | 0 => rfl
  | k + 1 => by rw [rpow_succ, rpow_succ, ofReal_mul, ofReal_rpow a k]

theorem ofReal_natCastR : ∀ n : Nat, (ofReal (natCastR n) : ComplexOver R) = natCastR n
  | 0 => rfl
  | n + 1 => by rw [natCastR_succ, natCastR_succ, ofReal_add, ofReal_natCastR n, ofReal_one]

theorem conj_add (z w : ComplexOver R) : conj (z + w) = conj z + conj w :=
  ext rfl (neg_add_distrib z.im w.im)

theorem conj_mul (z w : ComplexOver R) : conj (z * w) = conj z * conj w := by
  apply ext
  · change z.re * w.re - z.im * w.im = z.re * w.re - (-z.im) * (-w.im)
    rw [neg_mul_neg]
  · change -(z.re * w.im + z.im * w.re) = z.re * (-w.im) + (-z.im) * w.re
    rw [mul_neg_eq, neg_mul_eq, neg_add_distrib]

theorem mul_conj_eq (z : ComplexOver R) : z * conj z = ofReal (normSq z) := by
  apply ext
  · change z.re * z.re - z.im * (-z.im) = z.re * z.re + z.im * z.im
    rw [mul_neg_eq, CommRing.sub_eq_add_neg, neg_neg_eq]
  · change z.re * (-z.im) + z.im * z.re = 0
    rw [mul_neg_eq, CommRing.mul_comm z.im z.re, neg_add_cancel_eq]

theorem normSq_ofReal (a : R) : normSq (ofReal a) = a * a := by
  unfold normSq ofReal
  rw [mul_zero_eq, add_zero_eq]

theorem normSq_conj (z : ComplexOver R) : normSq (conj z) = normSq z := by
  unfold normSq conj
  rw [neg_mul_neg]

theorem normSq_neg (z : ComplexOver R) : normSq (-z) = normSq z := by
  unfold normSq
  rw [neg_re, neg_im, neg_mul_neg, neg_mul_neg]

/-- Brahmagupta-Fibonacci identity `|z * w|^2 = |z|^2 * |w|^2` over any `CommRing R`. -/
theorem normSq_mul (z w : ComplexOver R) : normSq (z * w) = normSq z * normSq w := by
  unfold normSq
  simp only [mul_re, mul_im]
  have h1 : (z.re * w.re - z.im * w.im) * (z.re * w.re - z.im * w.im) =
      (z.re * z.re) * (w.re * w.re) + (z.im * z.im) * (w.im * w.im) -
      ((z.re * w.re) * (z.im * w.im) + (z.re * w.re) * (z.im * w.im)) := by
    rw [sub_sq_eq]
    have ha : (z.re * w.re) * (z.re * w.re) = (z.re * z.re) * (w.re * w.re) := by
      rw [CommRing.mul_assoc, mul_left_comm_eq w.re z.re w.re, ← CommRing.mul_assoc]
    have hb : (z.im * w.im) * (z.im * w.im) = (z.im * z.im) * (w.im * w.im) := by
      rw [CommRing.mul_assoc, mul_left_comm_eq w.im z.im w.im, ← CommRing.mul_assoc]
    rw [ha, hb]
  have h2 : (z.re * w.im + z.im * w.re) * (z.re * w.im + z.im * w.re) =
      (z.re * z.re) * (w.im * w.im) + (z.im * z.im) * (w.re * w.re) +
      ((z.re * w.re) * (z.im * w.im) + (z.re * w.re) * (z.im * w.im)) := by
    rw [CommRing.left_distrib, CommRing.right_distrib, CommRing.right_distrib]
    have ha : (z.re * w.im) * (z.re * w.im) = (z.re * z.re) * (w.im * w.im) := by
      rw [CommRing.mul_assoc, mul_left_comm_eq w.im z.re w.im, ← CommRing.mul_assoc]
    have hb : (z.im * w.re) * (z.im * w.re) = (z.im * z.im) * (w.re * w.re) := by
      rw [CommRing.mul_assoc, mul_left_comm_eq w.re z.im w.re, ← CommRing.mul_assoc]
    have hc : (z.re * w.im) * (z.im * w.re) = (z.re * w.re) * (z.im * w.im) := by
      rw [CommRing.mul_assoc, CommRing.mul_comm w.im (z.im * w.re),
          CommRing.mul_assoc z.im w.re w.im, mul_left_comm_eq z.re z.im (w.re * w.im),
          CommRing.mul_comm z.im, ← CommRing.mul_assoc z.re w.re,
          CommRing.mul_assoc (z.re * w.re), CommRing.mul_comm w.im z.im]
    have hd : (z.im * w.re) * (z.re * w.im) = (z.re * w.re) * (z.im * w.im) := by
      rw [CommRing.mul_comm (z.im * w.re), hc]
    rw [ha, hb, hc, hd]
    calc
      (z.re * z.re * (w.im * w.im) + z.re * w.re * (z.im * w.im)) +
          (z.re * w.re * (z.im * w.im) + z.im * z.im * (w.re * w.re)) =
          z.re * z.re * (w.im * w.im) +
          (z.re * w.re * (z.im * w.im) + (z.im * z.im * (w.re * w.re) + z.re * w.re * (z.im * w.im))) := by
        rw [CommRing.add_comm (z.re * w.re * (z.im * w.im)) (z.im * z.im * (w.re * w.re)),
            CommRing.add_assoc]
      _ = z.re * z.re * (w.im * w.im) +
          (z.im * z.im * (w.re * w.re) + (z.re * w.re * (z.im * w.im) + z.re * w.re * (z.im * w.im))) := by
        rw [add_left_comm_eq (z.re * w.re * (z.im * w.im)) (z.im * z.im * (w.re * w.re))]
      _ = (z.re * z.re * (w.im * w.im) + z.im * z.im * (w.re * w.re)) +
          (z.re * w.re * (z.im * w.im) + z.re * w.re * (z.im * w.im)) := by
        rw [← CommRing.add_assoc]
  rw [h1, h2]
  let A := z.re * z.re * (w.re * w.re)
  let B := z.im * z.im * (w.im * w.im)
  let C := z.re * z.re * (w.im * w.im)
  let D := z.im * z.im * (w.re * w.re)
  let X := z.re * w.re * (z.im * w.im) + z.re * w.re * (z.im * w.im)
  have hcancel : (A + B - X) + ((C + D) + X) = (A + C) + (D + B) := by
    calc
      (A + B - X) + ((C + D) + X) = (A + B) + (-X + (X + (C + D))) := by
        rw [CommRing.sub_eq_add_neg, CommRing.add_comm (C + D) X, CommRing.add_assoc]
      _ = (A + B) + ((-X + X) + (C + D)) := by rw [← CommRing.add_assoc (-X) X]
      _ = (A + B) + (C + D) := by rw [neg_add_cancel_eq, zero_add_eq]
      _ = A + (B + (C + D)) := CommRing.add_assoc A B _
      _ = A + (C + (B + D)) := by rw [add_left_comm_eq B C D]
      _ = (A + C) + (D + B) := by rw [CommRing.add_comm B D, ← CommRing.add_assoc]
  change (A + B - X) + ((C + D) + X) = (z.re * z.re + z.im * z.im) * (w.re * w.re + w.im * w.im)
  rw [hcancel, CommRing.right_distrib, CommRing.left_distrib, CommRing.left_distrib]

theorem normSq_rpow (z : ComplexOver R) : ∀ k : Nat, normSq (rpow z k) = rpow (normSq z) k
  | 0 => by
    unfold normSq
    change 1 * 1 + 0 * 0 = 1
    rw [mul_one_eq, mul_zero_eq, add_zero_eq]
  | k + 1 => by rw [rpow_succ, rpow_succ, normSq_mul, normSq_rpow z k]

theorem normSq_sub_eq (z w : ComplexOver R) :
    normSq (z - w) = normSq z + normSq w - ((z * conj w).re + (z * conj w).re) := by
  unfold normSq conj
  simp only [sub_re, sub_im, mul_re]
  rw [sub_sq_eq, sub_sq_eq]
  have hzw : z.re * w.re - z.im * (-w.im) = z.re * w.re + z.im * w.im := by
    rw [mul_neg_eq, CommRing.sub_eq_add_neg, neg_neg_eq]
  rw [hzw]
  let P := z.re * z.re
  let Q := w.re * w.re
  let U := z.im * z.im
  let V := w.im * w.im
  let M := z.re * w.re
  let N := z.im * w.im
  change (P + Q - (M + M)) + (U + V - (N + N)) = (P + U) + (Q + V) - ((M + N) + (M + N))
  have hMN : (M + N) + (M + N) = (M + M) + (N + N) := by
    rw [CommRing.add_assoc, CommRing.add_assoc, add_left_comm_eq N M N]
  rw [hMN, CommRing.sub_eq_add_neg, CommRing.sub_eq_add_neg, CommRing.sub_eq_add_neg,
      neg_add_distrib (M + M) (N + N)]
  calc
    (P + Q + -(M + M)) + (U + V + -(N + N)) =
        P + (Q + (-(M + M) + (U + (V + -(N + N))))) := by
      rw [CommRing.add_assoc, CommRing.add_assoc, CommRing.add_assoc]
    _ = P + (U + (Q + (V + (-(M + M) + -(N + N))))) := by
      rw [add_left_comm_eq (-(M + M)) U, add_left_comm_eq Q U,
          add_left_comm_eq (-(M + M)) V]
    _ = ((P + U) + (Q + V)) + (-(M + M) + -(N + N)) := by
      rw [← CommRing.add_assoc Q V, ← CommRing.add_assoc P U,
          ← CommRing.add_assoc (P + U) (Q + V)]

end CommRingComplex

section OrderedComplex

variable {R : Type u} [OrderedDomain R]

theorem normSq_nonneg (z : ComplexOver R) : leR 0 (normSq z) := by
  unfold normSq
  have h := add_leR_add (sq_nonneg z.re) (sq_nonneg z.im)
  rw [zero_add_eq] at h
  exact h

theorem normSq_eq_zero_iff (z : ComplexOver R) : normSq z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have ⟨hre2, him2⟩ := eq_zero_of_add_nonneg_eq_zero (sq_nonneg z.re) (sq_nonneg z.im) h
    exact ext ((sq_eq_zero_iff z.re).mp hre2) ((sq_eq_zero_iff z.im).mp him2)
  · intro h
    subst h
    unfold normSq
    change 0 * 0 + 0 * 0 = 0
    rw [mul_zero_eq, add_zero_eq]

theorem normSq_pos_of_ne_zero {z : ComplexOver R} (hz : z ≠ 0) : ltR 0 (normSq z) := by
  refine ⟨normSq_nonneg z, ?_⟩
  intro h0
  exact hz ((normSq_eq_zero_iff z).mp h0.symm)

instance : IntegralDomain (ComplexOver R) where
  zero_ne_one h := by
    have hre : (0 : R) = 1 := congrArg ComplexOver.re h
    exact IntegralDomain.zero_ne_one hre
  mul_eq_zero z w h := by
    have hn : normSq (z * w) = 0 := by rw [h]; exact (normSq_eq_zero_iff 0).mpr rfl
    rw [normSq_mul] at hn
    cases IntegralDomain.mul_eq_zero _ _ hn with
    | inl hz => exact Or.inl ((normSq_eq_zero_iff z).mp hz)
    | inr hw => exact Or.inr ((normSq_eq_zero_iff w).mp hw)

end OrderedComplex

end ComplexOver

/-! ### Pascal Binomial Coefficients & Vandermonde's Identity -/

/-- Binomial coefficient `C(n, k)` defined via Pascal's recursion. -/
def binom : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => binom n k + binom n (k + 1)

@[simp] theorem binom_zero_zero : binom 0 0 = 1 := rfl
@[simp] theorem binom_zero_succ (k : Nat) : binom 0 (k + 1) = 0 := rfl
@[simp] theorem binom_succ_zero (n : Nat) : binom (n + 1) 0 = 1 := rfl
@[simp] theorem binom_succ_succ (n k : Nat) :
    binom (n + 1) (k + 1) = binom n k + binom n (k + 1) := rfl

theorem binom_zero_right : ∀ n : Nat, binom n 0 = 1
  | 0 => rfl
  | _ + 1 => rfl

theorem binom_eq_zero_of_lt : ∀ {n k : Nat}, n < k → binom n k = 0
  | 0, 0, h => by omega
  | 0, _ + 1, _ => rfl
  | n + 1, 0, h => by omega
  | n + 1, k + 1, h => by
    rw [binom_succ_succ, binom_eq_zero_of_lt (by omega), binom_eq_zero_of_lt (by omega)]

theorem binom_self : ∀ n : Nat, binom n n = 1
  | 0 => rfl
  | n + 1 => by rw [binom_succ_succ, binom_self n, binom_eq_zero_of_lt (by omega)]

theorem binom_one_right : ∀ n : Nat, binom n 1 = n
  | 0 => rfl
  | n + 1 => by rw [binom_succ_succ, binom_zero_right, binom_one_right n]; omega

theorem binom_pos : ∀ {n k : Nat}, k ≤ n → 1 ≤ binom n k
  | 0, 0, _ => by decide
  | 0, _ + 1, h => by omega
  | n + 1, 0, _ => by rw [binom_succ_zero]; omega
  | n + 1, k + 1, h => by
    rw [binom_succ_succ]
    have h1 : 1 ≤ binom n k := binom_pos (by omega)
    omega

/-- Finite sum `∑_{j=0}^{m-1} f(j)` in `Nat`. -/
def natSumRange : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | m + 1, f => natSumRange m f + f m

theorem natSumRange_congr {m : Nat} {f g : Nat → Nat} (h : ∀ j, j < m → f j = g j) :
    natSumRange m f = natSumRange m g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    unfold natSumRange
    rw [ih (fun j hj => h j (by omega)), h m (by omega)]

theorem natSumRange_add (m : Nat) (f g : Nat → Nat) :
    natSumRange m (fun j => f j + g j) = natSumRange m f + natSumRange m g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    unfold natSumRange
    dsimp only
    rw [ih]
    omega

theorem natSumRange_succ_shift (m : Nat) (f : Nat → Nat) :
    natSumRange (m + 1) f = f 0 + natSumRange m (fun j => f (j + 1)) := by
  induction m with
  | zero =>
    change 0 + f 0 = f 0 + 0
    omega
  | succ m ih =>
    change natSumRange (m + 1) f + f (m + 1) = f 0 + (natSumRange m (fun j => f (j + 1)) + f (m + 1))
    rw [ih]
    omega

/-- Row sum identity `∑_{k=0}^n C(n, k) = 2^n`. -/
theorem binom_row_sum : ∀ n : Nat, natSumRange (n + 1) (fun j => binom n j) = 2 ^ n
  | 0 => rfl
  | n + 1 => by
    rw [natSumRange_succ_shift (n + 1)]
    change 1 + natSumRange (n + 1) (fun j => binom n j + binom n (j + 1)) = 2 ^ (n + 1)
    rw [natSumRange_add, binom_row_sum n]
    have hshift : 1 + natSumRange (n + 1) (fun j => binom n (j + 1)) = 2 ^ n := by
      have htop : natSumRange (n + 2) (fun j => binom n j) =
          natSumRange (n + 1) (fun j => binom n j) + binom n (n + 1) := rfl
      rw [binom_eq_zero_of_lt (by omega), Nat.add_zero] at htop
      have hbot := natSumRange_succ_shift (n + 1) (fun j => binom n j)
      rw [binom_zero_right] at hbot
      change natSumRange (n + 2) (fun j => binom n j) = _ at hbot
      rw [htop, binom_row_sum n] at hbot
      exact hbot.symm
    have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; omega
    omega

/-- Symmetry of binomial coefficients `C(n, k) = C(n, n - k)` for `k ≤ n`. -/
theorem binom_symm : ∀ {n k : Nat}, k ≤ n → binom n k = binom n (n - k)
  | 0, 0, _ => rfl
  | 0, _ + 1, h => by omega
  | n + 1, 0, _ => by rw [Nat.sub_zero, binom_succ_zero, binom_self]
  | n + 1, k + 1, h => by
    by_cases heq : k + 1 = n + 1
    · have hk : k = n := by omega
      subst hk
      rw [Nat.sub_self, binom_self, binom_zero_right]
    · have hlt : k < n := by omega
      have hd1 : n + 1 - (k + 1) = (n - (k + 1)) + 1 := by omega
      have hd2 : n - k = (n - (k + 1)) + 1 := by omega
      rw [hd1, binom_succ_succ, binom_succ_succ,
          binom_symm (n := n) (k := k) (by omega), hd2,
          binom_symm (n := n) (k := k + 1) (by omega)]
      omega

/-- Vandermonde's convolution identity: `∑_{j=0}^c C(a, j) * C(b, c - j) = C(a + b, c)`. -/
theorem vandermonde : ∀ (a b c : Nat),
    natSumRange (c + 1) (fun j => binom a j * binom b (c - j)) = binom (a + b) c
  | 0, b, c => by
    rw [natSumRange_succ_shift, Nat.zero_add, binom_zero_zero, Nat.sub_zero, Nat.one_mul]
    have hzero : natSumRange c (fun j => binom 0 (j + 1) * binom b (c - (j + 1))) = 0 := by
      suffices ∀ m (f : Nat → Nat), (∀ j, f j = 0) → natSumRange m f = 0 from
        this c _ (fun _ => by simp)
      intro m f hf
      induction m with
      | zero => rfl
      | succ m ihm => unfold natSumRange; rw [ihm, hf]
    rw [hzero]
    omega
  | a + 1, b, 0 => by
    change 0 + binom (a + 1) 0 * binom b 0 = binom (a + 1 + b) 0
    rw [Nat.zero_add, binom_zero_right, binom_zero_right, binom_zero_right]
  | a + 1, b, c + 1 => by
    rw [natSumRange_succ_shift (c + 1)]
    simp only [binom_succ_zero, Nat.sub_zero, Nat.one_mul, binom_succ_succ]
    have hsub : ∀ j, j < c + 1 → c + 1 - (j + 1) = c - j := fun _ _ => by omega
    have hcongr : natSumRange (c + 1) (fun j => (binom a j + binom a (j + 1)) * binom b (c + 1 - (j + 1))) =
        natSumRange (c + 1) (fun j => binom a j * binom b (c - j) + binom a (j + 1) * binom b (c - j)) := by
      apply natSumRange_congr
      intro j hj
      rw [hsub j hj, Nat.right_distrib]
    rw [hcongr, natSumRange_add, vandermonde a b c]
    have h2 := vandermonde a b (c + 1)
    rw [natSumRange_succ_shift (c + 1)] at h2
    simp only [binom_zero_right, Nat.sub_zero, Nat.one_mul] at h2
    have hcongr2 : natSumRange (c + 1) (fun j => binom a (j + 1) * binom b (c + 1 - (j + 1))) =
        natSumRange (c + 1) (fun j => binom a (j + 1) * binom b (c - j)) := by
      apply natSumRange_congr
      intro j hj
      rw [hsub j hj]
    rw [hcongr2] at h2
    have hadd : a + 1 + b = a + b + 1 := by omega
    rw [hadd, binom_succ_succ]
    omega

/-- Special Vandermonde identity `∑_{k=0}^{m-1} C(m - 1, k) * C(m, k) = C(2m - 1, m - 1)`
    for the first row of the binomial-entry tensor `B_{m,2}` (`m = d + 1`). -/
theorem vandermonde_binom_row1 (d : Nat) :
    natSumRange (d + 1) (fun k => binom d k * binom (d + 1) k) = binom (2 * d + 1) d := by
  have hcongr : natSumRange (d + 1) (fun k => binom d k * binom (d + 1) k) =
      natSumRange (d + 1) (fun k => binom d k * binom (d + 1) (d + 1 - k)) := by
    apply natSumRange_congr
    intro k hk
    rw [← binom_symm (n := d + 1) (k := k) (by omega)]
  have hv := vandermonde d (d + 1) (d + 1)
  have hv_step : natSumRange (d + 2) (fun j => binom d j * binom (d + 1) (d + 1 - j)) =
      natSumRange (d + 1) (fun j => binom d j * binom (d + 1) (d + 1 - j)) +
      binom d (d + 1) * binom (d + 1) (d + 1 - (d + 1)) := rfl
  rw [hv_step, binom_eq_zero_of_lt (n := d) (k := d + 1) (by omega), Nat.zero_mul, Nat.add_zero] at hv
  have hadd : d + (d + 1) = 2 * d + 1 := by omega
  have hsymm : binom (2 * d + 1) (d + 1) = binom (2 * d + 1) d := by
    rw [binom_symm (n := 2 * d + 1) (k := d + 1) (by omega)]
    congr 1
    omega
  rw [hcongr, hv, hadd, hsymm]

/-- Special Vandermonde identity `∑_{k=0}^{m-1} C(m - 1, k) * C(m, k + 1) = C(2m - 1, m - 1)`
    for the second row of the binomial-entry tensor `B_{m,2}` (`m = d + 1`). -/
theorem vandermonde_binom_row2 (d : Nat) :
    natSumRange (d + 1) (fun k => binom d k * binom (d + 1) (k + 1)) = binom (2 * d + 1) d := by
  have hcongr : natSumRange (d + 1) (fun k => binom d k * binom (d + 1) (k + 1)) =
      natSumRange (d + 1) (fun k => binom d k * binom (d + 1) (d - k)) := by
    apply natSumRange_congr
    intro k hk
    have hsym := binom_symm (n := d + 1) (k := k + 1) (by omega)
    have hsub : d + 1 - (k + 1) = d - k := by omega
    rw [hsym, hsub]
  have hv := vandermonde d (d + 1) d
  have hadd : d + (d + 1) = 2 * d + 1 := by omega
  rw [hcongr, hv, hadd]

/-! ### Concrete Instance 1: `Int` (`ℤ`) -/

instance : OrderedDomain Int where
  zero := 0
  one := 1
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  neg_add_cancel := Int.add_left_neg
  sub_eq_add_neg := fun _ _ => Int.sub_eq_add_neg
  mul_assoc := Int.mul_assoc
  mul_comm := Int.mul_comm
  one_mul := Int.one_mul
  mul_one := Int.mul_one
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  zero_ne_one := by decide
  mul_eq_zero := fun _ _ h => Int.mul_eq_zero.mp h
  NonNeg := fun z => 0 ≤ z
  nonneg_zero := Int.le_refl 0
  nonneg_one := by decide
  nonneg_add := fun ha hb => Int.add_nonneg ha hb
  nonneg_mul := fun ha hb => Int.mul_nonneg ha hb
  nonneg_antisymm := fun ha hna => by omega
  nonneg_total := fun a => by omega

theorem int_natCastR_eq (n : Nat) : (natCastR n : Int) = (n : Int) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [natCastR_succ, ih]
    change (n : Int) + 1 = ((n + 1 : Nat) : Int)
    omega

theorem int_leR_iff {a b : Int} : leR a b ↔ a ≤ b := by
  unfold leR OrderedDomain.NonNeg
  change 0 ≤ b - a ↔ a ≤ b
  omega

theorem int_ltR_iff {a b : Int} : ltR a b ↔ a < b := by
  unfold ltR
  rw [int_leR_iff]
  omega

/-! ### Concrete Instance 2: `RatField` (`ℚ`) via Quotient of Integer Fractions -/

/-- Raw fraction `num / den` with `0 < den`. -/
structure RatRaw where
  num : Int
  den : Int
  den_pos : 0 < den

/-- Equivalence relation `a.num * b.den = b.num * a.den`. -/
def RatRel (a b : RatRaw) : Prop := a.num * b.den = b.num * a.den

theorem ratRel_refl (a : RatRaw) : RatRel a a := rfl
theorem ratRel_symm {a b : RatRaw} (h : RatRel a b) : RatRel b a := h.symm

private theorem int_mul_cancel_pos {x y c : Int} (hc : 0 < c) (h : x * c = y * c) : x = y := by
  have hsub : (x - y) * c = 0 := by
    rw [Int.sub_mul, h]
    omega
  cases Int.mul_eq_zero.mp hsub with
  | inl hxy => omega
  | inr hc0 => omega

private theorem int_mul_four (u v w z : Int) : (u * v) * (w * z) = (u * w) * (v * z) := by
  rw [Int.mul_assoc, Int.mul_left_comm v w z, ← Int.mul_assoc]

theorem ratRel_trans {a b c : RatRaw} (hab : RatRel a b) (hbc : RatRel b c) : RatRel a c := by
  unfold RatRel at *
  apply int_mul_cancel_pos b.den_pos
  calc
    a.num * c.den * b.den = (a.num * b.den) * c.den := by
      rw [Int.mul_assoc, Int.mul_comm c.den b.den, ← Int.mul_assoc]
    _ = (b.num * a.den) * c.den := by rw [hab]
    _ = (b.num * c.den) * a.den := by
      rw [Int.mul_assoc, Int.mul_comm a.den c.den, ← Int.mul_assoc]
    _ = (c.num * b.den) * a.den := by rw [hbc]
    _ = c.num * a.den * b.den := by
      rw [Int.mul_assoc, Int.mul_comm b.den a.den, ← Int.mul_assoc]

/-- The ordered field of rational numbers `ℚ`. -/
def RatField : Type := Quot RatRel

namespace RatField

def mk (num : Int) (den : Int) (h : 0 < den) : RatField := Quot.mk RatRel ⟨num, den, h⟩

def ofInt (z : Int) : RatField := mk z 1 (by omega)

private def addRaw (a b : RatRaw) : RatRaw :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den, Int.mul_pos a.den_pos b.den_pos⟩

private def negRaw (a : RatRaw) : RatRaw := ⟨-a.num, a.den, a.den_pos⟩

private def mulRaw (a b : RatRaw) : RatRaw :=
  ⟨a.num * b.num, a.den * b.den, Int.mul_pos a.den_pos b.den_pos⟩

private theorem addRaw_rel {a₁ a₂ b₁ b₂ : RatRaw}
    (ha : RatRel a₁ a₂) (hb : RatRel b₁ b₂) :
    RatRel (addRaw a₁ b₁) (addRaw a₂ b₂) := by
  change (a₁.num * b₁.den + b₁.num * a₁.den) * (a₂.den * b₂.den) =
         (a₂.num * b₂.den + b₂.num * a₂.den) * (a₁.den * b₁.den)
  unfold RatRel at ha hb
  have hL1 : (a₁.num * b₁.den) * (a₂.den * b₂.den) = (a₂.num * a₁.den) * (b₁.den * b₂.den) := by
    rw [int_mul_four, ha]
  have hL2 : (b₁.num * a₁.den) * (a₂.den * b₂.den) = (b₂.num * b₁.den) * (a₁.den * a₂.den) := by
    rw [Int.mul_comm a₂.den b₂.den, int_mul_four, hb]
  have hR1 : (a₂.num * b₂.den) * (a₁.den * b₁.den) = (a₂.num * a₁.den) * (b₁.den * b₂.den) := by
    rw [int_mul_four, Int.mul_comm b₂.den b₁.den]
  have hR2 : (b₂.num * a₂.den) * (a₁.den * b₁.den) = (b₂.num * b₁.den) * (a₁.den * a₂.den) := by
    rw [Int.mul_comm a₁.den b₁.den, int_mul_four, Int.mul_comm a₂.den a₁.den]
  rw [Int.add_mul, Int.add_mul, hL1, hL2, hR1, hR2]

private theorem negRaw_rel {a₁ a₂ : RatRaw} (ha : RatRel a₁ a₂) :
    RatRel (negRaw a₁) (negRaw a₂) := by
  change (-a₁.num) * a₂.den = (-a₂.num) * a₁.den
  unfold RatRel at ha
  rw [Int.neg_mul, Int.neg_mul, ha]

private theorem mulRaw_rel {a₁ a₂ b₁ b₂ : RatRaw}
    (ha : RatRel a₁ a₂) (hb : RatRel b₁ b₂) :
    RatRel (mulRaw a₁ b₁) (mulRaw a₂ b₂) := by
  change (a₁.num * b₁.num) * (a₂.den * b₂.den) = (a₂.num * b₂.num) * (a₁.den * b₁.den)
  unfold RatRel at ha hb
  rw [int_mul_four, ha, hb, int_mul_four]

def add (x y : RatField) : RatField :=
  Quot.lift
    (fun a => Quot.lift (fun b => Quot.mk RatRel (addRaw a b))
      (fun _ _ hb => Quot.sound (addRaw_rel (ratRel_refl a) hb)) y)
    (fun a₁ a₂ ha => by
      induction y using Quot.ind with
      | _ b => exact Quot.sound (addRaw_rel ha (ratRel_refl b)))
    x

def neg (x : RatField) : RatField :=
  Quot.lift (fun a => Quot.mk RatRel (negRaw a)) (fun _ _ ha => Quot.sound (negRaw_rel ha)) x

def mul (x y : RatField) : RatField :=
  Quot.lift
    (fun a => Quot.lift (fun b => Quot.mk RatRel (mulRaw a b))
      (fun _ _ hb => Quot.sound (mulRaw_rel (ratRel_refl a) hb)) y)
    (fun a₁ a₂ ha => by
      induction y using Quot.ind with
      | _ b => exact Quot.sound (mulRaw_rel ha (ratRel_refl b)))
    x

private theorem nonneg_well_def {a b : RatRaw} (h : RatRel a b) :
    (0 ≤ a.num) = (0 ≤ b.num) := by
  apply propext
  unfold RatRel at h
  have ha_pos := a.den_pos
  have hb_pos := b.den_pos
  constructor
  · intro ha
    by_cases hb : 0 ≤ b.num
    · exact hb
    · have hbn : 0 < -b.num := by omega
      have hprod1 : 0 < (-b.num) * a.den := Int.mul_pos hbn ha_pos
      have hprod2 : 0 ≤ a.num * b.den := Int.mul_nonneg ha (by omega)
      rw [Int.neg_mul] at hprod1
      omega
  · intro hb
    by_cases ha : 0 ≤ a.num
    · exact ha
    · have han : 0 < -a.num := by omega
      have hprod1 : 0 < (-a.num) * b.den := Int.mul_pos han hb_pos
      have hprod2 : 0 ≤ b.num * a.den := Int.mul_nonneg hb (by omega)
      rw [Int.neg_mul] at hprod1
      omega

def NonNeg (x : RatField) : Prop :=
  Quot.lift (fun a => 0 ≤ a.num) (fun _ _ h => nonneg_well_def h) x

private theorem num_zero_well_def (u v : RatRaw) (huv : RatRel u v) :
    (u.num = (0 : Int)) = (v.num = (0 : Int)) :=
  propext ⟨fun hu => by
      unfold RatRel at huv; rw [hu, Int.zero_mul] at huv
      cases Int.mul_eq_zero.mp huv.symm with
      | inl hv0 => exact hv0
      | inr hu0 => have := u.den_pos; omega,
    fun hv => by
      unfold RatRel at huv; rw [hv, Int.zero_mul] at huv
      cases Int.mul_eq_zero.mp huv with
      | inl hu0 => exact hu0
      | inr hv0 => have := v.den_pos; omega⟩

instance : OrderedDomain RatField where
  zero := ofInt 0
  one := ofInt 1
  add := add
  neg := neg
  sub x y := add x (neg y)
  mul := mul
  add_assoc x y z := by
    induction x using Quot.ind with | _ a =>
    induction y using Quot.ind with | _ b =>
    induction z using Quot.ind with | _ c =>
    apply Quot.sound
    change ((a.num * b.den + b.num * a.den) * c.den + c.num * (a.den * b.den)) *
           (a.den * (b.den * c.den)) =
           (a.num * (b.den * c.den) + (b.num * c.den + c.num * b.den) * a.den) *
           ((a.den * b.den) * c.den)
    simp only [Int.add_mul, Int.mul_add, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm,
               Int.add_assoc, Int.add_left_comm, Int.add_comm]
  add_comm x y := by
    induction x using Quot.ind with | _ a =>
    induction y using Quot.ind with | _ b =>
    apply Quot.sound
    change (a.num * b.den + b.num * a.den) * (b.den * a.den) =
           (b.num * a.den + a.num * b.den) * (a.den * b.den)
    simp only [Int.add_mul, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm, Int.add_comm]
  zero_add x := by
    induction x using Quot.ind with | _ a =>
    apply Quot.sound
    change ((0 : Int) * a.den + a.num * (1 : Int)) * a.den = a.num * ((1 : Int) * a.den)
    simp only [Int.zero_mul, Int.mul_one, Int.one_mul, Int.zero_add]
  add_zero x := by
    induction x using Quot.ind with | _ a =>
    apply Quot.sound
    change (a.num * (1 : Int) + (0 : Int) * a.den) * a.den = a.num * (a.den * (1 : Int))
    simp only [Int.zero_mul, Int.mul_one, Int.add_zero]
  neg_add_cancel x := by
    induction x using Quot.ind with | _ a =>
    apply Quot.sound
    change ((-a.num) * a.den + a.num * a.den) * (1 : Int) = (0 : Int) * (a.den * a.den)
    rw [Int.neg_mul]
    omega
  sub_eq_add_neg _ _ := rfl
  mul_assoc x y z := by
    induction x using Quot.ind with | _ a =>
    induction y using Quot.ind with | _ b =>
    induction z using Quot.ind with | _ c =>
    apply Quot.sound
    change ((a.num * b.num) * c.num) * (a.den * (b.den * c.den)) =
           (a.num * (b.num * c.num)) * ((a.den * b.den) * c.den)
    simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  mul_comm x y := by
    induction x using Quot.ind with | _ a =>
    induction y using Quot.ind with | _ b =>
    apply Quot.sound
    change (a.num * b.num) * (b.den * a.den) = (b.num * a.num) * (a.den * b.den)
    simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  one_mul x := by
    induction x using Quot.ind with | _ a =>
    apply Quot.sound
    change ((1 : Int) * a.num) * a.den = a.num * ((1 : Int) * a.den)
    simp only [Int.one_mul]
  mul_one x := by
    induction x using Quot.ind with | _ a =>
    apply Quot.sound
    change (a.num * (1 : Int)) * a.den = a.num * (a.den * (1 : Int))
    simp only [Int.mul_one]
  left_distrib x y z := by
    induction x using Quot.ind with | _ a =>
    induction y using Quot.ind with | _ b =>
    induction z using Quot.ind with | _ c =>
    apply Quot.sound
    change (a.num * (b.num * c.den + c.num * b.den)) * ((a.den * b.den) * (a.den * c.den)) =
           ((a.num * b.num) * (a.den * c.den) + (a.num * c.num) * (a.den * b.den)) *
           (a.den * (b.den * c.den))
    simp only [Int.add_mul, Int.mul_add, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  right_distrib x y z := by
    induction x using Quot.ind with | _ a =>
    induction y using Quot.ind with | _ b =>
    induction z using Quot.ind with | _ c =>
    apply Quot.sound
    change ((a.num * b.den + b.num * a.den) * c.num) * ((a.den * c.den) * (b.den * c.den)) =
           ((a.num * c.num) * (b.den * c.den) + (b.num * c.num) * (a.den * c.den)) *
           ((a.den * b.den) * c.den)
    simp only [Int.add_mul, Int.mul_add, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  zero_ne_one h := by
    have hp : Quot.lift (fun r : RatRaw => r.num = (0 : Int)) num_zero_well_def (ofInt 0) := rfl
    change ofInt 0 = ofInt 1 at h
    rw [h] at hp
    have hp1 : (1 : Int) = (0 : Int) := hp
    omega
  mul_eq_zero x y h := by
    induction x using Quot.ind with | _ a =>
    induction y using Quot.ind with | _ b =>
    have hnum0 : a.num * b.num = (0 : Int) := by
      have hp : Quot.lift (fun r : RatRaw => r.num = (0 : Int)) num_zero_well_def
          (mul (Quot.mk RatRel a) (Quot.mk RatRel b)) = (a.num * b.num = (0 : Int)) := rfl
      have hz : Quot.lift (fun r : RatRaw => r.num = (0 : Int)) num_zero_well_def (ofInt 0) := rfl
      change mul (Quot.mk RatRel a) (Quot.mk RatRel b) = ofInt 0 at h
      rw [← h, hp] at hz
      exact hz
    cases Int.mul_eq_zero.mp hnum0 with
    | inl ha0 =>
      left
      apply Quot.sound
      change a.num * (1 : Int) = (0 : Int) * a.den
      rw [ha0]; omega
    | inr hb0 =>
      right
      apply Quot.sound
      change b.num * (1 : Int) = (0 : Int) * b.den
      rw [hb0]; omega
  NonNeg := NonNeg
  nonneg_zero := Int.le_refl 0
  nonneg_one := by change (0 : Int) ≤ 1; omega
  nonneg_add {x y} hx hy := by
    induction x using Quot.ind with | _ a =>
    induction y using Quot.ind with | _ b =>
    change 0 ≤ a.num at hx
    change 0 ≤ b.num at hy
    change 0 ≤ a.num * b.den + b.num * a.den
    exact Int.add_nonneg (Int.mul_nonneg hx (by have := b.den_pos; omega))
                         (Int.mul_nonneg hy (by have := a.den_pos; omega))
  nonneg_mul {x y} hx hy := by
    induction x using Quot.ind with | _ a =>
    induction y using Quot.ind with | _ b =>
    exact Int.mul_nonneg hx hy
  nonneg_antisymm {x} hx hnx := by
    induction x using Quot.ind with | _ a =>
    change 0 ≤ a.num at hx
    change 0 ≤ -a.num at hnx
    have ha0 : a.num = (0 : Int) := by omega
    apply Quot.sound
    change a.num * (1 : Int) = (0 : Int) * a.den
    rw [ha0]; omega
  nonneg_total x := by
    induction x using Quot.ind with | _ a =>
    change (0 ≤ a.num) ∨ (0 ≤ -a.num)
    omega

theorem mk_eq_iff {n₁ d₁ n₂ d₂ : Int} (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    mk n₁ d₁ h₁ = mk n₂ d₂ h₂ ↔ n₁ * d₂ = n₂ * d₁ := by
  constructor
  · intro heq
    let wf : ∀ u v : RatRaw, RatRel u v → (u.num * d₂ = n₂ * u.den) = (v.num * d₂ = n₂ * v.den) :=
      fun u v huv => propext ⟨fun hu => by
        unfold RatRel at huv
        apply int_mul_cancel_pos u.den_pos
        calc
          v.num * d₂ * u.den = (v.num * u.den) * d₂ := by
            simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
          _ = (u.num * v.den) * d₂ := by rw [← huv]
          _ = (u.num * d₂) * v.den := by
            simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
          _ = (n₂ * u.den) * v.den := by rw [hu]
          _ = n₂ * v.den * u.den := by
            simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm],
       fun hv => by
        unfold RatRel at huv
        apply int_mul_cancel_pos v.den_pos
        calc
          u.num * d₂ * v.den = (u.num * v.den) * d₂ := by
            simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
          _ = (v.num * u.den) * d₂ := by rw [huv]
          _ = (v.num * d₂) * u.den := by
            simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
          _ = (n₂ * v.den) * u.den := by rw [hv]
          _ = n₂ * u.den * v.den := by
            simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]⟩
    have hp : Quot.lift (fun r : RatRaw => r.num * d₂ = n₂ * r.den) wf (mk n₁ d₁ h₁) =
        (n₁ * d₂ = n₂ * d₁) := rfl
    have hr : Quot.lift (fun r : RatRaw => r.num * d₂ = n₂ * r.den) wf (mk n₂ d₂ h₂) := rfl
    rw [← heq, hp] at hr
    exact hr
  · intro hrel
    exact Quot.sound hrel

theorem mk_add {n₁ d₁ n₂ d₂ : Int} (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    mk n₁ d₁ h₁ + mk n₂ d₂ h₂ = mk (n₁ * d₂ + n₂ * d₁) (d₁ * d₂) (Int.mul_pos h₁ h₂) := rfl

theorem mk_neg {n d : Int} (h : 0 < d) : -(mk n d h) = mk (-n) d h := rfl

theorem mk_sub {n₁ d₁ n₂ d₂ : Int} (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    mk n₁ d₁ h₁ - mk n₂ d₂ h₂ = mk (n₁ * d₂ + (-n₂) * d₁) (d₁ * d₂) (Int.mul_pos h₁ h₂) := rfl

theorem mk_mul {n₁ d₁ n₂ d₂ : Int} (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    mk n₁ d₁ h₁ * mk n₂ d₂ h₂ = mk (n₁ * n₂) (d₁ * d₂) (Int.mul_pos h₁ h₂) := rfl

theorem mk_rpow (n d : Int) (h : 0 < d) :
    ∀ k : Nat, rpow (mk n d h) k =
      mk (rpow n k) (rpow d k) (by
        have hp := rpow_pos (R := Int) (int_ltR_iff.mpr h) k
        exact int_ltR_iff.mp hp)
  | 0 => rfl
  | k + 1 => by
    simp only [rpow_succ, mk_rpow n d h k, mk_mul]

theorem natCastR_eq_mk (m : Nat) : (natCastR m : RatField) = mk (m : Int) 1 (by omega) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [natCastR_succ, ih]
    change mk (m : Int) 1 _ + mk (1 : Int) 1 _ = mk ((m + 1 : Nat) : Int) 1 _
    rw [mk_add, mk_eq_iff]
    omega

theorem leR_mk_iff {n₁ d₁ n₂ d₂ : Int} (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    leR (mk n₁ d₁ h₁) (mk n₂ d₂ h₂) ↔ n₁ * d₂ ≤ n₂ * d₁ := by
  unfold leR OrderedDomain.NonNeg
  rw [mk_sub]
  change 0 ≤ n₂ * d₁ + (-n₁) * d₂ ↔ n₁ * d₂ ≤ n₂ * d₁
  rw [Int.neg_mul]
  omega

theorem ltR_mk_iff {n₁ d₁ n₂ d₂ : Int} (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    ltR (mk n₁ d₁ h₁) (mk n₂ d₂ h₂) ↔ n₁ * d₂ < n₂ * d₁ := by
  unfold ltR
  rw [leR_mk_iff, ne_eq, mk_eq_iff]
  omega

end RatField

end Conjecture00000007176
