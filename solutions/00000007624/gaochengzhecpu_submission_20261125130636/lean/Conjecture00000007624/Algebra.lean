/-
Copyright (c) 2026 The Last Math Competition Contributors. All rights reserved.
Self-contained algebraic hierarchy in Core Lean 4.19.0 (zero external dependencies)
for Conjecture 00000007624: associative unital rings, commutative rings,
integral domains, ordered domains, nilpotency reduction, and concrete instances
(`Int`, `GaussInt`, `F3`, `F5`).
-/

namespace Conjecture00000007624

/-- An associative unital ring equipped with standard arithmetic operations. -/
class AssocRing (A : Type u) extends Add A, Mul A, Neg A, Sub A where
  zero : A
  one : A
  add_assoc : ∀ a b c : A, a + b + c = a + (b + c)
  add_comm : ∀ a b : A, a + b = b + a
  zero_add : ∀ a : A, zero + a = a
  add_zero : ∀ a : A, a + zero = a
  neg_add_cancel : ∀ a : A, -a + a = zero
  sub_eq_add_neg : ∀ a b : A, a - b = a + -b
  mul_assoc : ∀ a b c : A, a * b * c = a * (b * c)
  one_mul : ∀ a : A, one * a = a
  mul_one : ∀ a : A, a * one = a
  left_distrib : ∀ a b c : A, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : A, (a + b) * c = a * c + b * c

@[reducible] instance (priority := 100) [AssocRing A] : OfNat A 0 := ⟨AssocRing.zero⟩
@[reducible] instance (priority := 100) [AssocRing A] : OfNat A 1 := ⟨AssocRing.one⟩

@[simp] theorem AssocRing.ofNat_zero [AssocRing A] : (0 : A) = AssocRing.zero := rfl
@[simp] theorem AssocRing.ofNat_one [AssocRing A] : (1 : A) = AssocRing.one := rfl

/-- A commutative unital ring. -/
class CommRing (R : Type u) extends AssocRing R where
  mul_comm : ∀ a b : R, a * b = b * a

/-- An integral domain: nontrivial commutative ring with no zero divisors. -/
class IntegralDomain (R : Type u) extends CommRing R where
  zero_ne_one : (0 : R) ≠ 1
  mul_eq_zero : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0

/-- An ordered integral domain specified via its non-negative cone `NonNeg`.
    Simultaneously abstracts `ℤ`, `ℚ`, real algebraic fields, and `ℝ`. -/
class OrderedDomain (R : Type u) extends IntegralDomain R where
  NonNeg : R → Prop
  nonneg_zero : NonNeg 0
  nonneg_one : NonNeg 1
  nonneg_add : ∀ {a b : R}, NonNeg a → NonNeg b → NonNeg (a + b)
  nonneg_sq : ∀ a : R, NonNeg (a * a)
  nonneg_antisymm : ∀ {a : R}, NonNeg a → NonNeg (-a) → a = 0

section AssocRingLemmas

variable {A : Type u} [AssocRing A]

theorem zero_add_eq (a : A) : 0 + a = a := AssocRing.zero_add a
theorem add_zero_eq (a : A) : a + 0 = a := AssocRing.add_zero a
theorem neg_add_cancel_eq (a : A) : -a + a = 0 := AssocRing.neg_add_cancel a
theorem one_mul_eq (a : A) : 1 * a = a := AssocRing.one_mul a
theorem mul_one_eq (a : A) : a * 1 = a := AssocRing.mul_one a

theorem add_neg_cancel (a : A) : a + -a = 0 := by
  rw [AssocRing.add_comm, neg_add_cancel_eq]

theorem add_left_cancel {a b c : A} (h : a + b = a + c) : b = c := by
  have h1 : -a + (a + b) = -a + (a + c) := congrArg (fun x => -a + x) h
  rw [← AssocRing.add_assoc, ← AssocRing.add_assoc, neg_add_cancel_eq,
      zero_add_eq, zero_add_eq] at h1
  exact h1

theorem add_right_cancel {a b c : A} (h : b + a = c + a) : b = c := by
  apply add_left_cancel (a := a)
  rw [AssocRing.add_comm a b, AssocRing.add_comm a c]
  exact h

theorem neg_eq_of_add_eq_zero {a b : A} (h : a + b = 0) : -a = b := by
  apply add_left_cancel (a := a)
  rw [add_neg_cancel, h]

theorem neg_zero_eq : -(0 : A) = 0 :=
  neg_eq_of_add_eq_zero (zero_add_eq 0)

theorem neg_neg_eq (a : A) : -(-a) = a :=
  neg_eq_of_add_eq_zero (neg_add_cancel_eq a)

theorem neg_add_rev (a b : A) : -(a + b) = -b + -a := by
  apply neg_eq_of_add_eq_zero
  calc
    (a + b) + (-b + -a) = a + (b + (-b + -a)) := AssocRing.add_assoc a b (-b + -a)
    _ = a + ((b + -b) + -a) := by rw [AssocRing.add_assoc b (-b) (-a)]
    _ = a + (0 + -a) := by rw [add_neg_cancel]
    _ = a + -a := by rw [zero_add_eq]
    _ = 0 := add_neg_cancel a

theorem neg_add_distrib (a b : A) : -(a + b) = -a + -b := by
  rw [neg_add_rev, AssocRing.add_comm]

theorem sub_self_eq_zero (a : A) : a - a = 0 := by
  rw [AssocRing.sub_eq_add_neg, add_neg_cancel]

theorem mul_zero_eq (a : A) : a * 0 = 0 := by
  apply add_left_cancel (a := a * 0)
  calc
    a * 0 + a * 0 = a * (0 + 0) := (AssocRing.left_distrib a 0 0).symm
    _ = a * 0 := by rw [add_zero_eq]
    _ = a * 0 + 0 := (add_zero_eq (a * 0)).symm

theorem zero_mul_eq (a : A) : 0 * a = 0 := by
  apply add_left_cancel (a := 0 * a)
  calc
    0 * a + 0 * a = (0 + 0) * a := (AssocRing.right_distrib 0 0 a).symm
    _ = 0 * a := by rw [add_zero_eq]
    _ = 0 * a + 0 := (add_zero_eq (0 * a)).symm

theorem mul_neg_eq (a b : A) : a * (-b) = -(a * b) := by
  symm
  apply neg_eq_of_add_eq_zero
  calc
    a * b + a * (-b) = a * (b + -b) := (AssocRing.left_distrib a b (-b)).symm
    _ = a * 0 := by rw [add_neg_cancel]
    _ = 0 := mul_zero_eq a

theorem neg_mul_eq (a b : A) : (-a) * b = -(a * b) := by
  symm
  apply neg_eq_of_add_eq_zero
  calc
    a * b + (-a) * b = (a + -a) * b := (AssocRing.right_distrib a (-a) b).symm
    _ = 0 * b := by rw [add_neg_cancel]
    _ = 0 := zero_mul_eq b

theorem neg_mul_neg (a b : A) : (-a) * (-b) = a * b := by
  rw [neg_mul_eq, mul_neg_eq, neg_neg_eq]

theorem mul_sub_distrib (a b c : A) : a * (b - c) = a * b - a * c := by
  rw [AssocRing.sub_eq_add_neg, AssocRing.left_distrib, mul_neg_eq, ← AssocRing.sub_eq_add_neg]

theorem sub_mul_distrib (a b c : A) : (a - b) * c = a * c - b * c := by
  rw [AssocRing.sub_eq_add_neg, AssocRing.right_distrib, neg_mul_eq, ← AssocRing.sub_eq_add_neg]

/-- Monoid power in any associative unital ring. -/
def apow (x : A) : Nat → A
  | 0 => 1
  | k + 1 => apow x k * x

theorem apow_zero (x : A) : apow x 0 = 1 := rfl

theorem apow_one (x : A) : apow x 1 = x := by
  change 1 * x = x
  exact one_mul_eq x

theorem apow_two (x : A) : apow x 2 = x * x := by
  change (1 * x) * x = x * x
  rw [one_mul_eq]

theorem apow_add (x : A) (m : Nat) : ∀ n : Nat, apow x (m + n) = apow x m * apow x n
  | 0 => by
    change apow x m = apow x m * 1
    exact (mul_one_eq (apow x m)).symm
  | n + 1 => by
    rw [Nat.add_succ, apow, apow, apow_add x m n, AssocRing.mul_assoc]

/-- `x` is square-zero (`x^2 = 0`). -/
def IsSqZero (x : A) : Prop := x * x = 0

/-- `x` is nilpotent (`x^k = 0` for some exponent `k ≥ 1`). -/
def IsNilpotent (x : A) : Prop := ∃ k : Nat, k ≥ 1 ∧ apow x k = 0

theorem isNilpotent_of_isSqZero {x : A} (h : IsSqZero x) : IsNilpotent x :=
  ⟨2, by omega, by rw [apow_two]; exact h⟩

private theorem nat_le_two_pow : ∀ k : Nat, k ≤ 2 ^ k
  | 0 => by omega
  | k + 1 => by
    have ih := nat_le_two_pow k
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    calc
      k + 1 ≤ 2 ^ k + 1 := Nat.add_le_add_right ih 1
      _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add_left hpos (2 ^ k)
      _ = 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega

private theorem eq_zero_of_apow_two_pow_eq_zero
    (hred : ∀ y : A, y * y = 0 → y = 0) (x : A) :
    ∀ m : Nat, apow x (2 ^ m) = 0 → x = 0
  | 0, h => by
    change 1 * x = 0 at h
    rw [one_mul_eq] at h
    exact h
  | m + 1, h => by
    have hsplit : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by
      rw [Nat.pow_succ]
      omega
    rw [hsplit, apow_add] at h
    have hm : apow x (2 ^ m) = 0 := hred (apow x (2 ^ m)) h
    exact eq_zero_of_apow_two_pow_eq_zero hred x m hm

/-- In any associative unital ring, having no nonzero nilpotents of arbitrary index `k ≥ 1`
    is equivalent to having no nonzero square-zero elements (`y * y = 0 → y = 0`). -/
theorem reduced_iff_no_sq_zero :
    (∀ x : A, IsNilpotent x → x = 0) ↔ (∀ x : A, IsSqZero x → x = 0) := by
  constructor
  · intro h x hx
    exact h x (isNilpotent_of_isSqZero hx)
  · intro hred x ⟨k, _, hk⟩
    have hle : k ≤ 2 ^ k := nat_le_two_pow k
    have hsum : 2 ^ k = k + (2 ^ k - k) := (Nat.add_sub_of_le hle).symm
    have hpow : apow x (2 ^ k) = 0 := by
      rw [hsum, apow_add, hk, zero_mul_eq]
    exact eq_zero_of_apow_two_pow_eq_zero hred x k hpow

theorem exists_nonzero_nilpotent_iff_exists_nonzero_sq_zero :
    (∃ x : A, x ≠ 0 ∧ IsNilpotent x) ↔ (∃ x : A, x ≠ 0 ∧ IsSqZero x) := by
  constructor
  · intro ⟨x, hx0, k, hk1, hxk⟩
    -- Either look at minimal power or use induction on `k` directly:
    suffices ∀ m : Nat, ∀ y : A, m ≥ 1 → y ≠ 0 → apow y m = 0 → ∃ z : A, z ≠ 0 ∧ IsSqZero z from
      this k x hk1 hx0 hxk
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro y hm1 hy0 hym
      by_cases hm_eq : m = 1
      · subst hm_eq
        rw [apow_one] at hym
        exact False.elim (hy0 hym)
      · -- Consider `m = 2` vs `m > 2`: split at `q = (m + 1) / 2` so `q < m` and `2 * q ≥ m`
        let q := (m + 1) / 2
        have hq_lt : q < m := by omega
        have hq_ge : q ≥ 1 := by omega
        by_cases hyq : apow y q = 0
        · exact ih q hq_lt y hq_ge hy0 hyq
        · refine ⟨apow y q, hyq, ?_⟩
          change apow y q * apow y q = 0
          rw [← apow_add]
          have h2q : q + q ≥ m := by omega
          have hdecomp : q + q = m + (q + q - m) := (Nat.add_sub_of_le h2q).symm
          rw [hdecomp, apow_add, hym, zero_mul_eq]
  · intro ⟨x, hx0, hx2⟩
    exact ⟨x, hx0, isNilpotent_of_isSqZero hx2⟩

end AssocRingLemmas

section IntegralDomainLemmas

variable {R : Type u} [IntegralDomain R]

theorem apow_eq_zero_iff (a : R) : ∀ {k : Nat}, k ≥ 1 → (apow a k = 0 ↔ a = 0)
  | 0, hk => by omega
  | 1, _ => by rw [apow_one]
  | k + 2, _ => by
    constructor
    · intro h
      change apow a (k + 1) * a = 0 at h
      cases IntegralDomain.mul_eq_zero _ _ h with
      | inl h1 => exact (apow_eq_zero_iff a (k := k + 1) (by omega)).mp h1
      | inr h2 => exact h2
    · intro ha
      subst ha
      change apow (0 : R) (k + 1) * 0 = 0
      exact mul_zero_eq _

theorem sq_eq_zero_iff (a : R) : a * a = 0 ↔ a = 0 := by
  constructor
  · intro h
    cases IntegralDomain.mul_eq_zero a a h with
    | inl h1 => exact h1
    | inr h2 => exact h2
  · intro h
    rw [h, mul_zero_eq]

end IntegralDomainLemmas

section OrderedDomainLemmas

variable {R : Type u} [OrderedDomain R]

theorem eq_zero_of_add_nonneg_eq_zero {a b : R}
    (ha : OrderedDomain.NonNeg a) (hb : OrderedDomain.NonNeg b) (hab : a + b = 0) :
    a = 0 ∧ b = 0 := by
  have hneg : -a = b := neg_eq_of_add_eq_zero hab
  have hna : OrderedDomain.NonNeg (-a) := hneg ▸ hb
  have ha0 : a = 0 := OrderedDomain.nonneg_antisymm ha hna
  subst ha0
  rw [zero_add_eq] at hab
  exact ⟨rfl, hab⟩

theorem two_ne_zero : (1 + 1 : R) ≠ 0 := by
  intro h
  have ⟨h1, _⟩ := eq_zero_of_add_nonneg_eq_zero
    OrderedDomain.nonneg_one OrderedDomain.nonneg_one h
  exact IntegralDomain.zero_ne_one h1.symm

theorem eq_zero_of_two_mul_eq_zero {a : R} (h : (1 + 1 : R) * a = 0) : a = 0 := by
  cases IntegralDomain.mul_eq_zero (1 + 1) a h with
  | inl h2 => exact False.elim (two_ne_zero h2)
  | inr ha => exact ha

theorem eq_zero_of_add_self_eq_zero {a : R} (h : a + a = 0) : a = 0 := by
  apply eq_zero_of_two_mul_eq_zero
  rw [AssocRing.right_distrib, one_mul_eq]
  exact h

theorem sum_two_sq_eq_zero {a b : R} (h : a * a + b * b = 0) : a = 0 ∧ b = 0 := by
  have ⟨ha2, hb2⟩ := eq_zero_of_add_nonneg_eq_zero
    (OrderedDomain.nonneg_sq a) (OrderedDomain.nonneg_sq b) h
  exact ⟨(sq_eq_zero_iff a).mp ha2, (sq_eq_zero_iff b).mp hb2⟩

theorem sum_four_sq_eq_zero {a b c d : R}
    (h : (a * a + b * b) + (c * c + d * d) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have h12 : OrderedDomain.NonNeg (a * a + b * b) :=
    OrderedDomain.nonneg_add (OrderedDomain.nonneg_sq a) (OrderedDomain.nonneg_sq b)
  have h34 : OrderedDomain.NonNeg (c * c + d * d) :=
    OrderedDomain.nonneg_add (OrderedDomain.nonneg_sq c) (OrderedDomain.nonneg_sq d)
  have ⟨hab, hcd⟩ := eq_zero_of_add_nonneg_eq_zero h12 h34 h
  have ⟨ha, hb⟩ := sum_two_sq_eq_zero hab
  have ⟨hc, hd⟩ := sum_two_sq_eq_zero hcd
  exact ⟨ha, hb, hc, hd⟩

end OrderedDomainLemmas

/-! ### Concrete Instances: `Int`, `GaussInt`, `F3`, `F5` -/

private theorem int_sq_nonneg (a : Int) : 0 ≤ a * a := by
  by_cases h : 0 ≤ a
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ -a := by omega
    have heq : (-a) * (-a) = a * a := by
      rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    rw [← heq]
    exact Int.mul_nonneg hn hn

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
  nonneg_sq := int_sq_nonneg
  nonneg_antisymm := fun ha hna => by omega

/-- Gaussian integers `ℤ[i] = {re + im * i : re, im ∈ ℤ}`, modeling complex / algebraically
    closed quadratic phenomena where `-1 = i^2` is a square. -/
structure GaussInt where
  re : Int
  im : Int
  deriving DecidableEq, Repr

namespace GaussInt

def iUnit : GaussInt := ⟨0, 1⟩

def normSq (z : GaussInt) : Int := z.re * z.re + z.im * z.im

instance : Add GaussInt := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Neg GaussInt := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : Sub GaussInt := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩
instance : Mul GaussInt := ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩
instance : OfNat GaussInt 0 := ⟨⟨0, 0⟩⟩
instance : OfNat GaussInt 1 := ⟨⟨1, 0⟩⟩

@[ext]
theorem ext {z w : GaussInt} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z; cases w; simp_all

private theorem int_four_sq (a b c d : Int) :
    (a * c - b * d) * (a * c - b * d) + (a * d + b * c) * (a * d + b * c) =
    (a * a + b * b) * (c * c + d * d) := by
  have h1 : (a * c - b * d) * (a * c - b * d) =
      a * (a * (c * c)) - (a * (b * (c * d)) + a * (b * (c * d))) + b * (b * (d * d)) := by
    simp only [Int.sub_eq_add_neg, Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
      Int.neg_neg, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    omega
  have h2 : (a * d + b * c) * (a * d + b * c) =
      a * (a * (d * d)) + (a * (b * (c * d)) + a * (b * (c * d))) + b * (b * (c * c)) := by
    simp only [Int.add_mul, Int.mul_add, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    omega
  have h3 : (a * a + b * b) * (c * c + d * d) =
      a * (a * (c * c)) + a * (a * (d * d)) + b * (b * (c * c)) + b * (b * (d * d)) := by
    simp only [Int.add_mul, Int.mul_add, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    omega
  rw [h1, h2, h3]
  omega

theorem normSq_mul (z w : GaussInt) : normSq (z * w) = normSq z * normSq w :=
  int_four_sq z.re z.im w.re w.im

theorem normSq_eq_zero_iff (z : GaussInt) : normSq z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have ⟨hre, him⟩ := sum_two_sq_eq_zero (R := Int) h
    exact ext hre him
  · intro h
    subst h
    rfl

instance : IntegralDomain GaussInt where
  zero := 0
  one := 1
  add_assoc a b c := ext (Int.add_assoc _ _ _) (Int.add_assoc _ _ _)
  add_comm a b := ext (Int.add_comm _ _) (Int.add_comm _ _)
  zero_add a := ext (Int.zero_add _) (Int.zero_add _)
  add_zero a := ext (Int.add_zero _) (Int.add_zero _)
  neg_add_cancel a := ext (Int.add_left_neg _) (Int.add_left_neg _)
  sub_eq_add_neg _ _ := ext Int.sub_eq_add_neg Int.sub_eq_add_neg
  mul_assoc a b c := by
    apply ext
    · change (a.re * b.re - a.im * b.im) * c.re - (a.re * b.im + a.im * b.re) * c.im =
        a.re * (b.re * c.re - b.im * c.im) - a.im * (b.re * c.im + b.im * c.re)
      simp only [Int.sub_eq_add_neg, Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
        Int.neg_add, Int.neg_neg, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      omega
    · change (a.re * b.re - a.im * b.im) * c.im + (a.re * b.im + a.im * b.re) * c.re =
        a.re * (b.re * c.im + b.im * c.re) + a.im * (b.re * c.re - b.im * c.im)
      simp only [Int.sub_eq_add_neg, Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
        Int.neg_add, Int.neg_neg, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      omega
  mul_comm a b := by
    apply ext
    · change a.re * b.re - a.im * b.im = b.re * a.re - b.im * a.im
      rw [Int.mul_comm a.re b.re, Int.mul_comm a.im b.im]
    · change a.re * b.im + a.im * b.re = b.re * a.im + b.im * a.re
      rw [Int.mul_comm a.re b.im, Int.mul_comm a.im b.re, Int.add_comm]
  one_mul a := by
    apply ext
    · change 1 * a.re - 0 * a.im = a.re; omega
    · change 1 * a.im + 0 * a.re = a.im; omega
  mul_one a := by
    apply ext
    · change a.re * 1 - a.im * 0 = a.re; omega
    · change a.re * 0 + a.im * 1 = a.im; omega
  left_distrib a b c := by
    apply ext
    · change a.re * (b.re + c.re) - a.im * (b.im + c.im) =
        (a.re * b.re - a.im * b.im) + (a.re * c.re - a.im * c.im)
      simp only [Int.mul_add]; omega
    · change a.re * (b.im + c.im) + a.im * (b.re + c.re) =
        (a.re * b.im + a.im * b.re) + (a.re * c.im + a.im * c.re)
      simp only [Int.mul_add]; omega
  right_distrib a b c := by
    apply ext
    · change (a.re + b.re) * c.re - (a.im + b.im) * c.im =
        (a.re * c.re - a.im * c.im) + (b.re * c.re - b.im * c.im)
      simp only [Int.add_mul]; omega
    · change (a.re + b.re) * c.im + (a.im + b.im) * c.re =
        (a.re * c.im + a.im * c.re) + (b.re * c.im + b.im * c.re)
      simp only [Int.add_mul]; omega
  zero_ne_one := by decide
  mul_eq_zero a b h := by
    have hn : normSq (a * b) = 0 := by rw [h]; rfl
    rw [normSq_mul] at hn
    cases Int.mul_eq_zero.mp hn with
    | inl ha => exact Or.inl ((normSq_eq_zero_iff a).mp ha)
    | inr hb => exact Or.inr ((normSq_eq_zero_iff b).mp hb)

end GaussInt

/-- Finite prime field `𝔽_3 = Fin 3`. -/
abbrev F3 := Fin 3

/-- Finite prime field `𝔽_5 = Fin 5`. -/
abbrev F5 := Fin 5

instance : Neg F3 := ⟨fun x => 0 - x⟩
instance : Neg F5 := ⟨fun x => 0 - x⟩

instance : IntegralDomain F3 where
  zero := 0
  one := 1
  add_assoc := by decide
  add_comm := by decide
  zero_add := by decide
  add_zero := by decide
  neg_add_cancel := by decide
  sub_eq_add_neg := by decide
  mul_assoc := by decide
  mul_comm := by decide
  one_mul := by decide
  mul_one := by decide
  left_distrib := by decide
  right_distrib := by decide
  zero_ne_one := by decide
  mul_eq_zero := by decide

instance : IntegralDomain F5 where
  zero := 0
  one := 1
  add_assoc := by decide
  add_comm := by decide
  zero_add := by decide
  add_zero := by decide
  neg_add_cancel := by decide
  sub_eq_add_neg := by decide
  mul_assoc := by decide
  mul_comm := by decide
  one_mul := by decide
  mul_one := by decide
  left_distrib := by decide
  right_distrib := by decide
  zero_ne_one := by decide
  mul_eq_zero := by decide

end Conjecture00000007624
