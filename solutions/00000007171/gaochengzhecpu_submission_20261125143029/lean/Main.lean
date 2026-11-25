/-
  Conjecture 00000007171 — Core Lean 4.19.0 Formalization
  Title: Constrained Spectral Extrema with Fixed Trace:
         Schur-Convex Concentration vs. Multi-Regime Disproofs

  Zero external dependencies (Core Lean 4 only).
  Compiled with `-DwarningAsError=true`; zero `sorry`, `admit`, `native_decide`, or custom axioms.
-/

namespace Conjecture00000007171

/-! ## Section 1: Linearly Ordered Fields and Constructive Rational Field Witness -/

class HasOne (F : Type u) where
  one : F

instance {F : Type u} [HasOne F] : OfNat F 1 := ⟨HasOne.one⟩

class OrderedField (F : Type u) extends
    Add F, Sub F, Mul F, Neg F, Zero F, HasOne F, LE F, LT F where
  inv : F → F
  add_assoc : ∀ a b c : F, a + b + c = a + (b + c)
  add_comm : ∀ a b : F, a + b = b + a
  zero_add : ∀ a : F, 0 + a = a
  neg_add_cancel : ∀ a : F, -a + a = 0
  sub_eq_add_neg : ∀ a b : F, a - b = a + (-b)
  mul_assoc : ∀ a b c : F, a * b * c = a * (b * c)
  mul_comm : ∀ a b : F, a * b = b * a
  one_mul : ∀ a : F, 1 * a = a
  left_distrib : ∀ a b c : F, a * (b + c) = a * b + a * c
  zero_ne_one : (0 : F) ≠ 1
  inv_zero : inv 0 = 0
  mul_inv_cancel : ∀ a : F, a ≠ 0 → a * inv a = 1
  le_refl : ∀ a : F, a ≤ a
  le_trans : ∀ a b c : F, a ≤ b → b ≤ c → a ≤ c
  le_antisymm : ∀ a b : F, a ≤ b → b ≤ a → a = b
  le_total : ∀ a b : F, a ≤ b ∨ b ≤ a
  lt_iff_le_not_le : ∀ a b : F, a < b ↔ a ≤ b ∧ ¬ b ≤ a
  add_le_add_left : ∀ a b : F, a ≤ b → ∀ c : F, c + a ≤ c + b
  mul_pos : ∀ a b : F, 0 < a → 0 < b → 0 < a * b

section FieldLemmas

variable {F : Type u} [OrderedField F]

def fdiv (a b : F) : F := a * OrderedField.inv b

theorem add_zero_f (a : F) : a + 0 = a := by
  rw [OrderedField.add_comm, OrderedField.zero_add]

theorem add_neg_cancel_f (a : F) : a + (-a) = 0 := by
  rw [OrderedField.add_comm, OrderedField.neg_add_cancel]

theorem mul_one_f (a : F) : a * 1 = a := by
  rw [OrderedField.mul_comm, OrderedField.one_mul]

theorem right_distrib_f (a b c : F) : (a + b) * c = a * c + b * c := by
  rw [OrderedField.mul_comm, OrderedField.left_distrib, OrderedField.mul_comm c a,
      OrderedField.mul_comm c b]

theorem add_left_cancel_f {a b c : F} (h : a + b = a + c) : b = c := by
  have h1 : -a + (a + b) = -a + (a + c) := congrArg (fun x => -a + x) h
  rw [← OrderedField.add_assoc, ← OrderedField.add_assoc,
      OrderedField.neg_add_cancel, OrderedField.zero_add, OrderedField.zero_add] at h1
  exact h1

theorem add_right_cancel_f {a b c : F} (h : a + c = b + c) : a = b := by
  apply add_left_cancel_f (a := c)
  rw [OrderedField.add_comm c a, OrderedField.add_comm c b]
  exact h

theorem mul_zero_f (a : F) : a * 0 = 0 := by
  apply add_left_cancel_f (a := a * 0)
  rw [← OrderedField.left_distrib, add_zero_f, add_zero_f]

theorem zero_mul_f (a : F) : 0 * a = 0 := by
  rw [OrderedField.mul_comm, mul_zero_f]

theorem neg_eq_neg_one_mul_f (a : F) : -a = (-1 : F) * a := by
  apply add_left_cancel_f (a := a)
  rw [add_neg_cancel_f]
  have h : a + (-1 : F) * a = 1 * a + (-1 : F) * a := by rw [OrderedField.one_mul]
  rw [h, ← right_distrib_f, add_neg_cancel_f, zero_mul_f]

theorem neg_neg_f (a : F) : -(-a) = a := by
  apply add_left_cancel_f (a := -a)
  rw [add_neg_cancel_f, OrderedField.neg_add_cancel]

theorem neg_zero_f : -(0 : F) = 0 := by
  apply add_left_cancel_f (a := (0 : F))
  rw [add_neg_cancel_f, add_zero_f]

theorem neg_add_f (a b : F) : -(a + b) = -a + (-b) := by
  apply add_left_cancel_f (a := a + b)
  rw [add_neg_cancel_f]
  symm
  calc
    a + b + (-a + -b) = a + (b + (-b + -a)) := by
      rw [OrderedField.add_comm (-a) (-b), OrderedField.add_assoc]
    _ = a + (b + -b + -a) := by rw [← OrderedField.add_assoc b (-b) (-a)]
    _ = a + (0 + -a) := by rw [add_neg_cancel_f]
    _ = a + -a := by rw [OrderedField.zero_add]
    _ = 0 := add_neg_cancel_f a

theorem sub_self_f (a : F) : a - a = 0 := by
  rw [OrderedField.sub_eq_add_neg, add_neg_cancel_f]

theorem sub_zero_f (a : F) : a - 0 = a := by
  rw [OrderedField.sub_eq_add_neg, neg_zero_f, add_zero_f]

theorem zero_sub_f (a : F) : 0 - a = -a := by
  rw [OrderedField.sub_eq_add_neg, OrderedField.zero_add]

theorem neg_mul_f (a b : F) : (-a) * b = -(a * b) := by
  apply add_left_cancel_f (a := a * b)
  rw [← right_distrib_f, add_neg_cancel_f, zero_mul_f, add_neg_cancel_f]

theorem mul_neg_f (a b : F) : a * (-b) = -(a * b) := by
  rw [OrderedField.mul_comm, neg_mul_f, OrderedField.mul_comm]

theorem neg_mul_neg_f (a b : F) : (-a) * (-b) = a * b := by
  rw [neg_mul_f, mul_neg_f, neg_neg_f]

theorem mul_sub_f (a b c : F) : a * (b - c) = a * b - a * c := by
  rw [OrderedField.sub_eq_add_neg, OrderedField.left_distrib, mul_neg_f,
      ← OrderedField.sub_eq_add_neg]

theorem sub_mul_f (a b c : F) : (a - b) * c = a * c - b * c := by
  rw [OrderedField.sub_eq_add_neg, right_distrib_f, neg_mul_f,
      ← OrderedField.sub_eq_add_neg]

theorem inv_mul_cancel_f {a : F} (h : a ≠ 0) : OrderedField.inv a * a = 1 := by
  rw [OrderedField.mul_comm, OrderedField.mul_inv_cancel a h]

theorem mul_eq_zero_iff_f {a b : F} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      have h1 : OrderedField.inv a * (a * b) = OrderedField.inv a * 0 :=
        congrArg (fun x => OrderedField.inv a * x) h
      rw [← OrderedField.mul_assoc, inv_mul_cancel_f ha, OrderedField.one_mul, mul_zero_f] at h1
      exact h1
  · intro h
    cases h with
    | inl ha => rw [ha, zero_mul_f]
    | inr hb => rw [hb, mul_zero_f]

theorem lt_irrefl_f (a : F) : ¬ (a < a) := by
  rw [OrderedField.lt_iff_le_not_le]
  intro h
  exact h.2 h.1

theorem lt_of_lt_of_le_f {a b c : F} (hab : a < b) (hbc : b ≤ c) : a < c := by
  rw [OrderedField.lt_iff_le_not_le] at hab ⊢
  refine ⟨OrderedField.le_trans a b c hab.1 hbc, ?_⟩
  intro hca
  exact hab.2 (OrderedField.le_trans b c a hbc hca)

theorem lt_of_le_of_lt_f {a b c : F} (hab : a ≤ b) (hbc : b < c) : a < c := by
  rw [OrderedField.lt_iff_le_not_le] at hbc ⊢
  refine ⟨OrderedField.le_trans a b c hab hbc.1, ?_⟩
  intro hca
  exact hbc.2 (OrderedField.le_trans c a b hca hab)

theorem lt_trans_f {a b c : F} (hab : a < b) (hbc : b < c) : a < c := by
  rw [OrderedField.lt_iff_le_not_le] at hbc
  exact lt_of_lt_of_le_f hab hbc.1

theorem le_of_lt_f {a b : F} (h : a < b) : a ≤ b :=
  ((OrderedField.lt_iff_le_not_le a b).mp h).1

theorem ne_of_lt_f {a b : F} (h : a < b) : a ≠ b := by
  intro heq
  rw [heq] at h
  exact lt_irrefl_f b h

theorem lt_of_le_of_ne_f {a b : F} (hle : a ≤ b) (hne : a ≠ b) : a < b := by
  rw [OrderedField.lt_iff_le_not_le]
  refine ⟨hle, ?_⟩
  intro hba
  exact hne (OrderedField.le_antisymm a b hle hba)

theorem lt_trichotomy_f (a b : F) : a < b ∨ a = b ∨ b < a := by
  cases OrderedField.le_total a b with
  | inl hab =>
    by_cases heq : a = b
    · exact Or.inr (Or.inl heq)
    · exact Or.inl (lt_of_le_of_ne_f hab heq)
  | inr hba =>
    by_cases heq : a = b
    · exact Or.inr (Or.inl heq)
    · exact Or.inr (Or.inr (lt_of_le_of_ne_f hba (Ne.symm heq)))

theorem not_lt_iff_le_f {a b : F} : ¬ (a < b) ↔ b ≤ a := by
  rw [OrderedField.lt_iff_le_not_le]
  constructor
  · intro h
    cases OrderedField.le_total a b with
    | inl hab =>
      by_cases hba : b ≤ a
      · exact hba
      · exact False.elim (h ⟨hab, hba⟩)
    | inr hba => exact hba
  · intro hba h
    exact h.2 hba

theorem add_le_add_right_f {a b : F} (hab : a ≤ b) (c : F) : a + c ≤ b + c := by
  rw [OrderedField.add_comm a c, OrderedField.add_comm b c]
  exact OrderedField.add_le_add_left a b hab c

theorem add_le_add_f {a b c d : F} (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d :=
  OrderedField.le_trans (a + c) (b + c) (b + d)
    (add_le_add_right_f hab c) (OrderedField.add_le_add_left c d hcd b)

theorem add_lt_add_left_f {a b : F} (hab : a < b) (c : F) : c + a < c + b := by
  rw [OrderedField.lt_iff_le_not_le] at hab ⊢
  refine ⟨OrderedField.add_le_add_left a b hab.1 c, ?_⟩
  intro hba
  have h1 := OrderedField.add_le_add_left (c + b) (c + a) hba (-c)
  rw [← OrderedField.add_assoc, ← OrderedField.add_assoc,
      OrderedField.neg_add_cancel, OrderedField.zero_add, OrderedField.zero_add] at h1
  exact hab.2 h1

theorem add_lt_add_right_f {a b : F} (hab : a < b) (c : F) : a + c < b + c := by
  rw [OrderedField.add_comm a c, OrderedField.add_comm b c]
  exact add_lt_add_left_f hab c

theorem add_lt_add_of_lt_of_le_f {a b c d : F} (hab : a < b) (hcd : c ≤ d) : a + c < b + d :=
  lt_of_lt_of_le_f (add_lt_add_right_f hab c) (OrderedField.add_le_add_left c d hcd b)

theorem add_lt_add_of_le_of_lt_f {a b c d : F} (hab : a ≤ b) (hcd : c < d) : a + c < b + d :=
  lt_of_le_of_lt_f (add_le_add_right_f hab c) (add_lt_add_left_f hcd b)

theorem sub_nonneg_iff_f {a b : F} : 0 ≤ b - a ↔ a ≤ b := by
  constructor
  · intro h
    have h1 := OrderedField.add_le_add_left 0 (b - a) h a
    rw [add_zero_f, OrderedField.sub_eq_add_neg, OrderedField.add_comm b (-a),
        ← OrderedField.add_assoc, add_neg_cancel_f, OrderedField.zero_add] at h1
    exact h1
  · intro h
    have h1 := add_le_add_right_f h (-a)
    rw [add_neg_cancel_f, ← OrderedField.sub_eq_add_neg] at h1
    exact h1

theorem sub_pos_iff_f {a b : F} : 0 < b - a ↔ a < b := by
  constructor
  · intro h
    have h1 := add_lt_add_left_f h a
    rw [add_zero_f, OrderedField.sub_eq_add_neg, OrderedField.add_comm b (-a),
        ← OrderedField.add_assoc, add_neg_cancel_f, OrderedField.zero_add] at h1
    exact h1
  · intro h
    have h1 := add_lt_add_right_f h (-a)
    rw [add_neg_cancel_f, ← OrderedField.sub_eq_add_neg] at h1
    exact h1

theorem neg_nonneg_iff_f {a : F} : 0 ≤ -a ↔ a ≤ 0 := by
  have h := sub_nonneg_iff_f (a := a) (b := 0)
  rw [zero_sub_f] at h
  exact h

theorem neg_pos_iff_f {a : F} : 0 < -a ↔ a < 0 := by
  have h := sub_pos_iff_f (a := a) (b := 0)
  rw [zero_sub_f] at h
  exact h

theorem mul_nonneg_f {a b : F} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  by_cases ha0 : a = 0
  · rw [ha0, zero_mul_f]; exact OrderedField.le_refl 0
  · by_cases hb0 : b = 0
    · rw [hb0, mul_zero_f]; exact OrderedField.le_refl 0
    · exact le_of_lt_f (OrderedField.mul_pos a b
        (lt_of_le_of_ne_f ha (Ne.symm ha0))
        (lt_of_le_of_ne_f hb (Ne.symm hb0)))

theorem mul_le_mul_of_nonneg_left_f {a b c : F} (hab : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by
  rw [← sub_nonneg_iff_f, ← mul_sub_f]
  exact mul_nonneg_f hc (sub_nonneg_iff_f.mpr hab)

theorem mul_le_mul_of_nonneg_right_f {a b c : F} (hab : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  rw [OrderedField.mul_comm a c, OrderedField.mul_comm b c]
  exact mul_le_mul_of_nonneg_left_f hab hc

theorem mul_lt_mul_of_pos_left_f {a b c : F} (hab : a < b) (hc : 0 < c) : c * a < c * b := by
  rw [← sub_pos_iff_f, ← mul_sub_f]
  exact OrderedField.mul_pos c (b - a) hc (sub_pos_iff_f.mpr hab)

theorem mul_lt_mul_of_pos_right_f {a b c : F} (hab : a < b) (hc : 0 < c) : a * c < b * c := by
  rw [OrderedField.mul_comm a c, OrderedField.mul_comm b c]
  exact mul_lt_mul_of_pos_left_f hab hc

theorem sq_nonneg_f (a : F) : 0 ≤ a * a := by
  cases OrderedField.le_total 0 a with
  | inl ha => exact mul_nonneg_f ha ha
  | inr ha =>
    have hna : 0 ≤ -a := neg_nonneg_iff_f.mpr ha
    have h := mul_nonneg_f hna hna
    rw [neg_mul_neg_f] at h
    exact h

theorem sq_pos_of_ne_zero_f {a : F} (h : a ≠ 0) : 0 < a * a := by
  cases lt_trichotomy_f 0 a with
  | inl hpos => exact OrderedField.mul_pos a a hpos hpos
  | inr hrest =>
    cases hrest with
    | inl heq => exact False.elim (h heq.symm)
    | inr hneg =>
      have hn : 0 < -a := neg_pos_iff_f.mpr hneg
      have hp := OrderedField.mul_pos (-a) (-a) hn hn
      rw [neg_mul_neg_f] at hp
      exact hp

theorem zero_lt_one_f : (0 : F) < 1 := by
  have h := sq_pos_of_ne_zero_f (Ne.symm (OrderedField.zero_ne_one (F := F)))
  rw [OrderedField.one_mul] at h
  exact h

theorem zero_le_one_f : (0 : F) ≤ 1 := le_of_lt_f zero_lt_one_f

theorem inv_pos_f {a : F} (ha : 0 < a) : 0 < OrderedField.inv a := by
  have hne : a ≠ 0 := Ne.symm (ne_of_lt_f ha)
  cases lt_trichotomy_f 0 (OrderedField.inv a) with
  | inl hp => exact hp
  | inr hr =>
    cases hr with
    | inl hz =>
      have h1 : a * OrderedField.inv a = 1 := OrderedField.mul_inv_cancel a hne
      rw [← hz, mul_zero_f] at h1
      exact False.elim (OrderedField.zero_ne_one h1)
    | inr hn =>
      have hpos := OrderedField.mul_pos a (-OrderedField.inv a) ha (neg_pos_iff_f.mpr hn)
      rw [mul_neg_f, OrderedField.mul_inv_cancel a hne] at hpos
      have h1lt0 : (1 : F) < 0 := neg_pos_iff_f.mp hpos
      exact False.elim (lt_irrefl_f 0 (lt_trans_f zero_lt_one_f h1lt0))

theorem inv_nonneg_f {a : F} (ha : 0 ≤ a) : 0 ≤ OrderedField.inv a := by
  by_cases hz : a = 0
  · rw [hz, OrderedField.inv_zero]; exact OrderedField.le_refl 0
  · exact le_of_lt_f (inv_pos_f (lt_of_le_of_ne_f ha (Ne.symm hz)))

def ofNatF : Nat → F
  | 0 => 0
  | n + 1 => ofNatF n + 1

theorem ofNatF_add (m n : Nat) : (ofNatF (m + n) : F) = ofNatF m + ofNatF n := by
  induction n with
  | zero => simp [ofNatF, add_zero_f]
  | succ n ih =>
    simp [Nat.add_succ, ofNatF, ih, OrderedField.add_assoc]

theorem ofNatF_mul (m n : Nat) : (ofNatF (m * n) : F) = ofNatF m * ofNatF n := by
  induction n with
  | zero => simp [ofNatF, mul_zero_f]
  | succ n ih =>
    rw [Nat.mul_succ, ofNatF_add, ih]
    simp [ofNatF, OrderedField.left_distrib, mul_one_f]

theorem ofNatF_nonneg (n : Nat) : (0 : F) ≤ ofNatF n := by
  induction n with
  | zero => exact OrderedField.le_refl 0
  | succ n ih =>
    simpa [ofNatF, add_zero_f] using add_le_add_f ih zero_le_one_f

theorem ofNatF_pos {n : Nat} (hn : 0 < n) : (0 : F) < ofNatF n := by
  cases n with
  | zero => omega
  | succ k =>
    have hk : (0 : F) ≤ ofNatF k := ofNatF_nonneg k
    have h1 : (0 : F) + 0 < ofNatF k + 1 := add_lt_add_of_le_of_lt_f hk zero_lt_one_f
    rw [add_zero_f] at h1
    exact h1

theorem ofNatF_ne_zero {n : Nat} (hn : 0 < n) : (ofNatF n : F) ≠ 0 :=
  Ne.symm (ne_of_lt_f (ofNatF_pos hn))

theorem ofNatF_strictMono {m n : Nat} (h : m < n) : (ofNatF m : F) < ofNatF n := by
  have hd : 0 < n - m := by omega
  have heq : n = m + (n - m) := by omega
  rw [heq, ofNatF_add]
  have hp : (0 : F) < ofNatF (n - m) := ofNatF_pos hd
  have h1 := add_lt_add_left_f hp (ofNatF m)
  rw [add_zero_f] at h1
  exact h1

def fpow (x : F) : Nat → F
  | 0 => 1
  | k + 1 => fpow x k * x

theorem fpow_nonneg {x : F} (hx : 0 ≤ x) (k : Nat) : 0 ≤ fpow x k := by
  induction k with
  | zero => exact zero_le_one_f
  | succ k ih => exact mul_nonneg_f ih hx

theorem fpow_pos {x : F} (hx : 0 < x) (k : Nat) : 0 < fpow x k := by
  induction k with
  | zero => exact zero_lt_one_f
  | succ k ih => exact OrderedField.mul_pos _ _ ih hx

/-- Bernoulli's inequality `(1 + x)^k ≥ 1 + k x` for `0 ≤ 1 + x`, with strictness for `k ≥ 2`, `x ≠ 0`, `0 < 1 + x`. -/
theorem bernoulli_ge {x : F} (hx : 0 ≤ 1 + x) (k : Nat) :
    1 + ofNatF k * x ≤ fpow (1 + x) k := by
  induction k with
  | zero =>
    simp [ofNatF, fpow, zero_mul_f, add_zero_f]
    exact OrderedField.le_refl 1
  | succ k ih =>
    have hmul : (1 + ofNatF k * x) * (1 + x) ≤ fpow (1 + x) k * (1 + x) :=
      mul_le_mul_of_nonneg_right_f ih hx
    have hexpand :
        (1 + ofNatF k * x) * (1 + x) =
          (1 + ofNatF (k + 1) * x) + ofNatF k * (x * x) := by
      calc
        (1 + ofNatF k * x) * (1 + x)
            = 1 * (1 + x) + (ofNatF k * x) * (1 + x) := right_distrib_f _ _ _
        _ = (1 + x) + ((ofNatF k * x) * 1 + (ofNatF k * x) * x) := by
              rw [OrderedField.one_mul, OrderedField.left_distrib]
        _ = 1 + (x + ofNatF k * x) + ofNatF k * (x * x) := by
              rw [mul_one_f, OrderedField.mul_assoc (ofNatF k) x x,
                  OrderedField.add_assoc 1 x _,
                  ← OrderedField.add_assoc x (ofNatF k * x) _,
                  ← OrderedField.add_assoc 1 _ _]
        _ = (1 + ofNatF (k + 1) * x) + ofNatF k * (x * x) := by
              have hk1 : ofNatF (k + 1) * x = x + ofNatF k * x := by
                simp [ofNatF, right_distrib_f, OrderedField.one_mul, OrderedField.add_comm]
              rw [hk1]
    have hrem : 0 ≤ ofNatF k * (x * x) := mul_nonneg_f (ofNatF_nonneg k) (sq_nonneg_f x)
    have hlo : 1 + ofNatF (k + 1) * x ≤ (1 + ofNatF k * x) * (1 + x) := by
      rw [hexpand]
      have hstep := OrderedField.add_le_add_left 0 (ofNatF k * (x * x)) hrem (1 + ofNatF (k + 1) * x)
      rw [add_zero_f] at hstep
      exact hstep
    exact OrderedField.le_trans _ _ _ hlo hmul

theorem bernoulli_strict {x : F} (hx : 0 < 1 + x) (hxne : x ≠ 0) {k : Nat} (hk : 2 ≤ k) :
    1 + ofNatF k * x < fpow (1 + x) k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hbase : 1 + ofNatF (m + 1) * x ≤ fpow (1 + x) (m + 1) :=
    bernoulli_ge (le_of_lt_f hx) (m + 1)
  have hmul : (1 + ofNatF (m + 1) * x) * (1 + x) ≤ fpow (1 + x) (m + 1) * (1 + x) :=
    mul_le_mul_of_nonneg_right_f hbase (le_of_lt_f hx)
  have hexpand :
      (1 + ofNatF (m + 1) * x) * (1 + x) =
        (1 + ofNatF (m + 2) * x) + ofNatF (m + 1) * (x * x) := by
    calc
      (1 + ofNatF (m + 1) * x) * (1 + x)
          = 1 * (1 + x) + (ofNatF (m + 1) * x) * (1 + x) := right_distrib_f _ _ _
      _ = (1 + x) + ((ofNatF (m + 1) * x) * 1 + (ofNatF (m + 1) * x) * x) := by
            rw [OrderedField.one_mul, OrderedField.left_distrib]
      _ = 1 + (x + ofNatF (m + 1) * x) + ofNatF (m + 1) * (x * x) := by
            rw [mul_one_f, OrderedField.mul_assoc (ofNatF (m + 1)) x x,
                OrderedField.add_assoc 1 x _,
                ← OrderedField.add_assoc x (ofNatF (m + 1) * x) _,
                ← OrderedField.add_assoc 1 _ _]
      _ = (1 + ofNatF (m + 2) * x) + ofNatF (m + 1) * (x * x) := by
            have hm2 : ofNatF (m + 2) * x = x + ofNatF (m + 1) * x := by
              change (ofNatF (m + 1) + 1) * x = x + ofNatF (m + 1) * x
              rw [right_distrib_f, OrderedField.one_mul, OrderedField.add_comm]
            rw [hm2]
  have hpos_rem : 0 < ofNatF (m + 1) * (x * x) :=
    OrderedField.mul_pos _ _ (ofNatF_pos (by omega)) (sq_pos_of_ne_zero_f hxne)
  have hlt : 1 + ofNatF (m + 2) * x < (1 + ofNatF (m + 1) * x) * (1 + x) := by
    rw [hexpand]
    have hstep := add_lt_add_left_f hpos_rem (1 + ofNatF (m + 2) * x)
    rw [add_zero_f] at hstep
    exact hstep
  exact lt_of_lt_of_le_f hlt hmul

end FieldLemmas

/-! ### Constructive Quotient Model `RatField` of `OrderedField` -/

abbrev RatRaw := { p : Int × Int // 0 < p.2 }

def ratRel (x y : RatRaw) : Prop := x.1.1 * y.1.2 = y.1.1 * x.1.2

private theorem int_mul_right_cancel_pos {a b d : Int} (hd : 0 < d) (h : a * d = b * d) : a = b := by
  by_cases hlt : a < b
  · have hpos : 0 < (b - a) * d := Int.mul_pos (by omega) hd
    rw [Int.sub_mul, h] at hpos
    omega
  · by_cases hgt : b < a
    · have hpos : 0 < (a - b) * d := Int.mul_pos (by omega) hd
      rw [Int.sub_mul, h] at hpos
      omega
    · omega

private theorem ratRel_refl (x : RatRaw) : ratRel x x := rfl

private theorem ratRel_symm {x y : RatRaw} (h : ratRel x y) : ratRel y x := h.symm

private theorem ratRel_trans {x y z : RatRaw} (hxy : ratRel x y) (hyz : ratRel y z) :
    ratRel x z := by
  unfold ratRel at *
  apply int_mul_right_cancel_pos y.2
  calc
    (x.1.1 * z.1.2) * y.1.2 = (x.1.1 * y.1.2) * z.1.2 := by
      rw [Int.mul_assoc, Int.mul_comm z.1.2 y.1.2, ← Int.mul_assoc]
    _ = (y.1.1 * x.1.2) * z.1.2 := by rw [hxy]
    _ = (y.1.1 * z.1.2) * x.1.2 := by
      rw [Int.mul_assoc, Int.mul_comm x.1.2 z.1.2, ← Int.mul_assoc]
    _ = (z.1.1 * y.1.2) * x.1.2 := by rw [hyz]
    _ = (z.1.1 * x.1.2) * y.1.2 := by
      rw [Int.mul_assoc, Int.mul_comm y.1.2 x.1.2, ← Int.mul_assoc]

instance ratSetoid : Setoid RatRaw where
  r := ratRel
  iseqv := ⟨ratRel_refl, ratRel_symm, ratRel_trans⟩

abbrev RatField := Quotient ratSetoid

private def ratAddRaw (x y : RatRaw) : RatRaw :=
  ⟨(x.1.1 * y.1.2 + y.1.1 * x.1.2, x.1.2 * y.1.2), Int.mul_pos x.2 y.2⟩

private def ratNegRaw (x : RatRaw) : RatRaw :=
  ⟨(-x.1.1, x.1.2), x.2⟩

private def ratMulRaw (x y : RatRaw) : RatRaw :=
  ⟨(x.1.1 * y.1.1, x.1.2 * y.1.2), Int.mul_pos x.2 y.2⟩

private def ratInvRaw (x : RatRaw) : RatRaw :=
  if hpos : 0 < x.1.1 then
    ⟨(x.1.2, x.1.1), hpos⟩
  else if hneg : x.1.1 < 0 then
    ⟨(-x.1.2, -x.1.1), by omega⟩
  else
    ⟨(0, 1), by omega⟩

private theorem int_ring_add_wd (a1 b1 a2 b2 c1 d1 c2 d2 : Int)
    (h1 : a1 * b2 = a2 * b1) (h2 : c1 * d2 = c2 * d1) :
    (a1 * d1 + c1 * b1) * (b2 * d2) = (a2 * d2 + c2 * b2) * (b1 * d1) := by
  have p1 : (a1 * d1) * (b2 * d2) = (a2 * d2) * (b1 * d1) := by
    calc
      (a1 * d1) * (b2 * d2) = (a1 * b2) * (d1 * d2) := by
        rw [Int.mul_assoc, ← Int.mul_assoc d1 b2 d2, Int.mul_comm d1 b2,
            Int.mul_assoc b2 d1 d2, ← Int.mul_assoc]
      _ = (a2 * b1) * (d2 * d1) := by rw [h1, Int.mul_comm d1 d2]
      _ = (a2 * d2) * (b1 * d1) := by
        rw [Int.mul_assoc, ← Int.mul_assoc b1 d2 d1, Int.mul_comm b1 d2,
            Int.mul_assoc d2 b1 d1, ← Int.mul_assoc]
  have p2 : (c1 * b1) * (b2 * d2) = (c2 * b2) * (b1 * d1) := by
    calc
      (c1 * b1) * (b2 * d2) = (c1 * d2) * (b1 * b2) := by
        rw [Int.mul_assoc, Int.mul_comm b2 d2, ← Int.mul_assoc b1 d2 b2,
            Int.mul_comm b1 d2, Int.mul_assoc d2 b1 b2, ← Int.mul_assoc]
      _ = (c2 * d1) * (b2 * b1) := by rw [h2, Int.mul_comm b1 b2]
      _ = (c2 * b2) * (b1 * d1) := by
        rw [Int.mul_assoc, ← Int.mul_assoc d1 b2 b1, Int.mul_comm d1 b2,
            Int.mul_assoc b2 d1 b1, Int.mul_comm d1 b1, ← Int.mul_assoc]
  rw [Int.add_mul, Int.add_mul, p1, p2]

private theorem int_ring_mul_wd (a1 b1 a2 b2 c1 d1 c2 d2 : Int)
    (h1 : a1 * b2 = a2 * b1) (h2 : c1 * d2 = c2 * d1) :
    (a1 * c1) * (b2 * d2) = (a2 * c2) * (b1 * d1) := by
  calc
    (a1 * c1) * (b2 * d2) = (a1 * b2) * (c1 * d2) := by
      rw [Int.mul_assoc, ← Int.mul_assoc c1 b2 d2, Int.mul_comm c1 b2,
          Int.mul_assoc b2 c1 d2, ← Int.mul_assoc]
    _ = (a2 * b1) * (c2 * d1) := by rw [h1, h2]
    _ = (a2 * c2) * (b1 * d1) := by
      rw [Int.mul_assoc, ← Int.mul_assoc b1 c2 d1, Int.mul_comm b1 c2,
          Int.mul_assoc c2 b1 d1, ← Int.mul_assoc]

private theorem ratInvRaw_wd {x y : RatRaw} (h : ratRel x y) :
    ratRel (ratInvRaw x) (ratInvRaw y) := by
  unfold ratRel ratInvRaw at *
  have hxpos := x.2
  have hypos := y.2
  by_cases hx1 : 0 < x.1.1
  · have hy1 : 0 < y.1.1 := by
      have hp : 0 < x.1.1 * y.1.2 := Int.mul_pos hx1 hypos
      rw [h] at hp
      by_cases hy_le : y.1.1 ≤ 0
      · have hnp : y.1.1 * x.1.2 ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg hy_le (by omega)
        omega
      · omega
    simp [hx1, hy1]
    rw [Int.mul_comm x.1.2 y.1.1, ← h, Int.mul_comm]
  · by_cases hx2 : x.1.1 < 0
    · have hy2 : y.1.1 < 0 := by
        have hn : x.1.1 * y.1.2 < 0 := Int.mul_neg_of_neg_of_pos hx2 hypos
        rw [h] at hn
        by_cases hy_ge : 0 ≤ y.1.1
        · have hnn : 0 ≤ y.1.1 * x.1.2 := Int.mul_nonneg hy_ge (by omega)
          omega
        · omega
      have hy1 : ¬ (0 < y.1.1) := by omega
      simp [hx1, hx2, hy1, hy2]
      calc
        (-x.1.2) * (-y.1.1) = x.1.2 * y.1.1 := by rw [Int.neg_mul_neg]
        _ = y.1.1 * x.1.2 := Int.mul_comm _ _
        _ = x.1.1 * y.1.2 := h.symm
        _ = y.1.2 * x.1.1 := Int.mul_comm _ _
        _ = (-y.1.2) * (-x.1.1) := by rw [Int.neg_mul_neg]
    · have hxz : x.1.1 = 0 := by omega
      have hyz : y.1.1 = 0 := by
        apply int_mul_right_cancel_pos hxpos
        rw [Int.zero_mul, ← h, hxz, Int.zero_mul]
      have hy1 : ¬ (0 < y.1.1) := by omega
      have hy2 : ¬ (y.1.1 < 0) := by omega
      simp [hx1, hx2, hy1, hy2]

def ratAdd : RatField → RatField → RatField :=
  Quotient.lift₂ (fun x y => Quotient.mk _ (ratAddRaw x y)) (fun _ _ _ _ hx hy =>
    Quotient.sound (int_ring_add_wd _ _ _ _ _ _ _ _ hx hy))

def ratNeg : RatField → RatField :=
  Quotient.lift (fun x => Quotient.mk _ (ratNegRaw x)) (fun _ _ hx =>
    Quotient.sound (by
      change ratRel _ _ at *
      unfold ratRel ratNegRaw at *
      rw [Int.neg_mul, Int.neg_mul, hx]))

def ratMul : RatField → RatField → RatField :=
  Quotient.lift₂ (fun x y => Quotient.mk _ (ratMulRaw x y)) (fun _ _ _ _ hx hy =>
    Quotient.sound (int_ring_mul_wd _ _ _ _ _ _ _ _ hx hy))

def ratInv : RatField → RatField :=
  Quotient.lift (fun x => Quotient.mk _ (ratInvRaw x)) (fun _ _ hx =>
    Quotient.sound (ratInvRaw_wd hx))

private def ratLERaw (x y : RatRaw) : Prop := x.1.1 * y.1.2 ≤ y.1.1 * x.1.2

private theorem int_le_of_mul_le_pos {a b d : Int} (hd : 0 < d) (h : a * d ≤ b * d) : a ≤ b := by
  by_cases hgt : b < a
  · have hp : 0 < (a - b) * d := Int.mul_pos (by omega) hd
    rw [Int.sub_mul] at hp
    omega
  · omega

private theorem ratLERaw_wd {x1 y1 x2 y2 : RatRaw} (hx : ratRel x1 x2) (hy : ratRel y1 y2) :
    ratLERaw x1 y1 = ratLERaw x2 y2 := by
  apply propext
  unfold ratLERaw ratRel at *
  constructor
  · intro h
    apply int_le_of_mul_le_pos (Int.mul_pos x1.2 y1.2)
    have h1 : (x1.1.1 * y1.1.2) * (x2.1.2 * y2.1.2) ≤ (y1.1.1 * x1.1.2) * (x2.1.2 * y2.1.2) :=
      Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt (Int.mul_pos x2.2 y2.2))
    have lhs_eq : (x1.1.1 * y1.1.2) * (x2.1.2 * y2.1.2) = (x2.1.1 * y2.1.2) * (x1.1.2 * y1.1.2) := by
      calc
        (x1.1.1 * y1.1.2) * (x2.1.2 * y2.1.2) = (x1.1.1 * x2.1.2) * (y1.1.2 * y2.1.2) := by
          rw [Int.mul_assoc, ← Int.mul_assoc y1.1.2 x2.1.2 y2.1.2, Int.mul_comm y1.1.2 x2.1.2,
              Int.mul_assoc x2.1.2 y1.1.2 y2.1.2, ← Int.mul_assoc]
        _ = (x2.1.1 * x1.1.2) * (y2.1.2 * y1.1.2) := by rw [hx, Int.mul_comm y1.1.2 y2.1.2]
        _ = (x2.1.1 * y2.1.2) * (x1.1.2 * y1.1.2) := by
          rw [Int.mul_assoc, ← Int.mul_assoc x1.1.2 y2.1.2 y1.1.2, Int.mul_comm x1.1.2 y2.1.2,
              Int.mul_assoc y2.1.2 x1.1.2 y1.1.2, ← Int.mul_assoc]
    have rhs_eq : (y1.1.1 * x1.1.2) * (x2.1.2 * y2.1.2) = (y2.1.1 * x2.1.2) * (x1.1.2 * y1.1.2) := by
      calc
        (y1.1.1 * x1.1.2) * (x2.1.2 * y2.1.2) = (y1.1.1 * y2.1.2) * (x1.1.2 * x2.1.2) := by
          rw [Int.mul_assoc, Int.mul_comm x2.1.2 y2.1.2, ← Int.mul_assoc x1.1.2 y2.1.2 x2.1.2,
              Int.mul_comm x1.1.2 y2.1.2, Int.mul_assoc y2.1.2 x1.1.2 x2.1.2, ← Int.mul_assoc]
        _ = (y2.1.1 * y1.1.2) * (x2.1.2 * x1.1.2) := by rw [hy, Int.mul_comm x1.1.2 x2.1.2]
        _ = (y2.1.1 * x2.1.2) * (x1.1.2 * y1.1.2) := by
          rw [Int.mul_assoc, ← Int.mul_assoc y1.1.2 x2.1.2 x1.1.2, Int.mul_comm y1.1.2 x2.1.2,
              Int.mul_assoc x2.1.2 y1.1.2 x1.1.2, Int.mul_comm y1.1.2 x1.1.2, ← Int.mul_assoc]
    rw [lhs_eq, rhs_eq] at h1
    exact h1
  · intro h
    apply int_le_of_mul_le_pos (Int.mul_pos x2.2 y2.2)
    have h1 : (x2.1.1 * y2.1.2) * (x1.1.2 * y1.1.2) ≤ (y2.1.1 * x2.1.2) * (x1.1.2 * y1.1.2) :=
      Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt (Int.mul_pos x1.2 y1.2))
    have lhs_eq : (x2.1.1 * y2.1.2) * (x1.1.2 * y1.1.2) = (x1.1.1 * y1.1.2) * (x2.1.2 * y2.1.2) := by
      calc
        (x2.1.1 * y2.1.2) * (x1.1.2 * y1.1.2) = (x2.1.1 * x1.1.2) * (y2.1.2 * y1.1.2) := by
          rw [Int.mul_assoc, ← Int.mul_assoc y2.1.2 x1.1.2 y1.1.2, Int.mul_comm y2.1.2 x1.1.2,
              Int.mul_assoc x1.1.2 y2.1.2 y1.1.2, ← Int.mul_assoc]
        _ = (x1.1.1 * x2.1.2) * (y1.1.2 * y2.1.2) := by rw [← hx, Int.mul_comm y2.1.2 y1.1.2]
        _ = (x1.1.1 * y1.1.2) * (x2.1.2 * y2.1.2) := by
          rw [Int.mul_assoc, ← Int.mul_assoc x2.1.2 y1.1.2 y2.1.2, Int.mul_comm x2.1.2 y1.1.2,
              Int.mul_assoc y1.1.2 x2.1.2 y2.1.2, ← Int.mul_assoc]
    have rhs_eq : (y2.1.1 * x2.1.2) * (x1.1.2 * y1.1.2) = (y1.1.1 * x1.1.2) * (x2.1.2 * y2.1.2) := by
      calc
        (y2.1.1 * x2.1.2) * (x1.1.2 * y1.1.2) = (y2.1.1 * y1.1.2) * (x2.1.2 * x1.1.2) := by
          rw [Int.mul_assoc, Int.mul_comm x1.1.2 y1.1.2, ← Int.mul_assoc x2.1.2 y1.1.2 x1.1.2,
              Int.mul_comm x2.1.2 y1.1.2, Int.mul_assoc y1.1.2 x2.1.2 x1.1.2, ← Int.mul_assoc]
        _ = (y1.1.1 * y2.1.2) * (x1.1.2 * x2.1.2) := by rw [← hy, Int.mul_comm x2.1.2 x1.1.2]
        _ = (y1.1.1 * x1.1.2) * (x2.1.2 * y2.1.2) := by
          rw [Int.mul_assoc, ← Int.mul_assoc y2.1.2 x1.1.2 x2.1.2, Int.mul_comm y2.1.2 x1.1.2,
              Int.mul_assoc x1.1.2 y2.1.2 x2.1.2, Int.mul_comm y2.1.2 x2.1.2, ← Int.mul_assoc]
    rw [lhs_eq, rhs_eq] at h1
    exact h1

def ratLE : RatField → RatField → Prop :=
  Quotient.lift₂ ratLERaw (fun _ _ _ _ hx hy => ratLERaw_wd hx hy)

instance : Zero RatField   := ⟨Quotient.mk _ ⟨(0, 1), by omega⟩⟩
instance : HasOne RatField := ⟨Quotient.mk _ ⟨(1, 1), by omega⟩⟩
instance : Add RatField  := ⟨ratAdd⟩
instance : Neg RatField  := ⟨ratNeg⟩
instance : Sub RatField  := ⟨fun a b => ratAdd a (ratNeg b)⟩
instance : Mul RatField  := ⟨ratMul⟩
instance : LE RatField   := ⟨ratLE⟩
instance : LT RatField   := ⟨fun a b => ratLE a b ∧ ¬ ratLE b a⟩

instance instOrderedFieldRat : OrderedField RatField where
  inv := ratInv
  add_assoc := by
    intro a b c
    refine Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound ?_)
    change ratRel _ _
    unfold ratRel ratAddRaw
    simp only []
    rw [← Int.mul_assoc x.1.2 y.1.2 z.1.2]
    apply congrArg (fun u => u * (x.1.2 * y.1.2 * z.1.2))
    rw [Int.add_mul, Int.add_mul, Int.mul_assoc x.1.1 y.1.2 z.1.2, Int.add_assoc]
    apply congrArg (fun u => x.1.1 * (y.1.2 * z.1.2) + u)
    have p1 : y.1.1 * x.1.2 * z.1.2 = y.1.1 * z.1.2 * x.1.2 := by
      rw [Int.mul_assoc, Int.mul_comm x.1.2 z.1.2, ← Int.mul_assoc]
    have p2 : z.1.1 * (x.1.2 * y.1.2) = z.1.1 * y.1.2 * x.1.2 := by
      rw [Int.mul_comm x.1.2 y.1.2, ← Int.mul_assoc]
    rw [p1, p2]
  add_comm := by
    intro a b
    refine Quotient.inductionOn₂ a b (fun x y => Quotient.sound ?_)
    change ratRel _ _
    unfold ratRel ratAddRaw
    simp only []
    rw [Int.add_comm (x.1.1 * y.1.2), Int.mul_comm y.1.2 x.1.2]
  zero_add := by
    intro a
    refine Quotient.inductionOn a (fun x => Quotient.sound ?_)
    change ratRel _ _
    unfold ratRel ratAddRaw
    simp [Int.zero_mul, Int.one_mul, Int.mul_one, Int.zero_add]
  neg_add_cancel := by
    intro a
    refine Quotient.inductionOn a (fun x => Quotient.sound ?_)
    change ratRel _ _
    unfold ratRel ratAddRaw ratNegRaw
    simp [Int.neg_mul, Int.add_left_neg, Int.zero_mul, Int.mul_one]
  sub_eq_add_neg := fun _ _ => rfl
  mul_assoc := by
    intro a b c
    refine Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound ?_)
    change ratRel _ _
    unfold ratRel ratMulRaw
    simp [Int.mul_assoc]
  mul_comm := by
    intro a b
    refine Quotient.inductionOn₂ a b (fun x y => Quotient.sound ?_)
    change ratRel _ _
    unfold ratRel ratMulRaw
    simp [Int.mul_comm]
  one_mul := by
    intro a
    refine Quotient.inductionOn a (fun x => Quotient.sound ?_)
    change ratRel _ _
    unfold ratRel ratMulRaw
    simp [Int.one_mul]
  left_distrib := by
    intro a b c
    refine Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound ?_)
    change ratRel _ _
    unfold ratRel ratMulRaw ratAddRaw
    simp only []
    have d_eq : x.1.2 * y.1.2 * (x.1.2 * z.1.2) = x.1.2 * (x.1.2 * (y.1.2 * z.1.2)) := by
      rw [← Int.mul_assoc (x.1.2 * y.1.2) x.1.2 z.1.2,
          Int.mul_comm (x.1.2 * y.1.2) x.1.2,
          Int.mul_assoc x.1.2 (x.1.2 * y.1.2) z.1.2,
          Int.mul_assoc x.1.2 y.1.2 z.1.2]
    calc
      x.1.1 * (y.1.1 * z.1.2 + z.1.1 * y.1.2) * (x.1.2 * y.1.2 * (x.1.2 * z.1.2))
          = (x.1.1 * y.1.1 * z.1.2 + x.1.1 * z.1.1 * y.1.2) * x.1.2 *
              (x.1.2 * (y.1.2 * z.1.2)) := by
            rw [Int.mul_add, ← Int.mul_assoc x.1.1 y.1.1 z.1.2,
                ← Int.mul_assoc x.1.1 z.1.1 y.1.2, d_eq, ← Int.mul_assoc]
      _ = (x.1.1 * y.1.1 * (x.1.2 * z.1.2) + x.1.1 * z.1.1 * (x.1.2 * y.1.2)) *
            (x.1.2 * (y.1.2 * z.1.2)) := by
            apply congrArg (fun u => u * (x.1.2 * (y.1.2 * z.1.2)))
            rw [Int.add_mul, Int.mul_assoc (x.1.1 * y.1.1) z.1.2 x.1.2,
                Int.mul_comm z.1.2 x.1.2,
                Int.mul_assoc (x.1.1 * z.1.1) y.1.2 x.1.2,
                Int.mul_comm y.1.2 x.1.2]
  zero_ne_one := by
    intro h
    have h1 : ratRel ⟨(0, 1), by omega⟩ ⟨(1, 1), by omega⟩ := Quotient.exact h
    unfold ratRel at h1
    simp only [] at h1
    omega
  inv_zero := by
    apply Quotient.sound
    change ratRel _ _
    unfold ratRel ratInvRaw
    simp
  mul_inv_cancel := by
    intro a hne
    refine Quotient.inductionOn a (fun x => ?_) hne
    intro hne'
    apply Quotient.sound
    change ratRel _ _
    unfold ratRel ratMulRaw ratInvRaw
    by_cases hx1 : 0 < x.1.1
    · simp [hx1, Int.mul_comm]
    · by_cases hx2 : x.1.1 < 0
      · simp [hx1, hx2]
        rw [Int.mul_neg, Int.mul_neg, Int.mul_comm]
      · exfalso
        apply hne'
        apply Quotient.sound
        change ratRel _ _
        unfold ratRel
        have hxz : x.1.1 = 0 := by omega
        simp [hxz]
  le_refl := by
    intro a
    refine Quotient.inductionOn a (fun _ => Int.le_refl _)
  le_trans := by
    intro a b c
    refine Quotient.inductionOn₃ a b c (fun x y z hxy hyz => ?_)
    change ratLERaw x y at hxy
    change ratLERaw y z at hyz
    change ratLERaw x z
    unfold ratLERaw at *
    apply int_le_of_mul_le_pos y.2
    have p1 : (x.1.1 * z.1.2) * y.1.2 = (x.1.1 * y.1.2) * z.1.2 := by
      rw [Int.mul_assoc, Int.mul_comm z.1.2 y.1.2, ← Int.mul_assoc]
    have p2 : (y.1.1 * x.1.2) * z.1.2 = (y.1.1 * z.1.2) * x.1.2 := by
      rw [Int.mul_assoc, Int.mul_comm x.1.2 z.1.2, ← Int.mul_assoc]
    have p3 : (z.1.1 * x.1.2) * y.1.2 = (z.1.1 * y.1.2) * x.1.2 := by
      rw [Int.mul_assoc, Int.mul_comm x.1.2 y.1.2, ← Int.mul_assoc]
    rw [p1, p3]
    exact Int.le_trans
      (Int.mul_le_mul_of_nonneg_right hxy (Int.le_of_lt z.2))
      (by rw [p2]; exact Int.mul_le_mul_of_nonneg_right hyz (Int.le_of_lt x.2))
  le_antisymm := by
    intro a b
    refine Quotient.inductionOn₂ a b (fun x y hxy hyx => Quotient.sound ?_)
    change ratLERaw x y at hxy
    change ratLERaw y x at hyx
    change ratRel x y
    unfold ratLERaw ratRel at *
    omega
  le_total := by
    intro a b
    refine Quotient.inductionOn₂ a b (fun x y => ?_)
    change ratLERaw x y ∨ ratLERaw y x
    unfold ratLERaw
    omega
  lt_iff_le_not_le := fun _ _ => Iff.rfl
  add_le_add_left := by
    intro a b hab c
    refine Quotient.inductionOn₃ a b c (fun x y z hxy => ?_) hab
    change ratLERaw x y at hxy
    change ratLERaw (ratAddRaw z x) (ratAddRaw z y)
    unfold ratLERaw ratAddRaw at *
    simp only []
    have hmul :
        (x.1.1 * y.1.2) * (z.1.2 * z.1.2) ≤ (y.1.1 * x.1.2) * (z.1.2 * z.1.2) :=
      Int.mul_le_mul_of_nonneg_right hxy (Int.le_of_lt (Int.mul_pos z.2 z.2))
    have lhs :
        (z.1.1 * x.1.2 + x.1.1 * z.1.2) * (z.1.2 * y.1.2) =
          z.1.1 * z.1.2 * (x.1.2 * y.1.2) + (x.1.1 * y.1.2) * (z.1.2 * z.1.2) := by
      rw [Int.add_mul]
      have l1 : z.1.1 * x.1.2 * (z.1.2 * y.1.2) = z.1.1 * z.1.2 * (x.1.2 * y.1.2) := by
        rw [Int.mul_assoc, ← Int.mul_assoc x.1.2 z.1.2 y.1.2, Int.mul_comm x.1.2 z.1.2,
            Int.mul_assoc z.1.2 x.1.2 y.1.2, ← Int.mul_assoc]
      have l2 : x.1.1 * z.1.2 * (z.1.2 * y.1.2) = (x.1.1 * y.1.2) * (z.1.2 * z.1.2) := by
        rw [Int.mul_assoc, Int.mul_comm z.1.2 y.1.2, ← Int.mul_assoc z.1.2 y.1.2 z.1.2,
            Int.mul_comm z.1.2 y.1.2, Int.mul_assoc y.1.2 z.1.2 z.1.2, ← Int.mul_assoc]
      rw [l1, l2]
    have rhs :
        (z.1.1 * y.1.2 + y.1.1 * z.1.2) * (z.1.2 * x.1.2) =
          z.1.1 * z.1.2 * (x.1.2 * y.1.2) + (y.1.1 * x.1.2) * (z.1.2 * z.1.2) := by
      rw [Int.add_mul]
      have r1 : z.1.1 * y.1.2 * (z.1.2 * x.1.2) = z.1.1 * z.1.2 * (x.1.2 * y.1.2) := by
        rw [Int.mul_assoc, ← Int.mul_assoc y.1.2 z.1.2 x.1.2, Int.mul_comm y.1.2 z.1.2,
            Int.mul_assoc z.1.2 y.1.2 x.1.2, Int.mul_comm y.1.2 x.1.2, ← Int.mul_assoc]
      have r2 : y.1.1 * z.1.2 * (z.1.2 * x.1.2) = (y.1.1 * x.1.2) * (z.1.2 * z.1.2) := by
        rw [Int.mul_assoc, Int.mul_comm z.1.2 x.1.2, ← Int.mul_assoc z.1.2 x.1.2 z.1.2,
            Int.mul_comm z.1.2 x.1.2, Int.mul_assoc x.1.2 z.1.2 z.1.2, ← Int.mul_assoc]
      rw [r1, r2]
    rw [lhs, rhs]
    exact Int.add_le_add_left hmul _
  mul_pos := by
    intro a b ha hb
    refine Quotient.inductionOn₂ a b (fun x y hx hy => ?_) ha hb
    change ratLERaw ⟨(0, 1), by omega⟩ x ∧ ¬ ratLERaw x ⟨(0, 1), by omega⟩ at hx
    change ratLERaw ⟨(0, 1), by omega⟩ y ∧ ¬ ratLERaw y ⟨(0, 1), by omega⟩ at hy
    change ratLERaw ⟨(0, 1), by omega⟩ (ratMulRaw x y) ∧
           ¬ ratLERaw (ratMulRaw x y) ⟨(0, 1), by omega⟩
    unfold ratLERaw ratMulRaw at *
    simp only [Int.zero_mul, Int.mul_one] at *
    have hxp : 0 < x.1.1 := by omega
    have hyp : 0 < y.1.1 := by omega
    have hp : 0 < x.1.1 * y.1.1 := Int.mul_pos hxp hyp
    omega

theorem orderedField_nonvacuous : Nonempty { F : Type // Nonempty (OrderedField F) } :=
  ⟨⟨RatField, ⟨instOrderedFieldRat⟩⟩⟩

/-! ## Section 2: Finite Sums, Products, Subset Sums, and General `n`-Variable AM–GM -/

def Injective {α : Type u} {β : Type v} (f : α → β) : Prop :=
  ∀ x y : α, f x = f y → x = y

section SumsAndAMGM

variable {F : Type u} [OrderedField F]

theorem sub_eq_zero_iff_f {a b : F} : a - b = 0 ↔ a = b := by
  constructor
  · intro h
    have h1 : (a - b) + b = 0 + b := congrArg (fun x => x + b) h
    rw [OrderedField.sub_eq_add_neg, OrderedField.add_assoc, OrderedField.neg_add_cancel,
        add_zero_f, OrderedField.zero_add] at h1
    exact h1
  · intro h
    rw [h, sub_self_f]

theorem inv_one_f : OrderedField.inv (1 : F) = 1 := by
  have h := OrderedField.mul_inv_cancel (1 : F) (Ne.symm (OrderedField.zero_ne_one (F := F)))
  rw [OrderedField.one_mul] at h
  exact h

theorem mul_left_cancel_f {a b c : F} (hc : c ≠ 0) (h : c * a = c * b) : a = b := by
  have hsub : c * (a - b) = 0 := by rw [mul_sub_f, h, sub_self_f]
  cases mul_eq_zero_iff_f.mp hsub with
  | inl hc0 => exact False.elim (hc hc0)
  | inr hab => exact sub_eq_zero_iff_f.mp hab

theorem mul_right_cancel_f {a b c : F} (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  apply mul_left_cancel_f hc
  rw [OrderedField.mul_comm c a, OrderedField.mul_comm c b]
  exact h

theorem eq_zero_of_sq_eq_zero_f {a : F} (h : a * a = 0) : a = 0 := by
  cases mul_eq_zero_iff_f.mp h with
  | inl ha => exact ha
  | inr ha => exact ha

theorem two_pos_f : (0 : F) < 1 + 1 :=
  OrderedField.add_le_add_left 0 1 zero_le_one_f 1 |> lt_of_lt_of_le_f (by
    have h := zero_lt_one_f (F := F)
    simpa [add_zero_f] using h)

theorem two_ne_zero_f : (1 + 1 : F) ≠ 0 :=
  Ne.symm (ne_of_lt_f two_pos_f)

theorem sq_add_f (a b : F) :
    (a + b) * (a + b) = a * a + (1 + 1) * (a * b) + b * b := by
  calc
    (a + b) * (a + b) = a * (a + b) + b * (a + b) := right_distrib_f a b (a + b)
    _ = (a * a + a * b) + (b * a + b * b) := by
          rw [OrderedField.left_distrib, OrderedField.left_distrib]
    _ = a * a + (a * b + a * b) + b * b := by
          rw [OrderedField.mul_comm b a, OrderedField.add_assoc (a * a) (a * b) _,
              ← OrderedField.add_assoc (a * b) (a * b) (b * b),
              ← OrderedField.add_assoc (a * a) _ (b * b)]
    _ = a * a + (1 + 1) * (a * b) + b * b := by
          rw [right_distrib_f 1 1 (a * b), OrderedField.one_mul]

theorem sq_sub_f (a b : F) :
    (a - b) * (a - b) = a * a - (1 + 1) * (a * b) + b * b := by
  rw [OrderedField.sub_eq_add_neg a b, sq_add_f a (-b),
      mul_neg_f a b, mul_neg_f (1 + 1) (a * b), neg_mul_neg_f b b,
      ← OrderedField.sub_eq_add_neg]

theorem fpow_mul_f (a b : F) (k : Nat) : fpow (a * b) k = fpow a k * fpow b k := by
  induction k with
  | zero => simp [fpow, OrderedField.one_mul]
  | succ k ih =>
    simp only [fpow, ih]
    calc
      (fpow a k * fpow b k) * (a * b)
          = fpow a k * (fpow b k * (a * b)) := OrderedField.mul_assoc _ _ _
      _ = fpow a k * (a * (fpow b k * b)) := by
            rw [← OrderedField.mul_assoc (fpow b k) a b,
                OrderedField.mul_comm (fpow b k) a,
                OrderedField.mul_assoc a (fpow b k) b]
      _ = (fpow a k * a) * (fpow b k * b) := by
            rw [← OrderedField.mul_assoc (fpow a k) a _]

def finSum : {n : Nat} → (Fin n → F) → F
  | 0, _ => 0
  | n + 1, f =>
      finSum (fun i : Fin n => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) + f ⟨n, Nat.lt_succ_self n⟩

def finProd : {n : Nat} → (Fin n → F) → F
  | 0, _ => 1
  | n + 1, f =>
      finProd (fun i : Fin n => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) * f ⟨n, Nat.lt_succ_self n⟩

theorem finSum_congr {n : Nat} {f g : Fin n → F} (h : ∀ i, f i = g i) :
    finSum f = finSum g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSum]
    rw [ih (fun i => h _), h]

theorem finProd_congr {n : Nat} {f g : Fin n → F} (h : ∀ i, f i = g i) :
    finProd f = finProd g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finProd]
    rw [ih (fun i => h _), h]

theorem finSum_const (n : Nat) (c : F) :
    finSum (fun _ : Fin n => c) = ofNatF n * c := by
  induction n with
  | zero => simp [finSum, ofNatF, zero_mul_f]
  | succ n ih =>
    simp only [finSum, ih, ofNatF]
    rw [right_distrib_f, OrderedField.one_mul]

theorem finProd_const (n : Nat) (c : F) :
    finProd (fun _ : Fin n => c) = fpow c n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [finProd, fpow, ih]

theorem finSum_add {n : Nat} (f g : Fin n → F) :
    finSum (fun i => f i + g i) = finSum f + finSum g := by
  induction n with
  | zero => simp [finSum, add_zero_f]
  | succ n ih =>
    simp only [finSum, ih]
    calc
      (finSum (fun i : Fin n => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) +
        finSum (fun i : Fin n => g ⟨i.1, Nat.lt_succ_of_lt i.2⟩)) +
          (f ⟨n, Nat.lt_succ_self n⟩ + g ⟨n, Nat.lt_succ_self n⟩)
          = finSum (fun i : Fin n => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) +
            (finSum (fun i : Fin n => g ⟨i.1, Nat.lt_succ_of_lt i.2⟩) +
              (f ⟨n, Nat.lt_succ_self n⟩ + g ⟨n, Nat.lt_succ_self n⟩)) :=
            OrderedField.add_assoc _ _ _
      _ = finSum (fun i : Fin n => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) +
            (f ⟨n, Nat.lt_succ_self n⟩ +
              (finSum (fun i : Fin n => g ⟨i.1, Nat.lt_succ_of_lt i.2⟩) +
                g ⟨n, Nat.lt_succ_self n⟩)) := by
            rw [← OrderedField.add_assoc _ (f _) (g _),
                OrderedField.add_comm _ (f _),
                OrderedField.add_assoc (f _) _ (g _)]
      _ = (finSum (fun i : Fin n => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) +
            f ⟨n, Nat.lt_succ_self n⟩) +
          (finSum (fun i : Fin n => g ⟨i.1, Nat.lt_succ_of_lt i.2⟩) +
            g ⟨n, Nat.lt_succ_self n⟩) := by
            rw [← OrderedField.add_assoc]

theorem finSum_neg {n : Nat} (f : Fin n → F) :
    finSum (fun i => -f i) = -finSum f := by
  induction n with
  | zero => simp [finSum, neg_zero_f]
  | succ n ih =>
    simp only [finSum, ih, neg_add_f]

theorem finSum_sub {n : Nat} (f g : Fin n → F) :
    finSum (fun i => f i - g i) = finSum f - finSum g := by
  have h : finSum (fun i => f i - g i) = finSum (fun i => f i + (-g i)) :=
    finSum_congr (fun i => OrderedField.sub_eq_add_neg (f i) (g i))
  rw [h, finSum_add, finSum_neg, ← OrderedField.sub_eq_add_neg]

theorem finSum_scale {n : Nat} (c : F) (f : Fin n → F) :
    finSum (fun i => c * f i) = c * finSum f := by
  induction n with
  | zero => simp [finSum, mul_zero_f]
  | succ n ih =>
    simp only [finSum, ih, OrderedField.left_distrib]

theorem finSum_scale_right {n : Nat} (f : Fin n → F) (c : F) :
    finSum (fun i => f i * c) = finSum f * c := by
  induction n with
  | zero => simp [finSum, zero_mul_f]
  | succ n ih =>
    simp only [finSum, ih, right_distrib_f]

theorem finSum_nonneg {n : Nat} {f : Fin n → F} (hf : ∀ i, 0 ≤ f i) :
    0 ≤ finSum f := by
  induction n with
  | zero => exact OrderedField.le_refl 0
  | succ n ih =>
    simp only [finSum]
    have h1 : 0 ≤ finSum (fun i : Fin n => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) :=
      ih (fun i => hf _)
    have h2 := hf ⟨n, Nat.lt_succ_self n⟩
    simpa [add_zero_f] using add_le_add_f h1 h2

theorem finSum_le_finSum {n : Nat} {f g : Fin n → F} (h : ∀ i, f i ≤ g i) :
    finSum f ≤ finSum g := by
  rw [← sub_nonneg_iff_f, ← finSum_sub]
  exact finSum_nonneg (fun i => sub_nonneg_iff_f.mpr (h i))

theorem finSum_eq_zero_iff_of_nonneg {n : Nat} {f : Fin n → F} (hf : ∀ i, 0 ≤ f i) :
    finSum f = 0 ↔ ∀ i, f i = 0 := by
  constructor
  · induction n with
    | zero => intro _ i; exact Fin.elim0 i
    | succ n ih =>
      intro hsum
      simp only [finSum] at hsum
      have hs_nn : 0 ≤ finSum (fun i : Fin n => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) :=
        finSum_nonneg (fun i => hf _)
      have hl_nn : 0 ≤ f ⟨n, Nat.lt_succ_self n⟩ := hf _
      have hl_zero : f ⟨n, Nat.lt_succ_self n⟩ = 0 := by
        by_cases hne : f ⟨n, Nat.lt_succ_self n⟩ = 0
        · exact hne
        · have hp := lt_of_le_of_ne_f hl_nn (Ne.symm hne)
          have htot := add_lt_add_of_le_of_lt_f hs_nn hp
          rw [add_zero_f, hsum] at htot
          exact False.elim (lt_irrefl_f 0 htot)
      have hs_zero : finSum (fun i : Fin n => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) = 0 := by
        rw [hl_zero, add_zero_f] at hsum
        exact hsum
      have hinit := ih (fun i => hf _) hs_zero
      intro i
      by_cases hi : i.1 < n
      · have heq : i = ⟨i.1, Nat.lt_succ_of_lt hi⟩ := Fin.ext rfl
        rw [heq]
        exact hinit ⟨i.1, hi⟩
      · have heq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext (by dsimp; omega)
        rw [heq, hl_zero]
  · intro hz
    have h0 : finSum f = finSum (fun _ : Fin n => (0 : F)) := finSum_congr hz
    rw [h0, finSum_const, mul_zero_f]

theorem finSum_single {n : Nat} (k : Fin n) (v : F) :
    finSum (fun i : Fin n => if i = k then v else 0) = v := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    simp only [finSum]
    by_cases hk : k.1 < n
    · have hkne : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) ≠ k := by
        intro heq
        have hv : n = k.1 := congrArg Fin.val heq
        omega
      have hcongr :
          finSum (fun i : Fin n =>
            if (⟨i.1, Nat.lt_succ_of_lt i.2⟩ : Fin (n + 1)) = k then v else 0) =
          finSum (fun i : Fin n => if i = (⟨k.1, hk⟩ : Fin n) then v else 0) := by
        apply finSum_congr
        intro i
        by_cases hij : i.1 = k.1
        · have h1 : (⟨i.1, Nat.lt_succ_of_lt i.2⟩ : Fin (n + 1)) = k := Fin.ext hij
          have h2 : i = (⟨k.1, hk⟩ : Fin n) := Fin.ext hij
          simp [h1, h2]
        · have h1 : (⟨i.1, Nat.lt_succ_of_lt i.2⟩ : Fin (n + 1)) ≠ k :=
            fun he => hij (congrArg Fin.val he)
          have h2 : i ≠ (⟨k.1, hk⟩ : Fin n) :=
            fun he => hij (congrArg Fin.val he)
          simp [h1, h2]
      rw [hcongr, ih ⟨k.1, hk⟩, if_neg hkne, add_zero_f]
    · have hkeq : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = k := Fin.ext (by dsimp; omega)
      have hzero :
          finSum (fun i : Fin n =>
            if (⟨i.1, Nat.lt_succ_of_lt i.2⟩ : Fin (n + 1)) = k then v else 0) = 0 := by
        have hc :
            finSum (fun i : Fin n =>
              if (⟨i.1, Nat.lt_succ_of_lt i.2⟩ : Fin (n + 1)) = k then v else 0) =
            finSum (fun _ : Fin n => (0 : F)) := by
          apply finSum_congr
          intro i
          have hne : (⟨i.1, Nat.lt_succ_of_lt i.2⟩ : Fin (n + 1)) ≠ k := by
            intro he
            have hv : i.1 = k.1 := congrArg Fin.val he
            omega
          simp [hne]
        rw [hc, finSum_const, mul_zero_f]
      rw [hzero, if_pos hkeq, OrderedField.zero_add]

theorem finSum_split_at {n : Nat} (f : Fin n → F) (k : Fin n) :
    f k + finSum (fun i : Fin n => if i = k then 0 else f i) = finSum f := by
  have hsplit :
      finSum f =
        finSum (fun i : Fin n =>
          (if i = k then f k else 0) + (if i = k then 0 else f i)) := by
    apply finSum_congr
    intro i
    by_cases hik : i = k
    · subst hik; simp [add_zero_f]
    · simp [hik, OrderedField.zero_add]
  rw [hsplit, finSum_add, finSum_single]

theorem finSum_swap {n m : Nat} (A : Fin n → Fin m → F) :
    finSum (fun i => finSum (fun j => A i j)) =
      finSum (fun j => finSum (fun i => A i j)) := by
  induction n with
  | zero =>
    simp only [finSum]
    have hc : finSum (fun _ : Fin m => (0 : F)) = 0 := by
      rw [finSum_const, mul_zero_f]
    exact hc.symm
  | succ n ih =>
    simp only [finSum]
    rw [ih, ← finSum_add]

theorem finSum_mul_finSum {n m : Nat} (f : Fin n → F) (g : Fin m → F) :
    finSum f * finSum g = finSum (fun i => finSum (fun j => f i * g j)) := by
  calc
    finSum f * finSum g = finSum (fun i => f i * finSum g) :=
      (finSum_scale_right f (finSum g)).symm
    _ = finSum (fun i => finSum (fun j => f i * g j)) := by
      apply finSum_congr
      intro i
      exact (finSum_scale (f i) g).symm

/-- Computable membership test for the image of `ι : Fin k → Fin n`. -/
def memImage {n : Nat} : {k : Nat} → (Fin k → Fin n) → Fin n → Bool
  | 0, _, _ => false
  | k + 1, ι, i =>
      (decide (ι ⟨k, Nat.lt_succ_self k⟩ = i)) ||
        memImage (fun r : Fin k => ι ⟨r.1, Nat.lt_succ_of_lt r.2⟩) i

theorem memImage_iff {n k : Nat} (ι : Fin k → Fin n) (i : Fin n) :
    memImage ι i = true ↔ ∃ r : Fin k, ι r = i := by
  induction k with
  | zero =>
    simp only [memImage]
    constructor
    · intro h; cases h
    · intro ⟨r, _⟩; exact Fin.elim0 r
  | succ k ih =>
    simp only [memImage, Bool.or_eq_true, decide_eq_true_eq, ih]
    constructor
    · intro h
      cases h with
      | inl hlast => exact ⟨⟨k, Nat.lt_succ_self k⟩, hlast⟩
      | inr hprev =>
        obtain ⟨r, hr⟩ := hprev
        exact ⟨⟨r.1, Nat.lt_succ_of_lt r.2⟩, hr⟩
    · intro ⟨r, hr⟩
      by_cases hrk : r.1 < k
      · right
        refine ⟨⟨r.1, hrk⟩, ?_⟩
        have heq : (⟨r.1, Nat.lt_succ_of_lt hrk⟩ : Fin (k + 1)) = r := Fin.ext rfl
        rw [heq, hr]
      · left
        have heq : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = r := Fin.ext (by dsimp; omega)
        rw [heq, hr]

theorem finSum_injective_subset {n k : Nat} (ι : Fin k → Fin n)
    (hinj : Injective ι) (f : Fin n → F) :
    finSum (fun r : Fin k => f (ι r)) =
      finSum (fun i : Fin n => if memImage ι i then f i else 0) := by
  induction k with
  | zero =>
    simp only [finSum, memImage]
    have hc : finSum (fun _ : Fin n => (0 : F)) = 0 := by
      rw [finSum_const, mul_zero_f]
    exact hc.symm
  | succ k ih =>
    let ιInit : Fin k → Fin n := fun r => ι ⟨r.1, Nat.lt_succ_of_lt r.2⟩
    have hinjInit : Injective ιInit := by
      intro r1 r2 h
      have h' : (⟨r1.1, Nat.lt_succ_of_lt r1.2⟩ : Fin (k + 1)) =
                ⟨r2.1, Nat.lt_succ_of_lt r2.2⟩ :=
        hinj _ _ h
      have hv : (⟨r1.1, Nat.lt_succ_of_lt r1.2⟩ : Fin (k + 1)).1 =
                (⟨r2.1, Nat.lt_succ_of_lt r2.2⟩ : Fin (k + 1)).1 := congrArg Fin.val h'
      exact Fin.ext hv
    simp only [finSum]
    rw [ih ιInit hinjInit]
    rw [← finSum_single (ι ⟨k, Nat.lt_succ_self k⟩) (f (ι ⟨k, Nat.lt_succ_self k⟩)),
        ← finSum_add]
    apply finSum_congr
    intro i
    by_cases hlast : ι ⟨k, Nat.lt_succ_self k⟩ = i
    · have hnot : memImage ιInit i = false := by
        by_cases hm : memImage ιInit i = true
        · obtain ⟨r, hr⟩ := (memImage_iff ιInit i).mp hm
          have heq := hinj _ _ (hr.trans hlast.symm)
          have hv : r.1 = k := congrArg Fin.val heq
          omega
        · cases hbool : memImage ιInit i
          · rfl
          · exact False.elim (hm hbool)
      have hmem : memImage ι i = true := by
        simp [memImage, hlast]
      have h_ieq : i = ι ⟨k, Nat.lt_succ_self k⟩ := hlast.symm
      rw [hnot, hmem]
      simp [h_ieq, OrderedField.zero_add]
    · have h_ine : i ≠ ι ⟨k, Nat.lt_succ_self k⟩ := fun he => hlast he.symm
      have hmem_eq : memImage ι i = memImage ιInit i := by
        simp [memImage, hlast]
        rfl
      rw [hmem_eq, if_neg h_ine, add_zero_f]

theorem finSum_subset_plus_complement {n k : Nat} (ι : Fin k → Fin n)
    (hinj : Injective ι) (f : Fin n → F) :
    finSum (fun r : Fin k => f (ι r)) +
      finSum (fun i : Fin n => if memImage ι i then 0 else f i) = finSum f := by
  rw [finSum_injective_subset ι hinj f, ← finSum_add]
  apply finSum_congr
  intro i
  cases memImage ι i <;> simp [OrderedField.zero_add, add_zero_f]

theorem subset_complement_ones {n k : Nat} (hk : k ≤ n) (ι : Fin k → Fin n)
    (hinj : Injective ι) :
    finSum (fun i : Fin n => if memImage ι i then (0 : F) else 1) = ofNatF (n - k) := by
  have htot := finSum_subset_plus_complement ι hinj (fun _ : Fin n => (1 : F))
  rw [finSum_const k 1, finSum_const n 1, mul_one_f, mul_one_f] at htot
  apply add_left_cancel_f (a := ofNatF k)
  rw [htot, ← ofNatF_add]
  have hn : k + (n - k) = n := by omega
  rw [hn]

theorem finProd_nonneg {n : Nat} {f : Fin n → F} (hf : ∀ i, 0 ≤ f i) :
    0 ≤ finProd f := by
  induction n with
  | zero => exact zero_le_one_f
  | succ n ih =>
    simp only [finProd]
    exact mul_nonneg_f (ih (fun i => hf _)) (hf _)

/-- General `n`-variable AM–GM inequality with strict equality characterization over any `OrderedField`. -/
theorem am_gm_complete :
    ∀ {n : Nat} (_ : 0 < n) (f : Fin n → F) (_ : ∀ i, 0 ≤ f i),
      let m := fdiv (finSum f) (ofNatF n)
      finProd f ≤ fpow m n ∧ (finProd f = fpow m n ↔ ∀ i : Fin n, f i = m)
  | 0, hn, _, _ => by omega
  | 1, _, f, _ => by
    intro m
    have hm : m = f ⟨0, by omega⟩ := by
      change (0 + f ⟨0, by omega⟩) * OrderedField.inv (0 + 1) = f ⟨0, by omega⟩
      rw [OrderedField.zero_add, OrderedField.zero_add, inv_one_f, mul_one_f]
    have hp : finProd f = f ⟨0, by omega⟩ := by
      change 1 * f ⟨0, by omega⟩ = f ⟨0, by omega⟩
      exact OrderedField.one_mul _
    have hpow : fpow m 1 = m := by
      change 1 * m = m
      exact OrderedField.one_mul _
    rw [hp, hpow, hm]
    refine ⟨OrderedField.le_refl _, ?_⟩
    constructor
    · intro _ i
      have hi : i = ⟨0, by omega⟩ := Fin.ext (by omega)
      rw [hi]
    · intro _; rfl
  | n + 2, _, f, hf => by
    let k := n + 1
    have hk_pos : 0 < k := by omega
    let fInit : Fin k → F := fun i => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩
    let last : F := f ⟨k, Nat.lt_succ_self k⟩
    have hfInit : ∀ i, 0 ≤ fInit i := fun i => hf _
    have hlast_nn : 0 ≤ last := hf _
    obtain ⟨ih_le, ih_eq⟩ := am_gm_complete hk_pos fInit hfInit
    let μ : F := fdiv (finSum fInit) (ofNatF k)
    intro m
    have hk_ne : (ofNatF k : F) ≠ 0 := ofNatF_ne_zero hk_pos
    have hk1_ne : (ofNatF (k + 1) : F) ≠ 0 := ofNatF_ne_zero (by omega)
    have hsum_init : ofNatF k * μ = finSum fInit := by
      unfold μ fdiv
      rw [OrderedField.mul_comm (ofNatF k), OrderedField.mul_assoc,
          inv_mul_cancel_f hk_ne, mul_one_f]
    have hsum_full : ofNatF (k + 1) * m = ofNatF k * μ + last := by
      unfold m fdiv
      rw [OrderedField.mul_comm (ofNatF (k + 1)), OrderedField.mul_assoc,
          inv_mul_cancel_f hk1_ne, mul_one_f]
      change finSum fInit + last = ofNatF k * μ + last
      rw [hsum_init]
    have hm_nn : 0 ≤ m :=
      mul_nonneg_f (finSum_nonneg hf) (inv_nonneg_f (ofNatF_nonneg (k + 1)))
    by_cases hμ0 : μ = 0
    · have hinit_sum0 : finSum fInit = 0 := by
        rw [← hsum_init, hμ0, mul_zero_f]
      have hinit_all0 : ∀ i : Fin k, fInit i = 0 :=
        (finSum_eq_zero_iff_of_nonneg hfInit).mp hinit_sum0
      have hprod_init0 : finProd fInit = 0 := by
        cases n with
        | zero =>
          change 1 * fInit ⟨0, by omega⟩ = 0
          rw [OrderedField.one_mul, hinit_all0]
        | succ n' =>
          change finProd _ * fInit ⟨n' + 1, by omega⟩ = 0
          rw [hinit_all0, mul_zero_f]
      have hprod0 : finProd f = 0 := by
        change finProd fInit * last = 0
        rw [hprod_init0, zero_mul_f]
      rw [hprod0]
      refine ⟨fpow_nonneg hm_nn (k + 1), ?_⟩
      constructor
      · intro hpow0
        have hm0 : m = 0 := by
          by_cases hmnz : m = 0
          · exact hmnz
          · have hmp : 0 < m := lt_of_le_of_ne_f hm_nn (Ne.symm hmnz)
            have hpp : 0 < fpow m (k + 1) := fpow_pos hmp (k + 1)
            rw [← hpow0] at hpp
            exact False.elim (lt_irrefl_f 0 hpp)
        have hlast0 : last = 0 := by
          rw [hm0, mul_zero_f, hμ0, mul_zero_f, OrderedField.zero_add] at hsum_full
          exact hsum_full.symm
        intro i
        rw [hm0]
        by_cases hi : i.1 < k
        · have heq : i = ⟨i.1, Nat.lt_succ_of_lt hi⟩ := Fin.ext rfl
          rw [heq]; exact hinit_all0 ⟨i.1, hi⟩
        · have heq : i = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext (by dsimp; omega)
          rw [heq]; exact hlast0
      · intro hall
        have hm0 : m = 0 := by
          have h0 := hall ⟨0, by omega⟩
          have hf0 : f ⟨0, by omega⟩ = 0 := hinit_all0 ⟨0, by omega⟩
          rw [hf0] at h0
          exact h0.symm
        rw [hm0]
        change (0 : F) = fpow 0 k * 0
        rw [mul_zero_f]
    · have hμ_nn : 0 ≤ μ :=
        mul_nonneg_f (finSum_nonneg hfInit) (inv_nonneg_f (ofNatF_nonneg k))
      have hμ_pos : 0 < μ := lt_of_le_of_ne_f hμ_nn (Ne.symm hμ0)
      have hk1_pos : (0 : F) < ofNatF (k + 1) := ofNatF_pos (n := k + 1) (by omega)
      have hm_pos : 0 < m := by
        have htot_pos0 :=
          add_lt_add_of_lt_of_le_f (OrderedField.mul_pos _ _ (ofNatF_pos hk_pos) hμ_pos) hlast_nn
        rw [add_zero_f, ← hsum_full] at htot_pos0
        have hp := OrderedField.mul_pos _ _ htot_pos0 (inv_pos_f hk1_pos)
        rw [OrderedField.mul_comm (ofNatF (k + 1)) m, OrderedField.mul_assoc,
            OrderedField.mul_inv_cancel _ hk1_ne, mul_one_f] at hp
        exact hp
      let denom : F := ofNatF (k + 1) * μ
      have hdenom_pos : 0 < denom := OrderedField.mul_pos _ _ hk1_pos hμ_pos
      have hdenom_ne : denom ≠ 0 := Ne.symm (ne_of_lt_f hdenom_pos)
      let x : F := fdiv (last - μ) denom
      have h_denom_x : denom * x = last - μ := by
        unfold x fdiv
        rw [OrderedField.mul_comm denom, OrderedField.mul_assoc,
            inv_mul_cancel_f hdenom_ne, mul_one_f]
      have h_mu_one_add_x : μ * (1 + x) = m := by
        apply mul_left_cancel_f hk1_ne
        calc
          ofNatF (k + 1) * (μ * (1 + x)) = denom * (1 + x) := by
            unfold denom; rw [OrderedField.mul_assoc]
          _ = denom + (last - μ) := by
            rw [OrderedField.left_distrib, mul_one_f, h_denom_x]
          _ = ofNatF k * μ + μ + (last - μ) := by
            unfold denom
            have hk1 : ofNatF (k + 1) * μ = ofNatF k * μ + μ := by
              change (ofNatF k + 1) * μ = ofNatF k * μ + μ
              rw [right_distrib_f, OrderedField.one_mul]
            rw [hk1]
          _ = ofNatF k * μ + last := by
            rw [OrderedField.sub_eq_add_neg, OrderedField.add_assoc (ofNatF k * μ) μ _,
                OrderedField.add_comm last (-μ), ← OrderedField.add_assoc μ (-μ) last,
                add_neg_cancel_f, OrderedField.zero_add]
          _ = ofNatF (k + 1) * m := hsum_full.symm
      have h_one_add_x_pos : 0 < 1 + x := by
        have hp := OrderedField.mul_pos _ _ hm_pos (inv_pos_f hμ_pos)
        rw [← h_mu_one_add_x, OrderedField.mul_comm μ (1 + x), OrderedField.mul_assoc,
            OrderedField.mul_inv_cancel μ hμ0, mul_one_f] at hp
        exact hp
      have h_mu_kx : μ * (1 + ofNatF (k + 1) * x) = last := by
        calc
          μ * (1 + ofNatF (k + 1) * x) = μ + μ * (ofNatF (k + 1) * x) := by
            rw [OrderedField.left_distrib, mul_one_f]
          _ = μ + denom * x := by
            unfold denom
            rw [← OrderedField.mul_assoc μ (ofNatF (k + 1)) x,
                OrderedField.mul_comm μ (ofNatF (k + 1))]
          _ = μ + (last - μ) := by rw [h_denom_x]
          _ = last := by
            rw [OrderedField.sub_eq_add_neg, OrderedField.add_comm last (-μ),
                ← OrderedField.add_assoc, add_neg_cancel_f, OrderedField.zero_add]
      have hbern : 1 + ofNatF (k + 1) * x ≤ fpow (1 + x) (k + 1) :=
        bernoulli_ge (le_of_lt_f h_one_add_x_pos) (k + 1)
      have hpow_m : fpow μ (k + 1) * fpow (1 + x) (k + 1) = fpow m (k + 1) := by
        rw [← fpow_mul_f, h_mu_one_add_x]
      have hpow_lhs : fpow μ (k + 1) * (1 + ofNatF (k + 1) * x) = fpow μ k * last := by
        change (fpow μ k * μ) * (1 + ofNatF (k + 1) * x) = fpow μ k * last
        rw [OrderedField.mul_assoc, h_mu_kx]
      have hstep1 : finProd fInit * last ≤ fpow μ k * last :=
        mul_le_mul_of_nonneg_right_f ih_le hlast_nn
      have hstep2 : fpow μ k * last ≤ fpow m (k + 1) := by
        have hm1 := mul_le_mul_of_nonneg_left_f hbern (le_of_lt_f (fpow_pos hμ_pos (k + 1)))
        rw [hpow_lhs, hpow_m] at hm1
        exact hm1
      have hmain_le : finProd f ≤ fpow m (k + 1) :=
        OrderedField.le_trans _ _ _ hstep1 hstep2
      refine ⟨hmain_le, ?_⟩
      constructor
      · intro heq_prod
        have hx0 : x = 0 := by
          by_cases hxnz : x = 0
          · exact hxnz
          · have hstr := bernoulli_strict h_one_add_x_pos hxnz (k := k + 1) (by omega)
            have hm_str := mul_lt_mul_of_pos_left_f hstr (fpow_pos hμ_pos (k + 1))
            rw [hpow_lhs, hpow_m] at hm_str
            have hlt_tot := lt_of_le_of_lt_f hstep1 hm_str
            change finProd f < fpow m (k + 1) at hlt_tot
            rw [heq_prod] at hlt_tot
            exact False.elim (lt_irrefl_f _ hlt_tot)
        have hlast_eq_mu : last = μ := by
          rw [hx0, mul_zero_f, add_zero_f, mul_one_f] at h_mu_kx
          exact h_mu_kx.symm
        have hm_eq_mu : m = μ := by
          rw [hx0, add_zero_f, mul_one_f] at h_mu_one_add_x
          exact h_mu_one_add_x.symm
        have hprod_init_eq : finProd fInit = fpow μ k := by
          change finProd fInit * last = fpow m k * m at heq_prod
          rw [hlast_eq_mu, hm_eq_mu] at heq_prod
          exact mul_right_cancel_f hμ0 heq_prod
        have hall_init := ih_eq.mp hprod_init_eq
        intro i
        rw [hm_eq_mu]
        by_cases hi : i.1 < k
        · have heq : i = ⟨i.1, Nat.lt_succ_of_lt hi⟩ := Fin.ext rfl
          rw [heq]; exact hall_init ⟨i.1, hi⟩
        · have heq : i = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext (by dsimp; omega)
          rw [heq]; exact hlast_eq_mu
      · intro hall
        have hc : finProd f = finProd (fun _ : Fin (k + 1) => m) := finProd_congr hall
        rw [hc, finProd_const]

end SumsAndAMGM

/-! ## Section 3: Spectral Domains, Majorization, Matrix Algebra, and Householder Realization -/

section SpectralAndMatrices

variable {F : Type u} [OrderedField F]

abbrev Spec (n : Nat) (F : Type u) := Fin n → F
abbrev Mat  (n : Nat) (F : Type u) := Fin n → Fin n → F

abbrev specTrace {n : Nat} (lam : Spec n F) : F := finSum lam

/-- Lower-bounded fixed-trace simplex `Δ_{n,c}(a) = {λ ∈ F^n : a ≤ λ_i, ∑ λ_i = c}`. -/
def LowerTraceSimplex (n : Nat) (a c : F) (lam : Spec n F) : Prop :=
  (∀ i : Fin n, a ≤ lam i) ∧ specTrace lam = c

/-- PSD fixed-trace simplex `Δ_{n,c}(0) = {λ ≥ 0 : ∑ λ_i = c}`. -/
def PSDTraceSimplex (n : Nat) (c : F) (lam : Spec n F) : Prop :=
  LowerTraceSimplex n 0 c lam

/-- Two-sided box-constrained fixed-trace polytope `B_{n,c}(a,b) = {a ≤ λ_i ≤ b, ∑ λ_i = c}`. -/
def BoxTracePolytope (n : Nat) (a b c : F) (lam : Spec n F) : Prop :=
  (∀ i : Fin n, a ≤ lam i ∧ lam i ≤ b) ∧ specTrace lam = c

def IsNonincreasing {n : Nat} (lam : Spec n F) : Prop :=
  ∀ i j : Fin n, i.1 ≤ j.1 → lam j ≤ lam i

def IsPermSpec {n : Nat} (mu lam : Spec n F) : Prop :=
  ∃ (σ g : Fin n → Fin n),
    (∀ i, g (σ i) = i) ∧ (∀ i, σ (g i) = i) ∧ (∀ i, mu i = lam (σ i))

/-- Concentrated spectrum at index `0` with floor `a` and trace `c`: `(c - (n-1)a, a, ..., a)`. -/
def concSpec (n : Nat) (_ : 0 < n) (a c : F) : Spec n F :=
  fun i => if i.1 = 0 then c - ofNatF (n - 1) * a else a

/-- Uniform (isotropic) spectrum with trace `c`: `(c/n, ..., c/n)`. -/
abbrev unifSpec (n : Nat) (_ : 0 < n) (c : F) : Spec n F :=
  fun _ => fdiv c (ofNatF n)

/-- Concentrated floor predicate: excess above floor `a` sits on a single coordinate `k`. -/
def IsConcentratedFloor {n : Nat} (a : F) (lam : Spec n F) : Prop :=
  ∃ k : Fin n, a < lam k ∧ ∀ i : Fin n, i ≠ k → lam i = a

/-- Weak single-spike concentration: at least `n - 1` coordinates coincide with some background `α`. -/
def IsWeaklyConcentrated {n : Nat} (lam : Spec n F) : Prop :=
  ∃ (α : F) (k : Fin n), ∀ i : Fin n, i ≠ k → lam i = α

/-- Ky Fan / Hardy–Littlewood–Pólya majorization (`λ ≺ μ`) against a nonincreasing upper profile `μ`:
    equal trace and every `k`-element coordinate sum of `λ` is bounded by the top-`k` sum of `μ`. -/
def KyFanMajorizes {n : Nat} (mu lam : Spec n F) : Prop :=
  IsNonincreasing mu ∧
  specTrace lam = specTrace mu ∧
  ∀ (k : Nat) (hk : k ≤ n) (ι : Fin k → Fin n),
    Injective ι →
    finSum (fun r : Fin k => lam (ι r)) ≤
      finSum (fun r : Fin k => mu ⟨r.1, Nat.lt_of_lt_of_le r.2 hk⟩)

/-- Standard prefix-sum majorization on nonincreasingly sorted vectors. -/
def SortedMajorizes {n : Nat} (mu lam : Spec n F) : Prop :=
  IsNonincreasing mu ∧
  IsNonincreasing lam ∧
  specTrace lam = specTrace mu ∧
  ∀ (k : Nat) (hk : k ≤ n),
    finSum (fun r : Fin k => lam ⟨r.1, Nat.lt_of_lt_of_le r.2 hk⟩) ≤
      finSum (fun r : Fin k => mu ⟨r.1, Nat.lt_of_lt_of_le r.2 hk⟩)

theorem kyFanMajorizes_implies_sortedMajorizes {n : Nat} {mu lam : Spec n F}
    (hlam : IsNonincreasing lam) (hKF : KyFanMajorizes mu lam) :
    SortedMajorizes mu lam := by
  refine ⟨hKF.1, hlam, hKF.2.1, ?_⟩
  intro k hk
  apply hKF.2.2 k hk (fun r => ⟨r.1, Nat.lt_of_lt_of_le r.2 hk⟩)
  intro r1 r2 heq
  have hv : (⟨r1.1, Nat.lt_of_lt_of_le r1.2 hk⟩ : Fin n).1 =
            (⟨r2.1, Nat.lt_of_lt_of_le r2.2 hk⟩ : Fin n).1 := congrArg Fin.val heq
  exact Fin.ext hv

/-! ### Matrix Operations, Rank-One Perturbations, and Orthogonal Spectral Realization -/

def matTrace {n : Nat} (A : Mat n F) : F := finSum (fun i => A i i)

def frobSq {n : Nat} (A : Mat n F) : F :=
  finSum (fun i => finSum (fun j => A i j * A i j))

def IsSymmetric {n : Nat} (A : Mat n F) : Prop :=
  ∀ i j : Fin n, A i j = A j i

def transpose {n : Nat} (A : Mat n F) : Mat n F := fun i j => A j i

def matAdd {n : Nat} (A B : Mat n F) : Mat n F := fun i j => A i j + B i j
def matSub {n : Nat} (A B : Mat n F) : Mat n F := fun i j => A i j - B i j

def matMul {n : Nat} (A B : Mat n F) : Mat n F :=
  fun i k => finSum (fun j => A i j * B j k)

def matVec {n : Nat} (A : Mat n F) (x : Fin n → F) : Fin n → F :=
  fun i => finSum (fun j => A i j * x j)

def dotProd {n : Nat} (u v : Fin n → F) : F :=
  finSum (fun i => u i * v i)

def vecNormSq {n : Nat} (u : Fin n → F) : F := dotProd u u

def scalarMat (n : Nat) (α : F) : Mat n F :=
  fun i j => if i = j then α else 0

def diagMat {n : Nat} (lam : Spec n F) : Mat n F :=
  fun i j => if i = j then lam i else 0

def outerProd {n : Nat} (u v : Fin n → F) : Mat n F :=
  fun i j => u i * v j

def symRankOne {n : Nat} (β : F) (u : Fin n → F) : Mat n F :=
  fun i j => β * (u i * u j)

/-- Exact rank-at-most-one predicate over a field: `R = u vᵀ`. -/
def IsRankAtMostOne {n : Nat} (R : Mat n F) : Prop :=
  ∃ u v : Fin n → F, ∀ i j : Fin n, R i j = u i * v j

/-- Exact rank-one predicate: `rank(R) ≤ 1` and `R ≠ 0`. -/
def IsRankOne {n : Nat} (R : Mat n F) : Prop :=
  IsRankAtMostOne R ∧ ∃ i j : Fin n, R i j ≠ 0

def IsOrthogonal {n : Nat} (Q : Mat n F) : Prop :=
  matMul (transpose Q) Q = scalarMat n 1 ∧
  matMul Q (transpose Q) = scalarMat n 1

/-- Symmetric matrix `A` realizes eigenvalue tuple `λ` via an orthonormal eigenbasis `Q`. -/
def RealizesSpectrum {n : Nat} (A : Mat n F) (lam : Spec n F) : Prop :=
  IsSymmetric A ∧
  ∃ Q : Mat n F,
    IsOrthogonal Q ∧
    ∀ j : Fin n, matVec A (fun i => Q i j) = fun i => lam j * Q i j

theorem realizesSpectrum_diagMat {n : Nat} (lam : Spec n F) :
    RealizesSpectrum (diagMat lam) lam := by
  refine ⟨?_, scalarMat n 1, ⟨?_, ?_⟩, ?_⟩
  · intro i j
    unfold diagMat
    by_cases hij : i = j
    · subst hij; rfl
    · have hji : j ≠ i := fun h => hij h.symm
      simp [hij, hji]
  · funext i k
    unfold matMul transpose scalarMat
    have hc :
        finSum (fun j : Fin n => (if j = i then (1 : F) else 0) * (if j = k then 1 else 0)) =
        finSum (fun j : Fin n => if j = i then (if i = k then (1 : F) else 0) else 0) := by
      apply finSum_congr
      intro j
      by_cases hji : j = i
      · subst hji; simp [OrderedField.one_mul]
      · simp [hji, zero_mul_f]
    rw [hc, finSum_single]
  · funext i k
    unfold matMul transpose scalarMat
    have hc :
        finSum (fun j : Fin n => (if i = j then (1 : F) else 0) * (if k = j then 1 else 0)) =
        finSum (fun j : Fin n => if j = i then (if i = k then (1 : F) else 0) else 0) := by
      apply finSum_congr
      intro j
      by_cases hji : j = i
      · subst hji
        by_cases hik : j = k
        · subst hik; simp [OrderedField.one_mul]
        · have hki : k ≠ j := fun h => hik h.symm
          simp [hik, hki, mul_zero_f]
      · have hij : i ≠ j := fun h => hji h.symm
        simp [hji, hij, zero_mul_f]
    rw [hc, finSum_single]
  · intro j
    funext i
    unfold matVec diagMat scalarMat
    have hc :
        finSum (fun r : Fin n => (if i = r then lam i else 0) * (if r = j then 1 else 0)) =
        finSum (fun r : Fin n => if r = i then lam i * (if i = j then 1 else 0) else 0) := by
      apply finSum_congr
      intro r
      by_cases hri : r = i
      · subst hri; simp
      · have hir : i ≠ r := fun h => hri h.symm
        simp [hri, hir, zero_mul_f]
    rw [hc, finSum_single]
    by_cases hij : i = j
    · subst hij; simp [mul_one_f]
    · simp [hij, mul_zero_f]

theorem realizesSpectrum_perm {n : Nat} {A : Mat n F} {lam mu : Spec n F}
    (hA : RealizesSpectrum A lam) (hperm : IsPermSpec mu lam) :
    RealizesSpectrum A mu := by
  obtain ⟨hsym, Q, ⟨hQtQ, hQQt⟩, heig⟩ := hA
  obtain ⟨σ, g, hgσ, hσg, hmu⟩ := hperm
  let Q' : Mat n F := fun i j => Q i (σ j)
  refine ⟨hsym, Q', ⟨?_, ?_⟩, ?_⟩
  · funext j k
    unfold matMul transpose Q'
    have hentry := congrFun (congrFun hQtQ (σ j)) (σ k)
    unfold matMul transpose scalarMat at hentry
    rw [hentry]
    unfold scalarMat
    by_cases hjk : j = k
    · subst hjk; simp
    · have hσne : σ j ≠ σ k := by
        intro hs
        have hj : g (σ j) = g (σ k) := congrArg g hs
        rw [hgσ, hgσ] at hj
        exact hjk hj
      simp [hjk, hσne]
  · funext i k
    unfold matMul transpose Q'
    have hsum_perm :
        finSum (fun j : Fin n => Q i (σ j) * Q k (σ j)) =
        finSum (fun r : Fin n => Q i r * Q k r) := by
      have h1 :
          finSum (fun j : Fin n => Q i (σ j) * Q k (σ j)) =
          finSum (fun r : Fin n => if memImage σ r then Q i r * Q k r else 0) :=
        finSum_injective_subset σ (fun j1 j2 (hs : σ j1 = σ j2) => by
          have hj : g (σ j1) = g (σ j2) := congrArg g hs
          rw [hgσ, hgσ] at hj
          exact hj) (fun r => Q i r * Q k r)
      rw [h1]
      apply finSum_congr
      intro r
      have hmem : memImage σ r = true := (memImage_iff σ r).mpr ⟨g r, hσg r⟩
      rw [hmem]; simp
    rw [hsum_perm]
    exact congrFun (congrFun hQQt i) k
  · intro j
    rw [hmu j]
    exact heig (σ j)

/-- Weyl's rank-one multiplicity obstruction: if `A` realizes spectrum `λ` and `A - α I_n` has
    rank at most `1`, then at most one coordinate of `λ` can differ from `α`. -/
theorem scalar_plus_rankAtMostOne_at_most_one_non_alpha {n : Nat} {A : Mat n F}
    {lam : Spec n F} (hSpec : RealizesSpectrum A lam) (α : F)
    (hRank : IsRankAtMostOne (matSub A (scalarMat n α))) :
    ∀ j k : Fin n, lam j ≠ α → lam k ≠ α → j = k := by
  obtain ⟨_, Q, ⟨hQtQ, _⟩, heig⟩ := hSpec
  obtain ⟨u, v, huv⟩ := hRank
  intro j k hj hk
  by_cases hjk : j = k
  · exact hjk
  · exfalso
    let qj : Fin n → F := fun i => Q i j
    let qk : Fin n → F := fun i => Q i k
    have h_qj_qj : dotProd qj qj = 1 := by
      have h1 := congrFun (congrFun hQtQ j) j
      unfold matMul transpose scalarMat at h1
      simpa [dotProd, qj] using h1
    have h_qk_qk : dotProd qk qk = 1 := by
      have h1 := congrFun (congrFun hQtQ k) k
      unfold matMul transpose scalarMat at h1
      simpa [dotProd, qk] using h1
    have h_qk_qj : dotProd qk qj = 0 := by
      have hkj : k ≠ j := fun h => hjk h.symm
      have h1 := congrFun (congrFun hQtQ k) j
      unfold matMul transpose scalarMat at h1
      simpa [dotProd, qk, qj, hkj] using h1
    have h_rel : ∀ m : Fin n, ∀ i : Fin n,
        (lam m - α) * Q i m = u i * dotProd v (fun r => Q r m) := by
      intro m i
      have he_m := congrFun (heig m) i
      unfold matVec at he_m
      have hsub_sum :
          finSum (fun r : Fin n => (A i r - scalarMat n α i r) * Q r m) =
            (lam m - α) * Q i m := by
        have hc :
            finSum (fun r : Fin n => (A i r - scalarMat n α i r) * Q r m) =
            finSum (fun r : Fin n => A i r * Q r m - scalarMat n α i r * Q r m) :=
          finSum_congr (fun r => sub_mul_f _ _ _)
        rw [hc, finSum_sub, he_m]
        have hsc :
            finSum (fun r : Fin n => scalarMat n α i r * Q r m) = α * Q i m := by
          unfold scalarMat
          have hc2 :
              finSum (fun r : Fin n => (if i = r then α else 0) * Q r m) =
              finSum (fun r : Fin n => if r = i then α * Q i m else 0) := by
            apply finSum_congr
            intro r
            by_cases hri : r = i
            · subst hri; simp
            · have hir : i ≠ r := fun h => hri h.symm
              simp [hri, hir, zero_mul_f]
          rw [hc2, finSum_single]
        rw [hsc, ← sub_mul_f]
      have hrhs :
          finSum (fun r : Fin n => (A i r - scalarMat n α i r) * Q r m) =
            u i * dotProd v (fun r => Q r m) := by
        have hc :
            finSum (fun r : Fin n => (A i r - scalarMat n α i r) * Q r m) =
            finSum (fun r : Fin n => u i * (v r * Q r m)) := by
          apply finSum_congr
          intro r
          have hr := huv i r
          unfold matSub at hr
          rw [hr, OrderedField.mul_assoc]
        rw [hc, finSum_scale]
        rfl
      rw [← hsub_sum, hrhs]
    -- Step 1: <qj, (lam_j - α) qj> = (lam_j - α) ≠ 0 => <v, qj> ≠ 0
    have hdiff_j_ne : lam j - α ≠ 0 :=
      fun hz => hj (sub_eq_zero_iff_f.mp hz)
    have hdiff_k_ne : lam k - α ≠ 0 :=
      fun hz => hk (sub_eq_zero_iff_f.mp hz)
    have hip_jj : (lam j - α) = dotProd qj u * dotProd v qj := by
      calc
        lam j - α = (lam j - α) * dotProd qj qj := by rw [h_qj_qj, mul_one_f]
        _ = finSum (fun i => qj i * ((lam j - α) * qj i)) := by
              unfold dotProd
              rw [← finSum_scale]
              apply finSum_congr
              intro i
              calc
                (lam j - α) * (qj i * qj i) = ((lam j - α) * qj i) * qj i :=
                  (OrderedField.mul_assoc _ _ _).symm
                _ = (qj i * (lam j - α)) * qj i := by
                  conv => lhs; rw [OrderedField.mul_comm (lam j - α) (qj i)]
                _ = qj i * ((lam j - α) * qj i) := OrderedField.mul_assoc _ _ _
        _ = finSum (fun i => (qj i * u i) * dotProd v qj) := by
              apply finSum_congr
              intro i
              rw [h_rel j i, ← OrderedField.mul_assoc]
        _ = dotProd qj u * dotProd v qj := finSum_scale_right _ _
    have hv_qj_ne : dotProd v qj ≠ 0 := by
      intro hz
      rw [hz, mul_zero_f] at hip_jj
      exact hdiff_j_ne hip_jj
    -- Step 2: 0 = (lam_j - α) <qk, qj> = <qk, u> <v, qj> => <qk, u> = 0
    have hip_kj : (0 : F) = dotProd qk u * dotProd v qj := by
      calc
        (0 : F) = (lam j - α) * dotProd qk qj := by rw [h_qk_qj, mul_zero_f]
        _ = finSum (fun i => qk i * ((lam j - α) * qj i)) := by
              unfold dotProd
              rw [← finSum_scale]
              apply finSum_congr
              intro i
              rw [← OrderedField.mul_assoc, OrderedField.mul_comm (lam j - α) (qk i),
                  OrderedField.mul_assoc]
        _ = finSum (fun i => (qk i * u i) * dotProd v qj) := by
              apply finSum_congr
              intro i
              rw [h_rel j i, ← OrderedField.mul_assoc]
        _ = dotProd qk u * dotProd v qj := finSum_scale_right _ _
    have hqk_u_zero : dotProd qk u = 0 := by
      cases mul_eq_zero_iff_f.mp hip_kj.symm with
      | inl h0 => exact h0
      | inr h0 => exact False.elim (hv_qj_ne h0)
    -- Step 3: (lam_k - α) = <qk, u> <v, qk> = 0, contradiction!
    have hip_kk : (lam k - α) = dotProd qk u * dotProd v qk := by
      calc
        lam k - α = (lam k - α) * dotProd qk qk := by rw [h_qk_qk, mul_one_f]
        _ = finSum (fun i => qk i * ((lam k - α) * qk i)) := by
              unfold dotProd
              rw [← finSum_scale]
              apply finSum_congr
              intro i
              calc
                (lam k - α) * (qk i * qk i) = ((lam k - α) * qk i) * qk i :=
                  (OrderedField.mul_assoc _ _ _).symm
                _ = (qk i * (lam k - α)) * qk i := by
                  conv => lhs; rw [OrderedField.mul_comm (lam k - α) (qk i)]
                _ = qk i * ((lam k - α) * qk i) := OrderedField.mul_assoc _ _ _
        _ = finSum (fun i => (qk i * u i) * dotProd v qk) := by
              apply finSum_congr
              intro i
              rw [h_rel k i, ← OrderedField.mul_assoc]
        _ = dotProd qk u * dotProd v qk := finSum_scale_right _ _
    rw [hqk_u_zero, zero_mul_f] at hip_kk
    exact hdiff_k_ne hip_kk

theorem scalar_plus_rankAtMostOne_weaklyConcentrated {n : Nat} (hn : 0 < n)
    {A : Mat n F} {lam : Spec n F} (hSpec : RealizesSpectrum A lam) (α : F)
    (hRank : IsRankAtMostOne (matSub A (scalarMat n α))) :
    IsWeaklyConcentrated lam := by
  by_cases hex : ∃ k : Fin n, lam k ≠ α
  · obtain ⟨k, hk⟩ := hex
    refine ⟨α, k, ?_⟩
    intro i hik
    by_cases hia : lam i = α
    · exact hia
    · exact False.elim (hik (scalar_plus_rankAtMostOne_at_most_one_non_alpha hSpec α hRank i k hia hk))
  · refine ⟨α, ⟨0, hn⟩, ?_⟩
    intro i _
    by_cases hia : lam i = α
    · exact hia
    · exact False.elim (hex ⟨i, hia⟩)

/-- Square-root-free Householder orthogonal realization theorem:
    for ANY unit vector `u` (`‖u‖² = 1`), `A(u) = a I_n + (c - n a) u uᵀ` is a rank-one
    perturbation of `a I_n` with trace `c` and exact spectrum `concSpec = (c - (n-1)a, a, ..., a)`. -/
theorem rankOnePerturb_realizes_concSpec {n : Nat} (hn : 0 < n) (a c : F)
    (hc : ofNatF n * a < c) (u : Fin n → F) (hu : vecNormSq u = 1) :
    let A := matAdd (scalarMat n a) (symRankOne (c - ofNatF n * a) u)
    IsRankOne (matSub A (scalarMat n a)) ∧
    matTrace A = c ∧
    RealizesSpectrum A (concSpec n hn a c) := by
  intro A
  let β : F := c - ofNatF n * a
  have hβ_pos : 0 < β := sub_pos_iff_f.mpr hc
  have hβ_ne : β ≠ 0 := Ne.symm (ne_of_lt_f hβ_pos)
  let i0 : Fin n := ⟨0, hn⟩
  -- Part 1: Rank-one perturbation of `a I_n`
  have hdiff_eq : ∀ i j : Fin n, matSub A (scalarMat n a) i j = (β * u i) * u j := by
    intro i j
    unfold matSub A matAdd symRankOne
    rw [OrderedField.add_comm (scalarMat n a i j), OrderedField.sub_eq_add_neg,
        OrderedField.add_assoc, add_neg_cancel_f, add_zero_f, OrderedField.mul_assoc]
  have hu_nz : ∃ k : Fin n, u k ≠ 0 := by
    by_cases hex : ∃ k : Fin n, u k ≠ 0
    · exact hex
    · exfalso
      have hall0 : ∀ k : Fin n, u k * u k = 0 := by
        intro k
        have hk0 : u k = 0 := by
          by_cases hkz : u k = 0
          · exact hkz
          · exact False.elim (hex ⟨k, hkz⟩)
        rw [hk0, mul_zero_f]
      have h0 : vecNormSq u = 0 :=
        (finSum_eq_zero_iff_of_nonneg (fun k => sq_nonneg_f (u k))).mpr hall0
      rw [hu] at h0
      exact OrderedField.zero_ne_one h0.symm
  have hRank1 : IsRankOne (matSub A (scalarMat n a)) := by
    refine ⟨⟨fun i => β * u i, u, hdiff_eq⟩, ?_⟩
    obtain ⟨k, huk⟩ := hu_nz
    refine ⟨k, k, ?_⟩
    rw [hdiff_eq k k]
    intro hz
    cases mul_eq_zero_iff_f.mp hz with
    | inl hbu =>
      cases mul_eq_zero_iff_f.mp hbu with
      | inl hb0 => exact hβ_ne hb0
      | inr hu0 => exact huk hu0
    | inr hu0 => exact huk hu0
  -- Part 2: Trace equals `c`
  have hTrace : matTrace A = c := by
    unfold matTrace A matAdd scalarMat symRankOne
    rw [finSum_add]
    have hs1 : finSum (fun i : Fin n => if i = i then a else 0) = ofNatF n * a := by
      have hc1 : finSum (fun i : Fin n => if i = i then a else 0) = finSum (fun _ : Fin n => a) :=
        finSum_congr (fun _ => by simp)
      rw [hc1, finSum_const]
    rw [hs1, finSum_scale]
    change ofNatF n * a + β * vecNormSq u = c
    rw [hu, mul_one_f]
    unfold β
    rw [OrderedField.add_comm (ofNatF n * a), OrderedField.sub_eq_add_neg,
        OrderedField.add_assoc, OrderedField.neg_add_cancel, add_zero_f]
  -- Part 3: Symmetric + Householder eigenbasis realizing `concSpec`
  have hSym : IsSymmetric A := by
    intro i j
    unfold A matAdd scalarMat symRankOne
    by_cases hij : i = j
    · subst hij; rfl
    · have hji : j ≠ i := fun h => hij h.symm
      simp [hij, hji, OrderedField.mul_comm (u i) (u j)]
  have htop_val : a + β = c - ofNatF (n - 1) * a := by
    unfold β
    have hn_eq : ofNatF n * a = ofNatF (n - 1) * a + a := by
      have hn1 : n = (n - 1) + 1 := by omega
      conv => lhs; rw [hn1]
      change (ofNatF (n - 1) + 1) * a = ofNatF (n - 1) * a + a
      rw [right_distrib_f, OrderedField.one_mul]
    rw [hn_eq, OrderedField.sub_eq_add_neg c _, neg_add_f,
        OrderedField.add_comm a _, OrderedField.add_assoc c _ a,
        OrderedField.add_assoc (- (ofNatF (n - 1) * a)) (-a) a,
        OrderedField.neg_add_cancel, add_zero_f, ← OrderedField.sub_eq_add_neg]
  -- Helper: any orthogonal Q whose 0-th column is `u` diagonalizes `A` to `concSpec`
  have h_diag_from_Q : ∀ Q : Mat n F,
      IsOrthogonal Q → (∀ i : Fin n, Q i i0 = u i) →
      ∀ j : Fin n, matVec A (fun i => Q i j) = fun i => concSpec n hn a c j * Q i j := by
    intro Q ⟨hQtQ, _⟩ hcol0 j
    funext i
    unfold matVec A matAdd scalarMat symRankOne
    have hc1 :
        finSum (fun r : Fin n => ((if i = r then a else 0) + β * (u i * u r)) * Q r j) =
        finSum (fun r : Fin n => (if i = r then a else 0) * Q r j) +
        finSum (fun r : Fin n => (β * u i) * (u r * Q r j)) := by
      rw [← finSum_add]
      apply finSum_congr
      intro r
      rw [right_distrib_f, ← OrderedField.mul_assoc β (u i) (u r), OrderedField.mul_assoc]
    rw [hc1, finSum_scale]
    have hs_a : finSum (fun r : Fin n => (if i = r then a else 0) * Q r j) = a * Q i j := by
      have hc2 :
          finSum (fun r : Fin n => (if i = r then a else 0) * Q r j) =
          finSum (fun r : Fin n => if r = i then a * Q i j else 0) := by
        apply finSum_congr
        intro r
        by_cases hri : r = i
        · subst hri; simp
        · have hir : i ≠ r := fun h => hri h.symm
          simp [hri, hir, zero_mul_f]
      rw [hc2, finSum_single]
    have hs_u : finSum (fun r : Fin n => u r * Q r j) = if i0 = j then 1 else 0 := by
      have hc3 :
          finSum (fun r : Fin n => u r * Q r j) =
          finSum (fun r : Fin n => Q r i0 * Q r j) :=
        finSum_congr (fun r => by rw [hcol0 r])
      rw [hc3]
      have hent := congrFun (congrFun hQtQ i0) j
      unfold matMul transpose scalarMat at hent
      exact hent
    rw [hs_a, hs_u]
    unfold concSpec
    by_cases hj0 : j.1 = 0
    · have hij0 : i0 = j := Fin.ext hj0.symm
      rw [if_pos hj0, if_pos hij0, mul_one_f, ← hcol0 i]
      have hj_eq : j = i0 := hij0.symm
      rw [hj_eq, ← right_distrib_f, htop_val]
    · have hij0 : i0 ≠ j := fun h => hj0 (congrArg Fin.val h).symm
      rw [if_neg hj0, if_neg hij0, mul_zero_f, add_zero_f]
  refine ⟨hRank1, hTrace, hSym, ?_⟩
  by_cases hu0 : u i0 = 1
  · -- Case `u_0 = 1`: then `u = e_0` and `Q = I_n` works directly
    have hrest0 : ∀ i : Fin n, i ≠ i0 → u i = 0 := by
      have hsp := finSum_split_at (fun i => u i * u i) i0
      change u i0 * u i0 + finSum (fun i => if i = i0 then 0 else u i * u i) = vecNormSq u at hsp
      rw [hu0, OrderedField.one_mul, hu] at hsp
      have hrem0 : finSum (fun i => if i = i0 then 0 else u i * u i) = 0 := by
        apply add_left_cancel_f (a := (1 : F))
        rw [hsp, add_zero_f]
      have hall := (finSum_eq_zero_iff_of_nonneg (fun i => by
        by_cases hi : i = i0
        · simp [hi]; exact OrderedField.le_refl 0
        · simp [hi]; exact sq_nonneg_f (u i))).mp hrem0
      intro i hi
      have hsq := hall i
      rw [if_neg hi] at hsq
      exact eq_zero_of_sq_eq_zero_f hsq
    have hIdOrth : IsOrthogonal (scalarMat n (1 : F)) := by
      constructor
      · funext i k
        unfold matMul transpose scalarMat
        have hc :
            finSum (fun j : Fin n => (if j = i then (1 : F) else 0) * (if j = k then 1 else 0)) =
            finSum (fun j : Fin n => if j = i then (if i = k then (1 : F) else 0) else 0) := by
          apply finSum_congr
          intro j
          by_cases hji : j = i
          · subst hji; simp [OrderedField.one_mul]
          · simp [hji, zero_mul_f]
        rw [hc, finSum_single]
      · funext i k
        unfold matMul transpose scalarMat
        have hc :
            finSum (fun j : Fin n => (if i = j then (1 : F) else 0) * (if k = j then 1 else 0)) =
            finSum (fun j : Fin n => if j = i then (if i = k then (1 : F) else 0) else 0) := by
          apply finSum_congr
          intro j
          by_cases hji : j = i
          · subst hji
            by_cases hik : j = k
            · subst hik; simp [OrderedField.one_mul]
            · have hki : k ≠ j := fun h => hik h.symm
              simp [hik, hki, mul_zero_f]
          · have hij : i ≠ j := fun h => hji h.symm
            simp [hji, hij, zero_mul_f]
        rw [hc, finSum_single]
    have hcol0 : ∀ i : Fin n, scalarMat n (1 : F) i i0 = u i := by
      intro i
      unfold scalarMat
      by_cases hi : i = i0
      · rw [if_pos hi, hi, hu0]
      · rw [if_neg hi, hrest0 i hi]
    exact ⟨scalarMat n 1, hIdOrth, h_diag_from_Q (scalarMat n 1) hIdOrth hcol0⟩
  · -- Case `u_0 ≠ 1`: square-root-free Householder reflection `H = I_n - (1 - u_0)⁻¹ w wᵀ`
    let e0 : Fin n → F := fun i => if i = i0 then 1 else 0
    let w : Fin n → F := fun i => u i - e0 i
    let d : F := 1 - u i0
    have hd_ne : d ≠ 0 :=
      fun hz => hu0 (sub_eq_zero_iff_f.mp hz).symm
    let γ : F := OrderedField.inv d
    have hγd : γ * d = 1 := inv_mul_cancel_f hd_ne
    have h_wnorm : vecNormSq w = (1 + 1) * d := by
      have hsp_w := finSum_split_at (fun i => w i * w i) i0
      have hsp_u := finSum_split_at (fun i => u i * u i) i0
      change w i0 * w i0 + finSum (fun i => if i = i0 then 0 else w i * w i) = vecNormSq w at hsp_w
      change u i0 * u i0 + finSum (fun i => if i = i0 then 0 else u i * u i) = vecNormSq u at hsp_u
      have htail_eq :
          finSum (fun i => if i = i0 then 0 else w i * w i) =
          finSum (fun i => if i = i0 then 0 else u i * u i) := by
        apply finSum_congr
        intro i
        by_cases hi : i = i0
        · simp [hi]
        · simp [hi, w, e0, sub_zero_f]
      have hw0 : w i0 * w i0 = u i0 * u i0 - (1 + 1) * u i0 + 1 := by
        change (u i0 - 1) * (u i0 - 1) = u i0 * u i0 - (1 + 1) * u i0 + 1
        rw [sq_sub_f, mul_one_f, OrderedField.one_mul]
      rw [htail_eq, hw0] at hsp_w
      rw [hu] at hsp_u
      -- Add `- (1 + 1) * u i0 + 1` to `hsp_u`
      calc
        vecNormSq w = (u i0 * u i0 - (1 + 1) * u i0 + 1) +
                      finSum (fun i => if i = i0 then 0 else u i * u i) := hsp_w.symm
        _ = (u i0 * u i0 + finSum (fun i => if i = i0 then 0 else u i * u i)) +
              (1 - (1 + 1) * u i0) := by
              rw [OrderedField.sub_eq_add_neg (u i0 * u i0) _,
                  OrderedField.add_assoc (u i0 * u i0) _ 1,
                  OrderedField.add_comm (- ((1 + 1) * u i0)) 1,
                  OrderedField.add_assoc (u i0 * u i0) _ _,
                  OrderedField.add_comm (1 + - ((1 + 1) * u i0)) _,
                  ← OrderedField.add_assoc (u i0 * u i0) _ _,
                  ← OrderedField.sub_eq_add_neg 1 _]
        _ = 1 + (1 - (1 + 1) * u i0) := by rw [hsp_u]
        _ = (1 + 1) - (1 + 1) * u i0 := by
              rw [OrderedField.sub_eq_add_neg, ← OrderedField.add_assoc,
                  ← OrderedField.sub_eq_add_neg]
        _ = (1 + 1) * d := by
              unfold d
              rw [mul_sub_f, mul_one_f]
    have hγ_wnorm : γ * vecNormSq w = 1 + 1 := by
      rw [h_wnorm, ← OrderedField.mul_assoc, OrderedField.mul_comm γ (1 + 1),
          OrderedField.mul_assoc, hγd, mul_one_f]
    let H : Mat n F := fun i j => scalarMat n 1 i j - γ * (w i * w j)
    have hH_sym : transpose H = H := by
      funext i j
      unfold transpose H scalarMat
      by_cases hij : i = j
      · subst hij; rfl
      · have hji : j ≠ i := fun h => hij h.symm
        simp [hij, hji, OrderedField.mul_comm (w j) (w i)]
    have hH_sq : matMul H H = scalarMat n 1 := by
      funext i k
      unfold matMul H
      let z : F := γ * (w i * w k)
      have hterm : ∀ j : Fin n,
          (scalarMat n 1 i j - γ * (w i * w j)) * (scalarMat n 1 j k - γ * (w j * w k)) =
            (scalarMat n 1 i j * scalarMat n 1 j k -
              (scalarMat n 1 i j * (γ * (w j * w k)) + (γ * (w i * w j)) * scalarMat n 1 j k)) +
            (z * γ) * (w j * w j) := by
        intro j
        have h4 :
            (γ * (w i * w j)) * (γ * (w j * w k)) = (z * γ) * (w j * w j) := by
          unfold z
          calc
            (γ * (w i * w j)) * (γ * (w j * w k))
                = γ * ((w i * w j) * (γ * (w j * w k))) := OrderedField.mul_assoc _ _ _
            _ = γ * (w i * (w j * (γ * (w j * w k)))) := by rw [OrderedField.mul_assoc (w i)]
            _ = γ * (w i * (γ * (w j * (w j * w k)))) := by
                  rw [← OrderedField.mul_assoc (w j) γ _, OrderedField.mul_comm (w j) γ,
                      OrderedField.mul_assoc γ (w j) _]
            _ = γ * (w i * (γ * ((w j * w j) * w k))) := by
                  rw [← OrderedField.mul_assoc (w j) (w j) (w k)]
            _ = γ * (w i * (w k * (γ * (w j * w j)))) := by
                  rw [← OrderedField.mul_assoc γ (w j * w j) (w k),
                      OrderedField.mul_comm (γ * (w j * w j)) (w k)]
            _ = ((γ * (w i * w k)) * γ) * (w j * w j) := by
                  rw [← OrderedField.mul_assoc (w i) (w k) _,
                      ← OrderedField.mul_assoc γ (w i * w k) _,
                      ← OrderedField.mul_assoc (γ * (w i * w k)) γ _]
        calc
          (scalarMat n 1 i j - γ * (w i * w j)) * (scalarMat n 1 j k - γ * (w j * w k))
              = scalarMat n 1 i j * (scalarMat n 1 j k - γ * (w j * w k)) -
                (γ * (w i * w j)) * (scalarMat n 1 j k - γ * (w j * w k)) := sub_mul_f _ _ _
          _ = (scalarMat n 1 i j * scalarMat n 1 j k - scalarMat n 1 i j * (γ * (w j * w k))) -
              ((γ * (w i * w j)) * scalarMat n 1 j k - (γ * (w i * w j)) * (γ * (w j * w k))) := by
                rw [mul_sub_f (scalarMat n 1 i j) (scalarMat n 1 j k) (γ * (w j * w k)),
                    mul_sub_f (γ * (w i * w j)) (scalarMat n 1 j k) (γ * (w j * w k))]
          _ = (scalarMat n 1 i j * scalarMat n 1 j k -
                (scalarMat n 1 i j * (γ * (w j * w k)) + (γ * (w i * w j)) * scalarMat n 1 j k)) +
              (z * γ) * (w j * w j) := by
                rw [h4, OrderedField.sub_eq_add_neg, OrderedField.sub_eq_add_neg,
                    OrderedField.sub_eq_add_neg, neg_add_f, neg_neg_f,
                    OrderedField.add_assoc (scalarMat n 1 i j * scalarMat n 1 j k) _ _,
                    ← OrderedField.add_assoc (- (scalarMat n 1 i j * (γ * (w j * w k)))) _ _,
                    ← OrderedField.add_assoc (scalarMat n 1 i j * scalarMat n 1 j k) _ _,
                    OrderedField.sub_eq_add_neg, neg_add_f]
      rw [finSum_congr hterm, finSum_add, finSum_sub, finSum_add, finSum_scale]
      have hs1 :
          finSum (fun j : Fin n => scalarMat n (1 : F) i j * scalarMat n (1 : F) j k) =
            scalarMat n (1 : F) i k := by
        unfold scalarMat
        have hc :
            finSum (fun j : Fin n => (if i = j then (1 : F) else 0) * (if j = k then 1 else 0)) =
            finSum (fun j : Fin n => if j = i then (if i = k then (1 : F) else 0) else 0) := by
          apply finSum_congr
          intro j
          by_cases hji : j = i
          · subst hji; simp [OrderedField.one_mul]
          · have hij : i ≠ j := fun h => hji h.symm
            simp [hji, hij, zero_mul_f]
        rw [hc, finSum_single]
      have hs2 : finSum (fun j : Fin n => scalarMat n (1 : F) i j * (γ * (w j * w k))) = z := by
        unfold scalarMat z
        have hc :
            finSum (fun j : Fin n => (if i = j then (1 : F) else 0) * (γ * (w j * w k))) =
            finSum (fun j : Fin n => if j = i then γ * (w i * w k) else 0) := by
          apply finSum_congr
          intro j
          by_cases hji : j = i
          · subst hji; simp [OrderedField.one_mul]
          · have hij : i ≠ j := fun h => hji h.symm
            simp [hji, hij, zero_mul_f]
        rw [hc, finSum_single]
      have hs3 : finSum (fun j : Fin n => (γ * (w i * w j)) * scalarMat n (1 : F) j k) = z := by
        unfold scalarMat z
        have hc :
            finSum (fun j : Fin n => (γ * (w i * w j)) * (if j = k then (1 : F) else 0)) =
            finSum (fun j : Fin n => if j = k then γ * (w i * w k) else 0) := by
          apply finSum_congr
          intro j
          by_cases hjk : j = k
          · subst hjk; simp [mul_one_f]
          · simp [hjk, mul_zero_f]
        rw [hc, finSum_single]
      unfold vecNormSq dotProd at hγ_wnorm
      rw [hs1, hs2, hs3, OrderedField.mul_assoc z γ _, hγ_wnorm]
      have hz2 : z * (1 + 1) = z + z := by
        rw [OrderedField.left_distrib, mul_one_f]
      rw [hz2, OrderedField.sub_eq_add_neg, OrderedField.add_assoc, OrderedField.neg_add_cancel,
          add_zero_f]
    have hH_orth : IsOrthogonal H := by
      constructor
      · rw [hH_sym]; exact hH_sq
      · rw [hH_sym]; exact hH_sq
    have hH_col0 : ∀ i : Fin n, H i i0 = u i := by
      intro i
      unfold H scalarMat
      have hw0 : w i0 = -d := by
        change u i0 - 1 = -(1 - u i0)
        rw [OrderedField.sub_eq_add_neg, OrderedField.sub_eq_add_neg,
            neg_add_f, neg_neg_f, OrderedField.add_comm]
      have hterm : γ * (w i * w i0) = -w i := by
        rw [hw0, mul_neg_f (w i) d, mul_neg_f γ (w i * d),
            ← OrderedField.mul_assoc γ (w i) d, OrderedField.mul_comm γ (w i),
            OrderedField.mul_assoc (w i) γ d, hγd, mul_one_f]
      rw [hterm, OrderedField.sub_eq_add_neg _ (-w i), neg_neg_f]
      change e0 i + (u i - e0 i) = u i
      rw [OrderedField.sub_eq_add_neg, OrderedField.add_comm (u i) (-e0 i),
          ← OrderedField.add_assoc, add_neg_cancel_f, OrderedField.zero_add]
    exact ⟨H, hH_orth, h_diag_from_Q H hH_orth hH_col0⟩

end SpectralAndMatrices

/-! ## Section 4: Positive Regime — Majorization & Schur-Convex Extrema on `Δ_{n,c}(a)` -/

section PositiveRegime

variable {F : Type u} [OrderedField F]

theorem sub_add_cancel_f (a b : F) : (a - b) + b = a := by
  rw [OrderedField.sub_eq_add_neg, OrderedField.add_assoc, OrderedField.neg_add_cancel, add_zero_f]

theorem add_sub_cancel_f (a b : F) : (a + b) - b = a := by
  rw [OrderedField.sub_eq_add_neg, OrderedField.add_assoc, add_neg_cancel_f, add_zero_f]

theorem sub_sub_add_cancel_f (u v w : F) : (u - (v + w)) + w = u - v := by
  rw [OrderedField.sub_eq_add_neg u (v + w), neg_add_f,
      OrderedField.add_assoc u (-v + -w) w, OrderedField.add_assoc (-v) (-w) w,
      OrderedField.neg_add_cancel, add_zero_f, ← OrderedField.sub_eq_add_neg]

theorem le_sub_of_add_le_f {a b c : F} (h : a + b ≤ c) : a ≤ c - b := by
  have h1 := add_le_add_right_f h (-b)
  rw [OrderedField.add_assoc, add_neg_cancel_f, add_zero_f, ← OrderedField.sub_eq_add_neg] at h1
  exact h1

theorem sub_le_sub_left_f {a b : F} (c : F) (h : a ≤ b) : c - b ≤ c - a := by
  rw [OrderedField.sub_eq_add_neg, OrderedField.sub_eq_add_neg]
  apply OrderedField.add_le_add_left (-b) (-a)
  rw [← sub_nonneg_iff_f, OrderedField.sub_eq_add_neg, neg_neg_f, OrderedField.add_comm]
  rw [← OrderedField.sub_eq_add_neg]
  exact sub_nonneg_iff_f.mpr h

theorem concSpec_prefix_sum {n : Nat} (hn : 0 < n) (a c : F) :
    ∀ {k : Nat} (_ : 1 ≤ k) (hk : k ≤ n),
      finSum (fun r : Fin k => concSpec n hn a c ⟨r.1, Nat.lt_of_lt_of_le r.2 hk⟩) =
        c - ofNatF (n - k) * a
  | 0, hk1, _ => by omega
  | 1, _, _ => by
    change 0 + concSpec n hn a c ⟨0, _⟩ = c - ofNatF (n - 1) * a
    rw [OrderedField.zero_add]
    unfold concSpec
    simp
  | m + 2, _, hk => by
    have hm1 : 1 ≤ m + 1 := by omega
    have hkm1 : m + 1 ≤ n := by omega
    have ih := concSpec_prefix_sum hn a c hm1 hkm1
    change finSum (fun r : Fin (m + 1) => concSpec n hn a c ⟨r.1, Nat.lt_of_lt_of_le r.2 hkm1⟩) +
            concSpec n hn a c ⟨m + 1, hk⟩ = c - ofNatF (n - (m + 2)) * a
    rw [ih]
    have hlast : concSpec n hn a c ⟨m + 1, hk⟩ = a := by
      unfold concSpec
      simp
    rw [hlast]
    have hn_step : ofNatF (n - (m + 1)) * a = ofNatF (n - (m + 2)) * a + a := by
      have hnat : n - (m + 1) = (n - (m + 2)) + 1 := by omega
      conv => lhs; rw [hnat]
      change (ofNatF (n - (m + 2)) + 1) * a = ofNatF (n - (m + 2)) * a + a
      rw [right_distrib_f, OrderedField.one_mul]
    rw [hn_step, sub_sub_add_cancel_f]

theorem concSpec_in_lowerTraceSimplex {n : Nat} (hn : 0 < n) (a c : F)
    (hc : ofNatF n * a < c) :
    LowerTraceSimplex n a c (concSpec n hn a c) := by
  have htop_gt : a < c - ofNatF (n - 1) * a := by
    apply sub_pos_iff_f.mp
    have hdiff : (c - ofNatF (n - 1) * a) - a = c - ofNatF n * a := by
      have hn_eq : ofNatF n * a = ofNatF (n - 1) * a + a := by
        have hn1 : n = (n - 1) + 1 := by omega
        conv => lhs; rw [hn1]
        change (ofNatF (n - 1) + 1) * a = ofNatF (n - 1) * a + a
        rw [right_distrib_f, OrderedField.one_mul]
      rw [hn_eq]
      calc
        (c - ofNatF (n - 1) * a) - a
            = (c + - (ofNatF (n - 1) * a)) + -a := by
                rw [OrderedField.sub_eq_add_neg, OrderedField.sub_eq_add_neg]
        _ = c + (- (ofNatF (n - 1) * a) + -a) := OrderedField.add_assoc _ _ _
        _ = c - (ofNatF (n - 1) * a + a) := by
                rw [← neg_add_f, ← OrderedField.sub_eq_add_neg]
    rw [hdiff]
    exact sub_pos_iff_f.mpr hc
  refine ⟨?_, ?_⟩
  · intro i
    unfold concSpec
    by_cases hi : i.1 = 0
    · rw [if_pos hi]; exact le_of_lt_f htop_gt
    · rw [if_neg hi]; exact OrderedField.le_refl a
  · have htr := concSpec_prefix_sum hn a c (k := n) (by omega) (Nat.le_refl n)
    have hsub0 : n - n = 0 := by omega
    rw [hsub0] at htr
    change finSum (fun r : Fin n => concSpec n hn a c r) = c - 0 * a at htr
    rw [zero_mul_f, sub_zero_f] at htr
    exact htr

/-- Universal Majorization Top on `Δ_{n,c}(a)` (Theorem 2.1):
    `concSpec` belongs to `Δ_{n,c}(a)`, is nonincreasing, and Ky-Fan-majorizes every `λ ∈ Δ_{n,c}(a)`. -/
theorem concSpec_majorizes_lowerTraceSimplex {n : Nat} (hn : 0 < n) (a c : F)
    (hc : ofNatF n * a < c) {lam : Spec n F} (hlam : LowerTraceSimplex n a c lam) :
    KyFanMajorizes (concSpec n hn a c) lam := by
  have hconc := concSpec_in_lowerTraceSimplex hn a c hc
  have htop_le : a ≤ c - ofNatF (n - 1) * a := by
    have h0 := hconc.1 ⟨0, hn⟩
    unfold concSpec at h0
    simpa using h0
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    unfold concSpec
    by_cases hj0 : j.1 = 0
    · have hi0 : i.1 = 0 := by omega
      rw [if_pos hj0, if_pos hi0]
      exact OrderedField.le_refl _
    · rw [if_neg hj0]
      by_cases hi0 : i.1 = 0
      · rw [if_pos hi0]; exact htop_le
      · rw [if_neg hi0]; exact OrderedField.le_refl a
  · rw [hlam.2, hconc.2]
  · intro k hk ι hinj
    cases k with
    | zero =>
      simp only [finSum]
      exact OrderedField.le_refl 0
    | succ m =>
      have hk1 : 1 ≤ m + 1 := by omega
      rw [concSpec_prefix_sum hn a c hk1 hk]
      have htot := finSum_subset_plus_complement ι hinj lam
      rw [show finSum lam = c from hlam.2] at htot
      have hcomp_ge :
          ofNatF (n - (m + 1)) * a ≤
            finSum (fun i : Fin n => if memImage ι i then 0 else lam i) := by
        have hones := subset_complement_ones hk ι hinj (F := F)
        have ha_sum :
            ofNatF (n - (m + 1)) * a =
              finSum (fun i : Fin n => if memImage ι i then (0 : F) else a) := by
          rw [← hones, ← finSum_scale_right]
          apply finSum_congr
          intro i
          cases memImage ι i <;> simp [zero_mul_f, OrderedField.one_mul]
        rw [ha_sum]
        apply finSum_le_finSum
        intro i
        cases memImage ι i
        · simp; exact hlam.1 i
        · simp; exact OrderedField.le_refl 0
      have h_add_le :
          finSum (fun r : Fin (m + 1) => lam (ι r)) + ofNatF (n - (m + 1)) * a ≤ c := by
        rw [← htot]
        exact OrderedField.add_le_add_left _ _ hcomp_ge _
      exact le_sub_of_add_le_f h_add_le

/-- Interval convexity predicate on `[lo, hi]`. -/
def IsConvexOn (lo hi : F) (φ : F → F) : Prop :=
  ∀ u v t : F, lo ≤ u → u ≤ hi → lo ≤ v → v ≤ hi → 0 ≤ t → t ≤ 1 →
    φ ((1 - t) * u + t * v) ≤ (1 - t) * φ u + t * φ v

/-- Separable Convex Maximization on `Δ_{n,c}(a)` (Theorem 2.2(1)):
    every convex function `φ` on `[a, c - (n-1)a]` achieves its maximum sum at `concSpec`. -/
theorem convex_sum_le_concSpec {n : Nat} (hn : 0 < n) (a c : F)
    (hc : ofNatF n * a < c) (φ : F → F)
    (hconv : IsConvexOn a (c - ofNatF (n - 1) * a) φ)
    {lam : Spec n F} (hlam : LowerTraceSimplex n a c lam) :
    finSum (fun i => φ (lam i)) ≤ finSum (fun i => φ (concSpec n hn a c i)) := by
  let s : F := c - ofNatF n * a
  have hs_pos : 0 < s := sub_pos_iff_f.mpr hc
  have hs_ne : s ≠ 0 := Ne.symm (ne_of_lt_f hs_pos)
  let hi : F := c - ofNatF (n - 1) * a
  have ha_add_s : a + s = hi := by
    unfold s hi
    have hn_eq : ofNatF n * a = ofNatF (n - 1) * a + a := by
      have hn1 : n = (n - 1) + 1 := by omega
      conv => lhs; rw [hn1]
      change (ofNatF (n - 1) + 1) * a = ofNatF (n - 1) * a + a
      rw [right_distrib_f, OrderedField.one_mul]
    rw [hn_eq, OrderedField.add_comm a _, sub_sub_add_cancel_f]
  have ha_le_hi : a ≤ hi := by
    rw [← ha_add_s]
    have h1 := OrderedField.add_le_add_left 0 s (le_of_lt_f hs_pos) a
    rwa [add_zero_f] at h1
  let x : Fin n → F := fun i => lam i - a
  have hx_nn : ∀ i, 0 ≤ x i := fun i => sub_nonneg_iff_f.mpr (hlam.1 i)
  have hx_sum : finSum x = s := by
    unfold x s
    rw [finSum_sub, finSum_const]
    exact congrArg (fun u => u - ofNatF n * a) hlam.2
  let t : Fin n → F := fun i => fdiv (x i) s
  have ht_nn : ∀ i, 0 ≤ t i :=
    fun i => mul_nonneg_f (hx_nn i) (le_of_lt_f (inv_pos_f hs_pos))
  have ht_le1 : ∀ i, t i ≤ 1 := by
    intro i
    have hsp := finSum_split_at x i
    rw [hx_sum] at hsp
    have hrem_nn : 0 ≤ finSum (fun j => if j = i then 0 else x j) := by
      apply finSum_nonneg
      intro j
      by_cases hji : j = i
      · simp [hji]; exact OrderedField.le_refl 0
      · simp [hji]; exact hx_nn j
    have hxi_le_s : x i ≤ s := by
      rw [← hsp]
      have h1 := OrderedField.add_le_add_left 0 _ hrem_nn (x i)
      rwa [add_zero_f] at h1
    have hm := mul_le_mul_of_nonneg_right_f hxi_le_s (le_of_lt_f (inv_pos_f hs_pos))
    rw [OrderedField.mul_inv_cancel s hs_ne] at hm
    exact hm
  have hpointwise : ∀ i : Fin n,
      φ (lam i) ≤ (1 - t i) * φ a + t i * φ hi := by
    intro i
    have hts : t i * s = x i := by
      unfold t fdiv
      rw [OrderedField.mul_assoc, inv_mul_cancel_f hs_ne, mul_one_f]
    have hcomb : (1 - t i) * a + t i * hi = lam i := by
      rw [← ha_add_s, sub_mul_f 1 (t i) a, OrderedField.one_mul,
          OrderedField.left_distrib (t i) a s, hts]
      calc
        a - t i * a + (t i * a + x i)
            = ((a - t i * a) + t i * a) + x i := (OrderedField.add_assoc _ _ _).symm
        _ = a + x i := by rw [sub_add_cancel_f]
        _ = lam i := by
              unfold x
              rw [OrderedField.add_comm a (lam i - a), sub_add_cancel_f]
    have hci := hconv a hi (t i) (OrderedField.le_refl a) ha_le_hi
      ha_le_hi (OrderedField.le_refl hi) (ht_nn i) (ht_le1 i)
    rwa [hcomb] at hci
  have hsum_le := finSum_le_finSum hpointwise
  have ht_sum : finSum t = 1 := by
    unfold t fdiv
    rw [finSum_scale_right, hx_sum, OrderedField.mul_inv_cancel s hs_ne]
  have hrhs_eq :
      finSum (fun i : Fin n => (1 - t i) * φ a + t i * φ hi) =
        finSum (fun i : Fin n => φ (concSpec n hn a c i)) := by
    rw [finSum_add, finSum_scale_right _ (φ a), finSum_scale_right _ (φ hi),
        finSum_sub, finSum_const n 1, mul_one_f, ht_sum, OrderedField.one_mul]
    have hn1_eq : ofNatF n - (1 : F) = ofNatF (n - 1) := by
      have hn1 : n = (n - 1) + 1 := by omega
      conv => lhs; rw [hn1]
      change (ofNatF (n - 1) + (1 : F)) - 1 = ofNatF (n - 1)
      exact add_sub_cancel_f (ofNatF (n - 1)) 1
    rw [hn1_eq]
    have hsp := finSum_split_at (fun i => φ (concSpec n hn a c i)) ⟨0, hn⟩
    rw [← hsp]
    have h0 : φ (concSpec n hn a c ⟨0, hn⟩) = φ hi := by
      unfold concSpec hi; simp
    have htail :
        finSum (fun i : Fin n => if i = ⟨0, hn⟩ then 0 else φ (concSpec n hn a c i)) =
          ofNatF (n - 1) * φ a := by
      have hsp1 := finSum_split_at (fun _ : Fin n => φ a) ⟨0, hn⟩
      rw [finSum_const] at hsp1
      have hcongr :
          finSum (fun i : Fin n => if i = ⟨0, hn⟩ then 0 else φ (concSpec n hn a c i)) =
          finSum (fun i : Fin n => if i = ⟨0, hn⟩ then 0 else φ a) := by
        apply finSum_congr
        intro i
        by_cases hi0 : i = ⟨0, hn⟩
        · simp [hi0]
        · have hval : i.1 ≠ 0 := fun hv => hi0 (Fin.ext hv)
          unfold concSpec
          simp [hi0, hval]
      rw [hcongr]
      apply add_left_cancel_f (a := φ a)
      rw [hsp1]
      have hn_phi : ofNatF n * φ a = φ a + ofNatF (n - 1) * φ a := by
        have hn1 : n = (n - 1) + 1 := by omega
        conv => lhs; rw [hn1]
        change (ofNatF (n - 1) + 1) * φ a = φ a + ofNatF (n - 1) * φ a
        rw [right_distrib_f, OrderedField.one_mul, OrderedField.add_comm]
      exact hn_phi
    rw [h0, htail, OrderedField.add_comm]
  rwa [hrhs_eq] at hsum_le

/-- Sum of squares `∑ λ_i²` and off-diagonal ordered-pair sum `∑_{i ≠ j} x_i x_j`. -/
def specSumSq {n : Nat} (lam : Spec n F) : F :=
  finSum (fun i => lam i * lam i)

def offDiagPairSum {n : Nat} (x : Spec n F) : F :=
  finSum (fun i => finSum (fun j => if i = j then 0 else x i * x j))

theorem sq_finSum_eq_sumSq_add_offDiag {n : Nat} (x : Spec n F) :
    finSum x * finSum x = specSumSq x + offDiagPairSum x := by
  rw [finSum_mul_finSum]
  unfold specSumSq offDiagPairSum
  rw [← finSum_add]
  apply finSum_congr
  intro i
  rw [← finSum_single i (x i * x i), ← finSum_add]
  apply finSum_congr
  intro j
  by_cases hij : j = i
  · subst hij; simp [add_zero_f]
  · have hji : i ≠ j := fun h => hij h.symm
    simp [hij, hji, OrderedField.zero_add]

theorem specSumSq_shift {n : Nat} (lam : Spec n F) (a : F) :
    specSumSq lam =
      specSumSq (fun i => lam i - a) +
      ((1 + 1) * a) * finSum (fun i => lam i - a) +
      ofNatF n * (a * a) := by
  unfold specSumSq
  have hterm : ∀ i : Fin n,
      lam i * lam i =
        ((lam i - a) * (lam i - a) + ((1 + 1) * a) * (lam i - a)) + a * a := by
    intro i
    have hl : lam i = (lam i - a) + a := (sub_add_cancel_f (lam i) a).symm
    conv => lhs; rw [hl]
    rw [sq_add_f (lam i - a) a]
    apply congrArg (fun u => u + a * a)
    apply congrArg (fun u => (lam i - a) * (lam i - a) + u)
    rw [OrderedField.mul_assoc (1 + 1) a (lam i - a), OrderedField.mul_comm a (lam i - a)]
  rw [finSum_congr hterm, finSum_add, finSum_add, finSum_scale, finSum_const]

/-- Strict Quadratic Maximization & Uniqueness on `Δ_{n,c}(a)` (Theorem 2.2(2)):
    `∑ (λ_i^conc)² - ∑ λ_i² = ∑_{i ≠ j} (λ_i - a)(λ_j - a) ≥ 0`, with equality iff `λ` is floor-concentrated. -/
theorem specSumSq_eq_concSpec_iff {n : Nat} (hn : 0 < n) (a c : F)
    (hc : ofNatF n * a < c) {lam : Spec n F} (hlam : LowerTraceSimplex n a c lam) :
    specSumSq (concSpec n hn a c) - specSumSq lam =
      offDiagPairSum (fun i => lam i - a) ∧
    specSumSq lam ≤ specSumSq (concSpec n hn a c) ∧
    (specSumSq lam = specSumSq (concSpec n hn a c) ↔ IsConcentratedFloor a lam) := by
  have hconc := concSpec_in_lowerTraceSimplex hn a c hc
  let x : Spec n F := fun i => lam i - a
  let xc : Spec n F := fun i => concSpec n hn a c i - a
  have hx_nn : ∀ i, 0 ≤ x i := fun i => sub_nonneg_iff_f.mpr (hlam.1 i)
  have hx_sum : finSum x = c - ofNatF n * a := by
    unfold x; rw [finSum_sub, finSum_const, show finSum lam = c from hlam.2]
  have hxc_sum : finSum xc = c - ofNatF n * a := by
    unfold xc; rw [finSum_sub, finSum_const, show finSum (concSpec n hn a c) = c from hconc.2]
  have hxc_off0 : offDiagPairSum xc = 0 := by
    unfold offDiagPairSum
    apply (finSum_eq_zero_iff_of_nonneg (fun i => finSum_nonneg (fun j => by
      by_cases hij : i = j
      · simp [hij]; exact OrderedField.le_refl 0
      · simp [hij]
        exact mul_nonneg_f (sub_nonneg_iff_f.mpr (hconc.1 i))
                           (sub_nonneg_iff_f.mpr (hconc.1 j))))).mpr
    intro i
    apply (finSum_eq_zero_iff_of_nonneg (fun j => by
      by_cases hij : i = j
      · simp [hij]; exact OrderedField.le_refl 0
      · simp [hij]
        exact mul_nonneg_f (sub_nonneg_iff_f.mpr (hconc.1 i))
                           (sub_nonneg_iff_f.mpr (hconc.1 j)))).mpr
    intro j
    by_cases hij : i = j
    · simp [hij]
    · simp only [if_neg hij]
      by_cases hi0 : i.1 = 0
      · have hj0 : j.1 ≠ 0 := fun hv => hij (Fin.ext (hi0.trans hv.symm))
        have hxj0 : xc j = 0 := by
          unfold xc concSpec
          rw [if_neg hj0, sub_self_f]
        rw [hxj0, mul_zero_f]
      · have hxi0 : xc i = 0 := by
          unfold xc concSpec
          rw [if_neg hi0, sub_self_f]
        rw [hxi0, zero_mul_f]
  have hxc_sq : specSumSq xc = finSum x * finSum x := by
    have h1 := sq_finSum_eq_sumSq_add_offDiag xc
    rw [hxc_off0, add_zero_f, hxc_sum, ← hx_sum] at h1
    exact h1.symm
  have hgap : specSumSq (concSpec n hn a c) - specSumSq lam = offDiagPairSum x := by
    have hs_lam := specSumSq_shift lam a
    have hs_conc := specSumSq_shift (concSpec n hn a c) a
    calc
      specSumSq (concSpec n hn a c) - specSumSq lam
          = (specSumSq xc + (((1 + 1) * a) * finSum xc + ofNatF n * (a * a))) -
            (specSumSq x + (((1 + 1) * a) * finSum x + ofNatF n * (a * a))) := by
              rw [hs_conc, hs_lam, OrderedField.add_assoc (specSumSq xc),
                  OrderedField.add_assoc (specSumSq x)]
      _ = specSumSq xc - specSumSq x := by
              rw [hxc_sum, hx_sum]
              let tail := ((1 + 1) * a) * (c - ofNatF n * a) + ofNatF n * (a * a)
              change (specSumSq xc + tail) - (specSumSq x + tail) = specSumSq xc - specSumSq x
              rw [OrderedField.sub_eq_add_neg, neg_add_f, OrderedField.add_assoc (specSumSq xc),
                  OrderedField.add_comm (-specSumSq x) (-tail),
                  ← OrderedField.add_assoc tail (-tail) (-specSumSq x),
                  add_neg_cancel_f, OrderedField.zero_add, ← OrderedField.sub_eq_add_neg]
      _ = (specSumSq x + offDiagPairSum x) - specSumSq x := by
              rw [hxc_sq, sq_finSum_eq_sumSq_add_offDiag]
      _ = offDiagPairSum x := by
              rw [OrderedField.add_comm (specSumSq x), add_sub_cancel_f]
  have hoff_nn : 0 ≤ offDiagPairSum x :=
    finSum_nonneg (fun i => finSum_nonneg (fun j => by
      by_cases hij : i = j
      · simp [hij]; exact OrderedField.le_refl 0
      · simp [hij]; exact mul_nonneg_f (hx_nn i) (hx_nn j)))
  have hle : specSumSq lam ≤ specSumSq (concSpec n hn a c) := by
    apply sub_nonneg_iff_f.mp
    rw [hgap]
    exact hoff_nn
  refine ⟨hgap, hle, ?_⟩
  constructor
  · intro heq
    have hoff0 : offDiagPairSum x = 0 := by
      rw [← hgap, heq, sub_self_f]
    have houter0 := (finSum_eq_zero_iff_of_nonneg (fun i => finSum_nonneg (fun j => by
      by_cases hij : i = j
      · simp [hij]; exact OrderedField.le_refl 0
      · simp [hij]; exact mul_nonneg_f (hx_nn i) (hx_nn j)))).mp hoff0
    have hpair0 : ∀ i j : Fin n, i ≠ j → x i * x j = 0 := by
      intro i j hij
      have hinner0 := (finSum_eq_zero_iff_of_nonneg (fun r => by
        by_cases hir : i = r
        · simp [hir]; exact OrderedField.le_refl 0
        · simp [hir]; exact mul_nonneg_f (hx_nn i) (hx_nn r))).mp (houter0 i) j
      simpa [hij] using hinner0
    have hex_pos : ∃ k : Fin n, 0 < x k := by
      by_cases hex : ∃ k : Fin n, 0 < x k
      · exact hex
      · exfalso
        have hall0 : ∀ k : Fin n, x k = 0 := by
          intro k
          by_cases hkz : x k = 0
          · exact hkz
          · exact False.elim (hex ⟨k, lt_of_le_of_ne_f (hx_nn k) (Ne.symm hkz)⟩)
        have hs0 : finSum x = 0 := (finSum_eq_zero_iff_of_nonneg hx_nn).mpr hall0
        rw [hx_sum] at hs0
        exact (ne_of_lt_f (sub_pos_iff_f.mpr hc)) hs0.symm
    obtain ⟨k, hxk_pos⟩ := hex_pos
    refine ⟨k, sub_pos_iff_f.mp hxk_pos, ?_⟩
    intro i hik
    have hprod0 := hpair0 k i (Ne.symm hik)
    cases mul_eq_zero_iff_f.mp hprod0 with
    | inl hkz => exact False.elim (ne_of_lt_f hxk_pos hkz.symm)
    | inr hiz => exact sub_eq_zero_iff_f.mp hiz
  · intro ⟨k, _, hrest⟩
    have hoff0 : offDiagPairSum x = 0 := by
      unfold offDiagPairSum
      have hc1 :
          finSum (fun i : Fin n => finSum (fun j : Fin n => if i = j then 0 else x i * x j)) =
          finSum (fun _ : Fin n => (0 : F)) := by
        apply finSum_congr
        intro i
        have hc2 :
            finSum (fun j : Fin n => if i = j then 0 else x i * x j) =
            finSum (fun _ : Fin n => (0 : F)) := by
          apply finSum_congr
          intro j
          by_cases hij : i = j
          · simp [hij]
          · simp only [if_neg hij]
            by_cases hik : i = k
            · have hjk : j ≠ k := fun h => hij (hik.trans h.symm)
              have hxj0 : x j = 0 := by unfold x; rw [hrest j hjk, sub_self_f]
              rw [hxj0, mul_zero_f]
            · have hxi0 : x i = 0 := by unfold x; rw [hrest i hik, sub_self_f]
              rw [hxi0, zero_mul_f]
        rw [hc2, finSum_const, mul_zero_f]
      rw [hc1, finSum_const, mul_zero_f]
    rw [hoff0] at hgap
    exact (sub_eq_zero_iff_f.mp hgap).symm

end PositiveRegime

/-! ## Section 5: The Three Independent Refutations (R1, R2, R3) -/

section Refutations

variable {F : Type u} [OrderedField F]

/-! ### Refutation R1: Schur-Concave Fixed-Trace Extrema (`det` and `e_2`) -/

private theorem finProd_zero_of_exists_zero {n : Nat} {f : Fin n → F}
    (k : Fin n) (hk : f k = 0) : finProd f = 0 := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    simp only [finProd]
    by_cases hlt : k.1 < n
    · have hp0 : finProd (fun i : Fin n => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) = 0 :=
        ih ⟨k.1, hlt⟩ (by
          have heq : (⟨k.1, Nat.lt_succ_of_lt hlt⟩ : Fin (n + 1)) = k := Fin.ext rfl
          rw [heq, hk])
      rw [hp0, zero_mul_f]
    · have heq : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = k := Fin.ext (by dsimp; omega)
      rw [heq, hk, mul_zero_f]

/-- Refutation R1 (Theorem 3.2): on the PSD fixed-trace simplex `Δ_{n,c}(0)` (`n ≥ 2`, `c > 0`),
    both `∏ λ_i = det(diag λ)` and `2 e_2(λ) = offDiagPairSum λ` achieve their unique global maximum
    at the uniform spectrum `(c/n, ..., c/n)`, while every concentrated spectrum achieves `0`. -/
theorem refutation_R1_det_and_elemSymm2 {n : Nat} (hn2 : 2 ≤ n) (c : F) (hc : 0 < c) :
    let hn : 0 < n := by omega
    let uSpec := unifSpec n hn c
    PSDTraceSimplex n c uSpec ∧
    ¬ IsConcentratedFloor 0 uSpec ∧
    (∀ lam : Spec n F, PSDTraceSimplex n c lam →
      finProd lam ≤ finProd uSpec ∧
      (finProd lam = finProd uSpec ↔ ∀ i : Fin n, lam i = uSpec i)) ∧
    (∀ lam : Spec n F, PSDTraceSimplex n c lam →
      offDiagPairSum lam ≤ offDiagPairSum uSpec ∧
      (offDiagPairSum lam = offDiagPairSum uSpec ↔ ∀ i : Fin n, lam i = uSpec i)) ∧
    (∀ lam_c : Spec n F, IsConcentratedFloor 0 lam_c →
      finProd lam_c = 0 ∧ offDiagPairSum lam_c = 0 ∧
      finProd lam_c < finProd uSpec ∧ offDiagPairSum lam_c < offDiagPairSum uSpec) := by
  intro hn uSpec
  let u : F := fdiv c (ofNatF n)
  have hn_pos : (0 : F) < ofNatF n := ofNatF_pos hn
  have hn_ne : (ofNatF n : F) ≠ 0 := ofNatF_ne_zero hn
  have hu_pos : 0 < u := OrderedField.mul_pos _ _ hc (inv_pos_f hn_pos)
  have hnu : ofNatF n * u = c := by
    unfold u fdiv
    rw [OrderedField.mul_comm (ofNatF n), OrderedField.mul_assoc, inv_mul_cancel_f hn_ne, mul_one_f]
  have hu_in : PSDTraceSimplex n c uSpec := by
    refine ⟨fun _ => le_of_lt_f hu_pos, ?_⟩
    unfold specTrace uSpec
    rw [finSum_const]
    exact hnu
  have hnot_conc : ¬ IsConcentratedFloor 0 uSpec := by
    intro ⟨k, _, hrest⟩
    let j : Fin n := if k.1 = 0 then ⟨1, by omega⟩ else ⟨0, hn⟩
    have hjk : j ≠ k := by
      unfold j
      by_cases hk0 : k.1 = 0
      · simp [hk0]
        intro he
        have hv : 1 = k.1 := congrArg Fin.val he
        omega
      · simp [hk0]
        intro he
        exact hk0 (congrArg Fin.val he).symm
    have huj0 : uSpec j = 0 := hrest j hjk
    unfold uSpec at huj0
    exact (ne_of_lt_f hu_pos) huj0.symm
  have hdet_max : ∀ lam : Spec n F, PSDTraceSimplex n c lam →
      finProd lam ≤ finProd uSpec ∧
      (finProd lam = finProd uSpec ↔ ∀ i : Fin n, lam i = uSpec i) := by
    intro lam hlam
    obtain ⟨hle, heq⟩ := am_gm_complete hn lam hlam.1
    have hm_eq : fdiv (finSum lam) (ofNatF n) = u := by
      unfold u
      rw [show finSum lam = c from hlam.2]
    have hpu : finProd uSpec = fpow u n := finProd_const n u
    rw [hm_eq, ← hpu] at hle heq
    exact ⟨hle, heq⟩
  have he2_max : ∀ lam : Spec n F, PSDTraceSimplex n c lam →
      offDiagPairSum lam ≤ offDiagPairSum uSpec ∧
      (offDiagPairSum lam = offDiagPairSum uSpec ↔ ∀ i : Fin n, lam i = uSpec i) := by
    intro lam hlam
    let dev : Spec n F := fun i => lam i - u
    have hdev_sum0 : finSum dev = 0 := by
      unfold dev
      rw [finSum_sub, show finSum lam = c from hlam.2, finSum_const, hnu, sub_self_f]
    have hsq_lam : specSumSq lam = specSumSq dev + ofNatF n * (u * u) := by
      have hs := specSumSq_shift lam u
      change specSumSq lam = specSumSq dev + ((1 + 1) * u) * finSum dev + ofNatF n * (u * u) at hs
      rw [hdev_sum0, mul_zero_f, add_zero_f] at hs
      exact hs
    have hsq_u : specSumSq uSpec = ofNatF n * (u * u) := finSum_const n (u * u)
    have htot_lam := sq_finSum_eq_sumSq_add_offDiag lam
    have htot_u := sq_finSum_eq_sumSq_add_offDiag uSpec
    rw [show finSum lam = c from hlam.2] at htot_lam
    rw [show finSum uSpec = c from hu_in.2] at htot_u
    have he2_diff : offDiagPairSum uSpec - offDiagPairSum lam = specSumSq dev := by
      apply add_left_cancel_f (a := specSumSq uSpec)
      calc
        specSumSq uSpec + (offDiagPairSum uSpec - offDiagPairSum lam)
            = (specSumSq uSpec + offDiagPairSum uSpec) - offDiagPairSum lam := by
                rw [OrderedField.sub_eq_add_neg, ← OrderedField.add_assoc,
                    ← OrderedField.sub_eq_add_neg]
        _ = (specSumSq lam + offDiagPairSum lam) - offDiagPairSum lam := by
                rw [← htot_u, ← htot_lam]
        _ = specSumSq lam := add_sub_cancel_f _ _
        _ = specSumSq uSpec + specSumSq dev := by
                rw [hsq_lam, hsq_u, OrderedField.add_comm]
    have hdev_nn : 0 ≤ specSumSq dev := finSum_nonneg (fun i => sq_nonneg_f (dev i))
    have hle : offDiagPairSum lam ≤ offDiagPairSum uSpec := by
      apply sub_nonneg_iff_f.mp
      rw [he2_diff]
      exact hdev_nn
    refine ⟨hle, ?_⟩
    constructor
    · intro heq
      have hdev0 : specSumSq dev = 0 := by rw [← he2_diff, heq, sub_self_f]
      have hall0 := (finSum_eq_zero_iff_of_nonneg (fun i => sq_nonneg_f (dev i))).mp hdev0
      intro i
      exact sub_eq_zero_iff_f.mp (eq_zero_of_sq_eq_zero_f (hall0 i))
    · intro hall
      have hdev0 : specSumSq dev = 0 := by
        apply (finSum_eq_zero_iff_of_nonneg (fun i => sq_nonneg_f (dev i))).mpr
        intro i
        have hi0 : dev i = 0 := by unfold dev; rw [hall i]; exact sub_self_f u
        rw [hi0, mul_zero_f]
      rw [hdev0] at he2_diff
      exact (sub_eq_zero_iff_f.mp he2_diff).symm
  refine ⟨hu_in, hnot_conc, hdet_max, he2_max, ?_⟩
  intro lam_c ⟨k, _, hrest⟩
  let j : Fin n := if k.1 = 0 then ⟨1, by omega⟩ else ⟨0, hn⟩
  have hjk : j ≠ k := by
    unfold j
    by_cases hk0 : k.1 = 0
    · simp [hk0]; intro he; have hv : 1 = k.1 := congrArg Fin.val he; omega
    · simp [hk0]; intro he; exact hk0 (congrArg Fin.val he).symm
  have hp0 : finProd lam_c = 0 := finProd_zero_of_exists_zero j (hrest j hjk)
  have hoff0 : offDiagPairSum lam_c = 0 := by
    unfold offDiagPairSum
    have hc1 :
        finSum (fun i : Fin n => finSum (fun r : Fin n => if i = r then 0 else lam_c i * lam_c r)) =
        finSum (fun _ : Fin n => (0 : F)) := by
      apply finSum_congr
      intro i
      have hc2 :
          finSum (fun r : Fin n => if i = r then 0 else lam_c i * lam_c r) =
          finSum (fun _ : Fin n => (0 : F)) := by
        apply finSum_congr
        intro r
        by_cases hir : i = r
        · simp [hir]
        · simp only [if_neg hir]
          by_cases hik : i = k
          · have hrk : r ≠ k := fun h => hir (hik.trans h.symm)
            rw [hrest r hrk, mul_zero_f]
          · rw [hrest i hik, zero_mul_f]
      rw [hc2, finSum_const, mul_zero_f]
    rw [hc1, finSum_const, mul_zero_f]
  have hpu_pos : 0 < finProd uSpec := by
    rw [finProd_const]
    exact fpow_pos hu_pos n
  have he2_pos : 0 < offDiagPairSum uSpec := by
    -- Pick distinct indices `0` and `1`: term `(0, 1)` is `u * u > 0`
    let i0 : Fin n := ⟨0, hn⟩
    let i1 : Fin n := ⟨1, hn2⟩
    have hi01 : i0 ≠ i1 := fun h => by have hv : (0 : Nat) = 1 := congrArg Fin.val h; omega
    have hsp_out := finSum_split_at
      (fun i : Fin n => finSum (fun r : Fin n => if i = r then 0 else uSpec i * uSpec r)) i0
    have hsp_in := finSum_split_at
      (fun r : Fin n => if i0 = r then 0 else uSpec i0 * uSpec r) i1
    have hterm_pos : 0 < (if i0 = i1 then (0 : F) else uSpec i0 * uSpec i1) := by
      rw [if_neg hi01]
      exact OrderedField.mul_pos _ _ hu_pos hu_pos
    have hin_nn : 0 ≤ finSum (fun r : Fin n =>
        if r = i1 then 0 else (if i0 = r then 0 else uSpec i0 * uSpec r)) := by
      apply finSum_nonneg
      intro r
      by_cases hr1 : r = i1
      · simp [hr1]; exact OrderedField.le_refl 0
      · simp only [if_neg hr1]
        by_cases h0r : i0 = r
        · simp [h0r]; exact OrderedField.le_refl 0
        · simp [h0r]; exact mul_nonneg_f (le_of_lt_f hu_pos) (le_of_lt_f hu_pos)
    have hin_pos : 0 < finSum (fun r : Fin n => if i0 = r then 0 else uSpec i0 * uSpec r) := by
      rw [← hsp_in]
      have h1 := add_lt_add_of_lt_of_le_f hterm_pos hin_nn
      rwa [add_zero_f] at h1
    have hout_nn : 0 ≤ finSum (fun i : Fin n =>
        if i = i0 then 0 else finSum (fun r : Fin n => if i = r then 0 else uSpec i * uSpec r)) := by
      apply finSum_nonneg
      intro i
      by_cases hi : i = i0
      · simp [hi]; exact OrderedField.le_refl 0
      · simp only [if_neg hi]
        apply finSum_nonneg
        intro r
        by_cases hir : i = r
        · simp [hir]; exact OrderedField.le_refl 0
        · simp [hir]; exact mul_nonneg_f (le_of_lt_f hu_pos) (le_of_lt_f hu_pos)
    unfold offDiagPairSum
    rw [← hsp_out]
    have h2 := add_lt_add_of_lt_of_le_f hin_pos hout_nn
    rwa [add_zero_f] at h2
  refine ⟨hp0, hoff0, ?_, ?_⟩
  · rwa [hp0]
  · rwa [hoff0]

/-! ### Refutation R2: Box-Constrained Extrema and Complete Rank-One Classification -/

/-- Saturated majorization-greatest profile on `B_{n,c}(a,b)` with `q` entries at `b`,
    `1` entry at `c - q b - (n - 1 - q) a`, and `n - 1 - q` entries at `a`. -/
def boxSpec (n : Nat) (a b c : F) (q : Nat) : Spec n F :=
  fun i =>
    if i.1 < q then b
    else if i.1 = q then c - ofNatF q * b - ofNatF (n - 1 - q) * a
    else a

theorem boxSpec_prefix_sum {n q : Nat} (hqn : q < n) (a b c : F) :
    ∀ (k : Nat) (hk : k ≤ n),
      finSum (fun r : Fin k => boxSpec n a b c q ⟨r.1, Nat.lt_of_lt_of_le r.2 hk⟩) =
        if k ≤ q then ofNatF k * b else c - ofNatF (n - k) * a
  | 0, _ => by
    have h0 : 0 ≤ q := Nat.zero_le q
    rw [if_pos h0]
    simp [finSum, ofNatF, zero_mul_f]
  | k + 1, hk => by
    have hkn : k ≤ n := by omega
    have ih := boxSpec_prefix_sum hqn a b c k hkn
    change finSum (fun r : Fin k => boxSpec n a b c q ⟨r.1, Nat.lt_of_lt_of_le r.2 hkn⟩) +
            boxSpec n a b c q ⟨k, hk⟩ =
           if k + 1 ≤ q then ofNatF (k + 1) * b else c - ofNatF (n - (k + 1)) * a
    rw [ih]
    by_cases hkq1 : k + 1 ≤ q
    · have hkq : k ≤ q := by omega
      have hlt : k < q := by omega
      rw [if_pos hkq, if_pos hkq1]
      unfold boxSpec
      simp only [hlt, ite_true]
      change ofNatF k * b + b = (ofNatF k + 1) * b
      rw [right_distrib_f, OrderedField.one_mul]
    · rw [if_neg hkq1]
      by_cases hkeq : k = q
      · subst hkeq
        rw [if_pos (Nat.le_refl k)]
        unfold boxSpec
        have hnotlt : ¬ (k < k) := Nat.lt_irrefl k
        simp only [hnotlt, ite_false, ite_true]
        have hn_sub : n - 1 - k = n - (k + 1) := by omega
        rw [hn_sub]
        calc
          ofNatF k * b + ((c - ofNatF k * b) - ofNatF (n - (k + 1)) * a)
              = (ofNatF k * b + (c - ofNatF k * b)) - ofNatF (n - (k + 1)) * a := by
                  rw [OrderedField.sub_eq_add_neg (c - ofNatF k * b),
                      ← OrderedField.add_assoc, ← OrderedField.sub_eq_add_neg]
          _ = c - ofNatF (n - (k + 1)) * a := by
                  rw [OrderedField.add_comm (ofNatF k * b), sub_add_cancel_f]
      · have hkgt : ¬ (k ≤ q) := by omega
        have hnotlt : ¬ (k < q) := by omega
        rw [if_neg hkgt]
        unfold boxSpec
        simp only [hnotlt, hkeq, ite_false]
        have hn_step : ofNatF (n - k) * a = ofNatF (n - (k + 1)) * a + a := by
          have hnat : n - k = (n - (k + 1)) + 1 := by omega
          conv => lhs; rw [hnat]
          change (ofNatF (n - (k + 1)) + 1) * a = ofNatF (n - (k + 1)) * a + a
          rw [right_distrib_f, OrderedField.one_mul]
        rw [hn_step, sub_sub_add_cancel_f]

private theorem boxSpec_mid_eq {n q : Nat} (hqn : q < n) (a b c : F) :
    c - ofNatF q * b - ofNatF (n - 1 - q) * a =
      a + ((c - ofNatF n * a) - ofNatF q * (b - a)) := by
  have hn_split : ofNatF n * a = ofNatF q * a + a + ofNatF (n - 1 - q) * a := by
    have hnat : n = (q + 1) + (n - 1 - q) := by omega
    conv => lhs; rw [hnat]
    rw [ofNatF_add, right_distrib_f]
    change (ofNatF q + 1) * a + ofNatF (n - 1 - q) * a = ofNatF q * a + a + ofNatF (n - 1 - q) * a
    rw [right_distrib_f, OrderedField.one_mul]
  apply add_right_cancel_f (c := ofNatF q * b + ofNatF (n - 1 - q) * a)
  have hlhs :
      (c - ofNatF q * b - ofNatF (n - 1 - q) * a) +
        (ofNatF q * b + ofNatF (n - 1 - q) * a) = c := by
    calc
      (c - ofNatF q * b - ofNatF (n - 1 - q) * a) +
          (ofNatF q * b + ofNatF (n - 1 - q) * a)
          = ((c - ofNatF q * b - ofNatF (n - 1 - q) * a) + ofNatF (n - 1 - q) * a) +
              ofNatF q * b := by
              rw [OrderedField.add_comm (ofNatF q * b), ← OrderedField.add_assoc]
      _ = (c - ofNatF q * b) + ofNatF q * b := by rw [sub_add_cancel_f]
      _ = c := sub_add_cancel_f _ _
  rw [hlhs]
  symm
  calc
    (a + ((c - ofNatF n * a) - ofNatF q * (b - a))) +
        (ofNatF q * b + ofNatF (n - 1 - q) * a)
        = (((c - ofNatF n * a) - ofNatF q * b + ofNatF q * a) + ofNatF q * b) +
            (a + ofNatF (n - 1 - q) * a) := by
            rw [mul_sub_f (ofNatF q) b a,
                OrderedField.sub_eq_add_neg (c - ofNatF n * a) _,
                OrderedField.sub_eq_add_neg (ofNatF q * b) _,
                neg_add_f, neg_neg_f,
                ← OrderedField.add_assoc (c - ofNatF n * a) (- (ofNatF q * b)) (ofNatF q * a),
                ← OrderedField.sub_eq_add_neg (c - ofNatF n * a) (ofNatF q * b),
                OrderedField.add_comm a _,
                OrderedField.add_assoc ((c - ofNatF n * a) - ofNatF q * b + ofNatF q * a) a _,
                OrderedField.add_comm a (ofNatF q * b + ofNatF (n - 1 - q) * a),
                OrderedField.add_assoc (ofNatF q * b) (ofNatF (n - 1 - q) * a) a,
                OrderedField.add_comm (ofNatF (n - 1 - q) * a) a,
                ← OrderedField.add_assoc]
    _ = ((c - ofNatF n * a) + ofNatF q * a) + (a + ofNatF (n - 1 - q) * a) := by
            apply congrArg (fun u => u + (a + ofNatF (n - 1 - q) * a))
            rw [OrderedField.add_assoc _ (ofNatF q * a) (ofNatF q * b),
                OrderedField.add_comm (ofNatF q * a) (ofNatF q * b),
                ← OrderedField.add_assoc, sub_add_cancel_f]
    _ = (c - ofNatF n * a) + ofNatF n * a := by
            rw [OrderedField.add_assoc (c - ofNatF n * a),
                ← OrderedField.add_assoc (ofNatF q * a) a _, ← hn_split]
    _ = c := sub_add_cancel_f _ _

/-- Box-Constrained Majorization Top (Theorem 4.2(1)):
    `boxSpec` belongs to `B_{n,c}(a,b)`, is nonincreasing, and Ky-Fan-majorizes every `λ ∈ B_{n,c}(a,b)`. -/
theorem boxSpec_majorizes_boxTracePolytope {n q : Nat} (hqn : q < n) (a b c : F)
    (hq_lo : ofNatF q * (b - a) ≤ c - ofNatF n * a)
    (hq_hi : c - ofNatF n * a < ofNatF (q + 1) * (b - a)) :
    BoxTracePolytope n a b c (boxSpec n a b c q) ∧
    (∀ lam : Spec n F, BoxTracePolytope n a b c lam →
      KyFanMajorizes (boxSpec n a b c q) lam) := by
  let r_val : F := c - ofNatF q * b - ofNatF (n - 1 - q) * a
  have hr_eq : r_val = a + ((c - ofNatF n * a) - ofNatF q * (b - a)) :=
    boxSpec_mid_eq hqn a b c
  have ha_le_r : a ≤ r_val := by
    rw [hr_eq]
    have hnn : 0 ≤ (c - ofNatF n * a) - ofNatF q * (b - a) := sub_nonneg_iff_f.mpr hq_lo
    have h1 := OrderedField.add_le_add_left 0 _ hnn a
    rwa [add_zero_f] at h1
  have hr_lt_b : r_val < b := by
    rw [hr_eq]
    have hdiff_lt : (c - ofNatF n * a) - ofNatF q * (b - a) < b - a := by
      have hq1 : ofNatF (q + 1) * (b - a) = (b - a) + ofNatF q * (b - a) := by
        change (ofNatF q + 1) * (b - a) = (b - a) + ofNatF q * (b - a)
        rw [right_distrib_f, OrderedField.one_mul, OrderedField.add_comm]
      rw [hq1] at hq_hi
      have h1 := add_lt_add_right_f hq_hi (- (ofNatF q * (b - a)))
      rw [OrderedField.add_assoc, add_neg_cancel_f, add_zero_f, ← OrderedField.sub_eq_add_neg] at h1
      exact h1
    have h2 := add_lt_add_left_f hdiff_lt a
    rwa [OrderedField.add_comm a (b - a), sub_add_cancel_f] at h2
  have hr_le_b : r_val ≤ b := le_of_lt_f hr_lt_b
  have ha_le_b : a ≤ b := OrderedField.le_trans _ _ _ ha_le_r hr_le_b
  have htr_box : specTrace (boxSpec n a b c q) = c := by
    have hp := boxSpec_prefix_sum hqn a b c n (Nat.le_refl n)
    have hnot : ¬ (n ≤ q) := by omega
    have hsub0 : n - n = 0 := by omega
    rw [if_neg hnot, hsub0, ofNatF, zero_mul_f, sub_zero_f] at hp
    exact hp
  have hbox_in : BoxTracePolytope n a b c (boxSpec n a b c q) := by
    refine ⟨?_, htr_box⟩
    intro i
    unfold boxSpec
    by_cases h1 : i.1 < q
    · rw [if_pos h1]; exact ⟨ha_le_b, OrderedField.le_refl b⟩
    · rw [if_neg h1]
      by_cases h2 : i.1 = q
      · rw [if_pos h2]; exact ⟨ha_le_r, hr_le_b⟩
      · rw [if_neg h2]; exact ⟨OrderedField.le_refl a, ha_le_b⟩
  have hmono : IsNonincreasing (boxSpec n a b c q) := by
    intro i j hij
    unfold boxSpec
    by_cases hj1 : j.1 < q
    · have hi1 : i.1 < q := by omega
      rw [if_pos hj1, if_pos hi1]; exact OrderedField.le_refl b
    · rw [if_neg hj1]
      by_cases hj2 : j.1 = q
      · rw [if_pos hj2]
        by_cases hi1 : i.1 < q
        · rw [if_pos hi1]; exact hr_le_b
        · have hi2 : i.1 = q := by omega
          rw [if_neg hi1, if_pos hi2]; exact OrderedField.le_refl _
      · rw [if_neg hj2]
        by_cases hi1 : i.1 < q
        · rw [if_pos hi1]; exact ha_le_b
        · rw [if_neg hi1]
          by_cases hi2 : i.1 = q
          · rw [if_pos hi2]; exact ha_le_r
          · rw [if_neg hi2]; exact OrderedField.le_refl a
  refine ⟨hbox_in, ?_⟩
  intro lam hlam
  refine ⟨hmono, ?_, ?_⟩
  · rw [hlam.2, htr_box]
  · intro k hk ι hinj
    rw [boxSpec_prefix_sum hqn a b c k hk]
    by_cases hkq : k ≤ q
    · rw [if_pos hkq, ← finSum_const k b]
      exact finSum_le_finSum (fun r => (hlam.1 (ι r)).2)
    · rw [if_neg hkq]
      have htot := finSum_subset_plus_complement ι hinj lam
      rw [show finSum lam = c from hlam.2] at htot
      have hcomp_ge :
          ofNatF (n - k) * a ≤
            finSum (fun i : Fin n => if memImage ι i then 0 else lam i) := by
        have hones := subset_complement_ones hk ι hinj (F := F)
        have ha_sum :
            ofNatF (n - k) * a =
              finSum (fun i : Fin n => if memImage ι i then (0 : F) else a) := by
          rw [← hones, ← finSum_scale_right]
          apply finSum_congr
          intro i
          cases memImage ι i <;> simp [zero_mul_f, OrderedField.one_mul]
        rw [ha_sum]
        apply finSum_le_finSum
        intro i
        cases memImage ι i
        · simp; exact (hlam.1 i).1
        · simp; exact OrderedField.le_refl 0
      have h_add_le : finSum (fun r : Fin k => lam (ι r)) + ofNatF (n - k) * a ≤ c := by
        rw [← htot]
        exact OrderedField.add_le_add_left _ _ hcomp_ge _
      exact le_sub_of_add_le_f h_add_le

/-- Refutation R2 — Interior Box Classification Theorem (Theorem 4.2(3)):
    whenever `(n-1)a + b < c < a + (n-1)b`, the unique sorted majorization-greatest profile
    `boxSpec` fails even weak concentration, and EVERY symmetric matrix `A` realizing any
    permutation of `boxSpec` satisfies `¬ IsRankAtMostOne (A - α I_n)` for EVERY scalar `α`. -/
theorem refutation_R2_box_interior {n q : Nat} (hqn : q < n) (a b c : F) (hab : a < b)
    (hc_lo : ofNatF (n - 1) * a + b < c)
    (hc_hi : c < a + ofNatF (n - 1) * b)
    (hq_lo : ofNatF q * (b - a) ≤ c - ofNatF n * a)
    (hq_hi : c - ofNatF n * a < ofNatF (q + 1) * (b - a)) :
    ¬ IsWeaklyConcentrated (boxSpec n a b c q) ∧
    (∀ (A : Mat n F) (mu : Spec n F),
      IsPermSpec mu (boxSpec n a b c q) →
      RealizesSpectrum A mu →
      ∀ α : F, ¬ IsRankAtMostOne (matSub A (scalarMat n α))) := by
  have hn1 : 0 < n := by omega
  have hba_pos : 0 < b - a := sub_pos_iff_f.mpr hab
  -- Deduce `b - a < c - n a` and `c - n a < (n - 1)(b - a)`
  have hn_a : ofNatF n * a = ofNatF (n - 1) * a + a := by
    have hnat : n = (n - 1) + 1 := by omega
    conv => lhs; rw [hnat]
    change (ofNatF (n - 1) + 1) * a = ofNatF (n - 1) * a + a
    rw [right_distrib_f, OrderedField.one_mul]
  have h_excess_gt : 1 * (b - a) < c - ofNatF n * a := by
    rw [OrderedField.one_mul]
    have h1 := add_lt_add_right_f hc_lo (- (ofNatF n * a))
    rw [← OrderedField.sub_eq_add_neg c _, hn_a, neg_add_f,
        OrderedField.add_comm (ofNatF (n - 1) * a) b,
        OrderedField.add_assoc b (ofNatF (n - 1) * a) _,
        ← OrderedField.add_assoc (ofNatF (n - 1) * a) _ (-a),
        add_neg_cancel_f, OrderedField.zero_add, ← OrderedField.sub_eq_add_neg, ← hn_a] at h1
    exact h1
  have h_excess_lt : c - ofNatF n * a < ofNatF (n - 1) * (b - a) := by
    have hrhs : a + ofNatF (n - 1) * b - ofNatF n * a = ofNatF (n - 1) * (b - a) := by
      rw [hn_a, OrderedField.sub_eq_add_neg (a + ofNatF (n - 1) * b),
          neg_add_f, OrderedField.add_comm (- (ofNatF (n - 1) * a)) (-a),
          OrderedField.add_comm a (ofNatF (n - 1) * b),
          OrderedField.add_assoc (ofNatF (n - 1) * b) a _,
          ← OrderedField.add_assoc a (-a) _, add_neg_cancel_f, OrderedField.zero_add,
          ← OrderedField.sub_eq_add_neg, mul_sub_f]
    have h1 := add_lt_add_right_f hc_hi (- (ofNatF n * a))
    rw [← OrderedField.sub_eq_add_neg, ← OrderedField.sub_eq_add_neg, hrhs] at h1
    exact h1
  -- Hence `1 ≤ q` and `q + 2 ≤ n`
  have hq_ge1 : 1 ≤ q := by
    by_cases hq0 : q = 0
    · subst hq0
      change c - ofNatF n * a < (0 + 1) * (b - a) at hq_hi
      rw [OrderedField.zero_add] at hq_hi
      exact False.elim (lt_irrefl_f _ (lt_trans_f h_excess_gt hq_hi))
    · omega
  have hq_le_n2 : q + 2 ≤ n := by
    by_cases hbad : n - 1 ≤ q
    · have hmon : (ofNatF (n - 1) : F) ≤ ofNatF q := by
        by_cases heq : n - 1 = q
        · rw [heq]; exact OrderedField.le_refl _
        · exact le_of_lt_f (ofNatF_strictMono (F := F) (by omega))
      have hm := mul_le_mul_of_nonneg_right_f hmon (le_of_lt_f hba_pos)
      have hlt := lt_of_le_of_lt_f (OrderedField.le_trans _ _ _ hm hq_lo) h_excess_lt
      exact False.elim (lt_irrefl_f _ hlt)
    · omega
  -- Key two-witness lemma: for EVERY `α : F`, there exist `j ≠ k` with `boxSpec j ≠ α` and `boxSpec k ≠ α`
  let r_val : F := c - ofNatF q * b - ofNatF (n - 1 - q) * a
  have hr_eq : r_val = a + ((c - ofNatF n * a) - ofNatF q * (b - a)) :=
    boxSpec_mid_eq hqn a b c
  have ha_le_r : a ≤ r_val := by
    rw [hr_eq]
    have h1 := OrderedField.add_le_add_left 0 _ (sub_nonneg_iff_f.mpr hq_lo) a
    rwa [add_zero_f] at h1
  have hr_lt_b : r_val < b := by
    rw [hr_eq]
    have hq1 : ofNatF (q + 1) * (b - a) = (b - a) + ofNatF q * (b - a) := by
      change (ofNatF q + 1) * (b - a) = (b - a) + ofNatF q * (b - a)
      rw [right_distrib_f, OrderedField.one_mul, OrderedField.add_comm]
    rw [hq1] at hq_hi
    have h1 := add_lt_add_right_f hq_hi (- (ofNatF q * (b - a)))
    rw [OrderedField.add_assoc, add_neg_cancel_f, add_zero_f, ← OrderedField.sub_eq_add_neg] at h1
    have h2 := add_lt_add_left_f h1 a
    rwa [OrderedField.add_comm a (b - a), sub_add_cancel_f] at h2
  have htwo_non_alpha : ∀ α : F,
      ∃ j k : Fin n, j ≠ k ∧ boxSpec n a b c q j ≠ α ∧ boxSpec n a b c q k ≠ α := by
    intro α
    let idx0 : Fin n := ⟨0, by omega⟩
    let idxq : Fin n := ⟨q, hqn⟩
    let idxLast : Fin n := ⟨n - 1, by omega⟩
    have hv0 : boxSpec n a b c q idx0 = b := by
      unfold boxSpec idx0
      have h0ltq : (0 : Nat) < q := hq_ge1
      simp [h0ltq]
    have hvq : boxSpec n a b c q idxq = r_val := by
      unfold boxSpec idxq
      have hnl : ¬ (q < q) := Nat.lt_irrefl q
      simp [hnl, r_val]
    have hvLast : boxSpec n a b c q idxLast = a := by
      unfold boxSpec idxLast
      have hnl : ¬ (n - 1 < q) := by omega
      have hne : n - 1 ≠ q := by omega
      simp [hnl, hne]
    by_cases hra : r_val = a
    · -- Case 2: `r_val = a`, which forces `2 ≤ q`
      have hq_ge2 : 2 ≤ q := by
        by_cases hq1 : q = 1
        · subst hq1
          have h0 : (c - ofNatF n * a) - ofNatF 1 * (b - a) = 0 := by
            apply add_left_cancel_f (a := a)
            rw [← hr_eq, hra, add_zero_f]
          have heq1 : c - ofNatF n * a = 1 * (b - a) := by
            have h' := sub_eq_zero_iff_f.mp h0
            change c - ofNatF n * a = (0 + 1) * (b - a) at h'
            rw [OrderedField.zero_add] at h'
            exact h'
          rw [heq1] at h_excess_gt
          exact False.elim (lt_irrefl_f _ h_excess_gt)
        · omega
      let idx1 : Fin n := ⟨1, by omega⟩
      have hv1 : boxSpec n a b c q idx1 = b := by
        unfold boxSpec idx1
        have h1ltq : (1 : Nat) < q := hq_ge2
        simp [h1ltq]
      by_cases hαb : α = b
      · refine ⟨idxq, idxLast, ?_, ?_, ?_⟩
        · intro he; have hv := congrArg Fin.val he; dsimp [idxq, idxLast] at hv; omega
        · rw [hvq, hra, hαb]; exact ne_of_lt_f hab
        · rw [hvLast, hαb]; exact ne_of_lt_f hab
      · refine ⟨idx0, idx1, ?_, ?_, ?_⟩
        · intro he; have hv := congrArg Fin.val he; dsimp [idx0, idx1] at hv; omega
        · rw [hv0]; exact Ne.symm hαb
        · rw [hv1]; exact Ne.symm hαb
    · -- Case 1: `a < r_val < b` at `idx0`, `idxq`, `idxLast`
      have ha_lt_r : a < r_val := lt_of_le_of_ne_f ha_le_r (Ne.symm hra)
      by_cases hαb : α = b
      · refine ⟨idxq, idxLast, ?_, ?_, ?_⟩
        · intro he; have hv := congrArg Fin.val he; dsimp [idxq, idxLast] at hv; omega
        · rw [hvq, hαb]; exact ne_of_lt_f hr_lt_b
        · rw [hvLast, hαb]; exact ne_of_lt_f hab
      · by_cases hαr : α = r_val
        · refine ⟨idx0, idxLast, ?_, ?_, ?_⟩
          · intro he; have hv := congrArg Fin.val he; dsimp [idx0, idxLast] at hv; omega
          · rw [hv0, hαr]; exact Ne.symm (ne_of_lt_f hr_lt_b)
          · rw [hvLast, hαr]; exact ne_of_lt_f ha_lt_r
        · refine ⟨idx0, idxq, ?_, ?_, ?_⟩
          · intro he; have hv := congrArg Fin.val he; dsimp [idx0, idxq] at hv; omega
          · rw [hv0]; exact Ne.symm hαb
          · rw [hvq]; exact Ne.symm hαr
  refine ⟨?_, ?_⟩
  · intro ⟨α, k, hrest⟩
    obtain ⟨j1, j2, hj12, h1, h2⟩ := htwo_non_alpha α
    by_cases hj1k : j1 = k
    · have hj2k : j2 ≠ k := fun h => hj12 (hj1k.trans h.symm)
      exact h2 (hrest j2 hj2k)
    · exact h1 (hrest j1 hj1k)
  · intro A mu hperm hSpec α hRank
    -- Symmetrize `IsPermSpec mu boxSpec` to `IsPermSpec boxSpec mu`
    obtain ⟨σ, g, hgσ, hσg, hmu⟩ := hperm
    have hperm_sym : IsPermSpec (boxSpec n a b c q) mu := by
      refine ⟨g, σ, hσg, hgσ, ?_⟩
      intro i
      have h1 := hmu (g i)
      rw [hσg i] at h1
      exact h1.symm
    have hSpec_box := realizesSpectrum_perm hSpec hperm_sym
    obtain ⟨j1, j2, hj12, h1, h2⟩ := htwo_non_alpha α
    exact hj12 (scalar_plus_rankAtMostOne_at_most_one_non_alpha hSpec_box α hRank j1 j2 h1 h2)

/-- Explicit Canonical Box Counterexamples at `n = 3` (`B_{3,3}(0,2) -> (2,1,0)`) and
    `n = 4` (`B_{4,2}(0,1) -> (1,1,0,0)` with strict Frobenius bound `∑ λ_i² ≤ 2`) (Corollary 4.3). -/
theorem refutation_R2_n3_and_n4 :
    let two : F := 1 + 1
    let three : F := (1 + 1) + 1
    let spec3 := boxSpec 3 0 two three 1
    let spec4 := boxSpec 4 0 1 two 2
    (BoxTracePolytope 3 0 two three spec3 ∧
     ¬ IsWeaklyConcentrated spec3 ∧
     ∀ A : Mat 3 F, RealizesSpectrum A spec3 →
       ∀ α : F, ¬ IsRankAtMostOne (matSub A (scalarMat 3 α))) ∧
    (BoxTracePolytope 4 0 1 two spec4 ∧
     ¬ IsWeaklyConcentrated spec4 ∧
     (∀ lam : Spec 4 F, BoxTracePolytope 4 0 1 two lam → specSumSq lam ≤ two) ∧
     ∀ A : Mat 4 F, RealizesSpectrum A spec4 →
       ∀ α : F, ¬ IsRankAtMostOne (matSub A (scalarMat 4 α))) := by
  intro two three spec3 spec4
  have htwo_pos : (0 : F) < two := two_pos_f
  have h1_lt_2 : (1 : F) < two := by
    unfold two
    have h := add_lt_add_left_f (zero_lt_one_f (F := F)) 1
    rwa [add_zero_f] at h
  have h2_lt_3 : two < three := by
    unfold three
    have h := add_lt_add_left_f (zero_lt_one_f (F := F)) two
    rwa [add_zero_f] at h
  have h3_lt_4 : three < two + two := by
    unfold three two
    exact add_lt_add_left_f h1_lt_2 (1 + 1)
  have hid_perm : ∀ m : Nat, ∀ s : Spec m F, IsPermSpec s s :=
    fun _ _ => ⟨fun i => i, fun i => i, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  -- Part 1: `n = 3`
  have hq3_lo : ofNatF 1 * (two - 0) ≤ three - ofNatF 3 * 0 := by
    change (0 + 1) * (two - 0) ≤ three - ofNatF 3 * 0
    rw [OrderedField.zero_add, OrderedField.one_mul, sub_zero_f, mul_zero_f, sub_zero_f]
    exact le_of_lt_f h2_lt_3
  have hq3_hi : three - ofNatF 3 * 0 < ofNatF 2 * (two - 0) := by
    change three - ofNatF 3 * 0 < ((0 + 1) + 1) * (two - 0)
    rw [mul_zero_f, sub_zero_f, sub_zero_f, OrderedField.zero_add,
        right_distrib_f, OrderedField.one_mul]
    exact h3_lt_4
  have hc3_lo : ofNatF (3 - 1) * 0 + two < three := by
    rw [mul_zero_f, OrderedField.zero_add]; exact h2_lt_3
  have hc3_hi : three < 0 + ofNatF (3 - 1) * two := by
    change three < 0 + ((0 + 1) + 1) * two
    rw [OrderedField.zero_add, OrderedField.zero_add, right_distrib_f, OrderedField.one_mul]
    exact h3_lt_4
  have ⟨hb3, _⟩ := boxSpec_majorizes_boxTracePolytope (by omega : 1 < 3) 0 two three hq3_lo hq3_hi
  have ⟨hnwc3, hrk3⟩ := refutation_R2_box_interior (by omega : 1 < 3) 0 two three
    htwo_pos hc3_lo hc3_hi hq3_lo hq3_hi
  -- Part 2: `n = 4`
  have h2_lt_3' : two < ((0 + 1) + 1) + 1 := by
    rw [OrderedField.zero_add]; exact h2_lt_3
  have hq4_lo : ofNatF 2 * (1 - 0) ≤ two - ofNatF 4 * 0 := by
    change ((0 + 1) + 1) * (1 - 0) ≤ two - ofNatF 4 * 0
    rw [OrderedField.zero_add, sub_zero_f, mul_one_f, mul_zero_f, sub_zero_f]
    exact OrderedField.le_refl two
  have hq4_hi : two - ofNatF 4 * 0 < ofNatF 3 * (1 - 0) := by
    change two - ofNatF 4 * 0 < (((0 + 1) + 1) + 1) * (1 - 0)
    rw [mul_zero_f, sub_zero_f, sub_zero_f, mul_one_f]
    exact h2_lt_3'
  have hc4_lo : ofNatF (4 - 1) * 0 + 1 < two := by
    rw [mul_zero_f, OrderedField.zero_add]; exact h1_lt_2
  have hc4_hi : two < 0 + ofNatF (4 - 1) * 1 := by
    change two < 0 + (((0 + 1) + 1) + 1) * 1
    rw [OrderedField.zero_add, mul_one_f]
    exact h2_lt_3'
  have ⟨hb4, _⟩ := boxSpec_majorizes_boxTracePolytope (by omega : 2 < 4) 0 1 two hq4_lo hq4_hi
  have ⟨hnwc4, hrk4⟩ := refutation_R2_box_interior (by omega : 2 < 4) 0 1 two
    zero_lt_one_f hc4_lo hc4_hi hq4_lo hq4_hi
  have hf2_4 : ∀ lam : Spec 4 F, BoxTracePolytope 4 0 1 two lam → specSumSq lam ≤ two := by
    intro lam hlam
    have hpt : ∀ i : Fin 4, lam i * lam i ≤ lam i := by
      intro i
      have ⟨h0, h1⟩ := hlam.1 i
      have hm := mul_le_mul_of_nonneg_left_f h1 h0
      rwa [mul_one_f] at hm
    have hs : specSumSq lam ≤ specTrace lam := finSum_le_finSum hpt
    rwa [hlam.2] at hs
  exact ⟨⟨hb3, hnwc3, fun A hA => hrk3 A spec3 (hid_perm 3 spec3) hA⟩,
         ⟨hb4, hnwc4, hf2_4, fun A hA => hrk4 A spec4 (hid_perm 4 spec4) hA⟩⟩

/-! ### Refutation R3: Fixed-Trace Rank-One Perturbation Rigidity -/

/-- Exact Frobenius–Trace Identity for Symmetric Rank-`≤ 1` Matrices (Theorem 5.1(1)):
    `IsSymmetric R` and `IsRankAtMostOne R` imply `‖R‖_F² = (tr R)²`. -/
theorem symmetric_rankAtMostOne_frobSq_eq_trace_sq {n : Nat} {R : Mat n F}
    (hsym : IsSymmetric R) (hrank : IsRankAtMostOne R) :
    frobSq R = matTrace R * matTrace R := by
  obtain ⟨u, v, huv⟩ := hrank
  unfold frobSq matTrace
  rw [finSum_mul_finSum]
  apply finSum_congr
  intro i
  apply finSum_congr
  intro j
  calc
    R i j * R i j = R i j * R j i := by rw [hsym i j]
    _ = (u i * v j) * (u j * v i) := by rw [huv i j, huv j i]
    _ = (u i * v i) * (u j * v j) := by
          calc
            (u i * v j) * (u j * v i) = u i * (v j * (u j * v i)) :=
              OrderedField.mul_assoc _ _ _
            _ = u i * ((v j * u j) * v i) := by
              rw [← OrderedField.mul_assoc (v j) (u j) (v i)]
            _ = u i * (v i * (u j * v j)) := by
              rw [OrderedField.mul_comm (v j) (u j),
                  OrderedField.mul_comm (u j * v j) (v i)]
            _ = (u i * v i) * (u j * v j) :=
              (OrderedField.mul_assoc _ _ _).symm
    _ = R i i * R j j := by rw [← huv i i, ← huv j j]

theorem traceless_symmetric_rankAtMostOne_eq_zero {n : Nat} {R : Mat n F}
    (hsym : IsSymmetric R) (hrank : IsRankAtMostOne R) (htr : matTrace R = 0) :
    ∀ i j : Fin n, R i j = 0 := by
  have hf0 : frobSq R = 0 := by
    rw [symmetric_rankAtMostOne_frobSq_eq_trace_sq hsym hrank, htr, mul_zero_f]
  unfold frobSq at hf0
  have hout := (finSum_eq_zero_iff_of_nonneg (fun i =>
    finSum_nonneg (fun j => sq_nonneg_f (R i j)))).mp hf0
  intro i j
  have hin := (finSum_eq_zero_iff_of_nonneg (fun r => sq_nonneg_f (R i r))).mp (hout i) j
  exact eq_zero_of_sq_eq_zero_f hin

/-- No Nonzero Trace-Preserving Symmetric Rank-One Perturbation Exists (Theorem 5.1(3)). -/
theorem no_trace_preserving_symmetric_rankOne_perturbation {n : Nat}
    {A0 A : Mat n F} (hsym0 : IsSymmetric A0) (hsym : IsSymmetric A)
    (htr : matTrace A = matTrace A0)
    (hrank : IsRankAtMostOne (matSub A A0)) :
    A = A0 := by
  let R : Mat n F := matSub A A0
  have hR_sym : IsSymmetric R := by
    intro i j
    unfold R matSub
    rw [hsym i j, hsym0 i j]
  have hR_tr : matTrace R = 0 := by
    unfold matTrace R matSub
    rw [finSum_sub]
    change matTrace A - matTrace A0 = 0
    rw [htr, sub_self_f]
  have hR0 := traceless_symmetric_rankAtMostOne_eq_zero hR_sym hrank hR_tr
  funext i j
  exact sub_eq_zero_iff_f.mp (hR0 i j)

/-- Non-symmetric traceless rank-`≤ 1` matrices are nilpotent of index `≤ 2` (`R² = 0`, Remark 5.2). -/
theorem traceless_rankAtMostOne_nilpotent {n : Nat} {R : Mat n F}
    (hrank : IsRankAtMostOne R) (htr : matTrace R = 0) :
    matMul R R = scalarMat n 0 := by
  obtain ⟨u, v, huv⟩ := hrank
  have hvu0 : finSum (fun k : Fin n => v k * u k) = 0 := by
    have hc : finSum (fun k : Fin n => v k * u k) = matTrace R := by
      unfold matTrace
      apply finSum_congr
      intro k
      rw [huv k k, OrderedField.mul_comm]
    rw [hc, htr]
  funext i j
  unfold matMul scalarMat
  simp only [ite_self]
  have hc :
      finSum (fun k : Fin n => R i k * R k j) =
      finSum (fun k : Fin n => (u i * v j) * (v k * u k)) := by
    apply finSum_congr
    intro k
    rw [huv i k, huv k j]
    calc
      (u i * v k) * (u k * v j) = u i * (v k * (u k * v j)) := OrderedField.mul_assoc _ _ _
      _ = u i * ((v k * u k) * v j) := by rw [← OrderedField.mul_assoc (v k) (u k) (v j)]
      _ = u i * (v j * (v k * u k)) := by rw [OrderedField.mul_comm (v k * u k) (v j)]
      _ = (u i * v j) * (v k * u k) := (OrderedField.mul_assoc _ _ _).symm
  rw [hc, finSum_scale, hvu0, mul_zero_f]

/-- Sharpness of rank `2` for fixed-trace symmetric perturbations:
    for `n ≥ 2` and `δ ≠ 0`, `T = δ (e_0 e_0ᵀ - e_1 e_1ᵀ)` is symmetric, traceless, nonzero,
    and not rank-at-most-one. -/
theorem robinMuirhead_rankTwo_witness {n : Nat} (hn2 : 2 ≤ n) (δ : F) (hδ : δ ≠ 0) :
    ∃ T : Mat n F,
      IsSymmetric T ∧ matTrace T = 0 ∧ (∃ i j : Fin n, T i j ≠ 0) ∧ ¬ IsRankAtMostOne T := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, hn2⟩
  let e0 : Fin n → F := fun i => if i = i0 then 1 else 0
  let e1 : Fin n → F := fun i => if i = i1 then 1 else 0
  let T : Mat n F := matSub (symRankOne δ e0) (symRankOne δ e1)
  have hsym : IsSymmetric T := by
    intro i j
    unfold T matSub symRankOne
    rw [OrderedField.mul_comm (e0 i) (e0 j), OrderedField.mul_comm (e1 i) (e1 j)]
  have htr : matTrace T = 0 := by
    unfold matTrace T matSub symRankOne
    rw [finSum_sub]
    have hs0 : finSum (fun i : Fin n => δ * (e0 i * e0 i)) = δ := by
      have hc : finSum (fun i : Fin n => δ * (e0 i * e0 i)) =
                finSum (fun i : Fin n => if i = i0 then δ else 0) := by
        apply finSum_congr
        intro i
        unfold e0
        by_cases hi : i = i0
        · simp [hi, OrderedField.one_mul, mul_one_f]
        · simp [hi, zero_mul_f, mul_zero_f]
      rw [hc, finSum_single]
    have hs1 : finSum (fun i : Fin n => δ * (e1 i * e1 i)) = δ := by
      have hc : finSum (fun i : Fin n => δ * (e1 i * e1 i)) =
                finSum (fun i : Fin n => if i = i1 then δ else 0) := by
        apply finSum_congr
        intro i
        unfold e1
        by_cases hi : i = i1
        · simp [hi, OrderedField.one_mul, mul_one_f]
        · simp [hi, zero_mul_f, mul_zero_f]
      rw [hc, finSum_single]
    rw [hs0, hs1, sub_self_f]
  have hnz : T i0 i0 ≠ 0 := by
    unfold T matSub symRankOne e0 e1
    have h01 : i0 ≠ i1 := fun h => by have hv : (0 : Nat) = 1 := congrArg Fin.val h; omega
    simp only [ite_true, if_neg h01, OrderedField.one_mul, mul_one_f,
               zero_mul_f, mul_zero_f, sub_zero_f]
    exact hδ
  refine ⟨T, hsym, htr, ⟨i0, i0, hnz⟩, ?_⟩
  intro hrk
  exact hnz (traceless_symmetric_rankAtMostOne_eq_zero hsym hrk htr i0 i0)

end Refutations

/-! ## Section 6: Master Synthesis Theorem and Axiom Audit -/

/-- Formalizations of the three unqualified claims asserted by Conjecture 00000007171:
    1. `Claim_AllObjectivesConcentrated`: every canonical fixed-trace PSD spectral objective
       attains a floor-concentrated maximum (refuted by `det` and `e_2` in R1).
    2. `Claim_BoxExtremaConcentratedRankOne`: every box-constrained fixed-trace majorization-maximal
       spectrum is weakly concentrated / scalar + rank-`≤ 1` realizable (refuted at `n = 3, 4` in R2).
    3. `Claim_TracePreservingRankOneRealization`: distinct fixed-trace symmetric matrices can be
       linked by a rank-`≤ 1` perturbation `A = A0 + R` (refuted universally in R3). -/
def Claim_AllObjectivesConcentrated (F : Type u) [OrderedField F] : Prop :=
  ∀ (n : Nat) (_ : 2 ≤ n) (c : F) (_ : 0 < c) (Obj : Spec n F → F),
    (∃ lam_max : Spec n F, PSDTraceSimplex n c lam_max ∧
      ∀ lam : Spec n F, PSDTraceSimplex n c lam → Obj lam ≤ Obj lam_max) →
    ∃ lam_max : Spec n F, PSDTraceSimplex n c lam_max ∧ IsConcentratedFloor 0 lam_max ∧
      ∀ lam : Spec n F, PSDTraceSimplex n c lam → Obj lam ≤ Obj lam_max

def Claim_BoxExtremaConcentratedRankOne (F : Type u) [OrderedField F] : Prop :=
  ∀ (n : Nat) (a b c : F) (lam_star : Spec n F),
    a < b → BoxTracePolytope n a b c lam_star →
    (∀ lam : Spec n F, BoxTracePolytope n a b c lam → KyFanMajorizes lam_star lam) →
    IsWeaklyConcentrated lam_star ∧
    ∃ (A : Mat n F) (α : F), RealizesSpectrum A lam_star ∧
      IsRankAtMostOne (matSub A (scalarMat n α))

def Claim_TracePreservingRankOneRealization (F : Type u) [OrderedField F] : Prop :=
  ∀ (n : Nat) (_ : 2 ≤ n) (c : F) (_ : 0 < c),
    ∃ (A0 A : Mat n F),
      IsSymmetric A0 ∧ IsSymmetric A ∧
      matTrace A0 = c ∧ matTrace A = c ∧ A ≠ A0 ∧
      IsRankAtMostOne (matSub A A0)

theorem conjecture_00000007171_poly (F : Type u) [OrderedField F] :
    ¬ Claim_AllObjectivesConcentrated F ∧
    ¬ Claim_BoxExtremaConcentratedRankOne F ∧
    ¬ Claim_TracePreservingRankOneRealization F := by
  refine ⟨?_, ?_, ?_⟩
  · -- Negate Claim 1 using `Obj := finProd` at `n = 2, c = 1`
    intro hC1
    have ⟨hu_in, _, hdm, _, hconc_zero⟩ :=
      refutation_R1_det_and_elemSymm2 (F := F) (n := 2) (by omega) 1 zero_lt_one_f
    have hdet_max_all :
        ∃ lam_max : Spec 2 F, PSDTraceSimplex 2 1 lam_max ∧
          ∀ lam : Spec 2 F, PSDTraceSimplex 2 1 lam → finProd lam ≤ finProd lam_max :=
      ⟨unifSpec 2 (by omega) 1, hu_in, fun lam hl => (hdm lam hl).1⟩
    obtain ⟨lam_c, _, hconc, hmax⟩ := hC1 2 (by omega) 1 zero_lt_one_f finProd hdet_max_all
    have hlt := (hconc_zero lam_c hconc).2.2.1
    have hge := hmax (unifSpec 2 (by omega) 1) hu_in
    exact lt_irrefl_f _ (lt_of_lt_of_le_f hlt hge)
  · -- Negate Claim 2 using `n = 3, B_{3,3}(0, 2) -> boxSpec 3 0 2 3 1 = (2, 1, 0)`
    intro hC2
    let two : F := 1 + 1
    let three : F := (1 + 1) + 1
    have h1_lt_2 : (1 : F) < two := by
      have h := add_lt_add_left_f (zero_lt_one_f (F := F)) 1; rwa [add_zero_f] at h
    have h2_lt_3 : two < three := by
      have h := add_lt_add_left_f (zero_lt_one_f (F := F)) two; rwa [add_zero_f] at h
    have h3_lt_4 : three < two + two := add_lt_add_left_f h1_lt_2 (1 + 1)
    have hq3_lo : ofNatF 1 * (two - 0) ≤ three - ofNatF 3 * 0 := by
      change (0 + 1) * (two - 0) ≤ three - ofNatF 3 * 0
      rw [OrderedField.zero_add, OrderedField.one_mul, sub_zero_f, mul_zero_f, sub_zero_f]
      exact le_of_lt_f h2_lt_3
    have hq3_hi : three - ofNatF 3 * 0 < ofNatF 2 * (two - 0) := by
      change three - ofNatF 3 * 0 < ((0 + 1) + 1) * (two - 0)
      rw [mul_zero_f, sub_zero_f, sub_zero_f, OrderedField.zero_add,
          right_distrib_f, OrderedField.one_mul]
      exact h3_lt_4
    have ⟨hb3, hmaj3⟩ :=
      boxSpec_majorizes_boxTracePolytope (by omega : 1 < 3) 0 two three hq3_lo hq3_hi
    have ⟨⟨_, hnwc3, _⟩, _⟩ := refutation_R2_n3_and_n4 (F := F)
    have ⟨hwc, _⟩ := hC2 3 0 two three (boxSpec 3 0 two three 1) two_pos_f hb3 hmaj3
    exact hnwc3 hwc
  · -- Negate Claim 3 using R3 (`no_trace_preserving_symmetric_rankOne_perturbation`)
    intro hC3
    obtain ⟨A0, A, hsym0, hsym, htr0, htr, hne, hrk⟩ :=
      hC3 2 (by omega) 1 zero_lt_one_f
    exact hne (no_trace_preserving_symmetric_rankOne_perturbation hsym0 hsym
      (htr.trans htr0.symm) hrk)

/-- Master Polymorphic Disproof of Conjecture 00000007171 over EVERY `OrderedField F`,
    together with Constructive Ground Instantiation on `RatField`. -/
theorem conjecture_00000007171_disproved :
    (∀ (F : Type u) [OrderedField F],
      ¬ Claim_AllObjectivesConcentrated F ∧
      ¬ Claim_BoxExtremaConcentratedRankOne F ∧
      ¬ Claim_TracePreservingRankOneRealization F) ∧
    (¬ Claim_AllObjectivesConcentrated RatField ∧
     ¬ Claim_BoxExtremaConcentratedRankOne RatField ∧
     ¬ Claim_TracePreservingRankOneRealization RatField) ∧
    -- Concrete ground non-vacuity witness of the positive Householder regime on `RatField`
    (∃ A : Mat 2 RatField,
      IsRankOne (matSub A (scalarMat 2 (0 : RatField))) ∧
      matTrace A = (1 : RatField) ∧
      RealizesSpectrum A (concSpec 2 (by omega) 0 1)) := by
  refine ⟨fun F _ => conjecture_00000007171_poly F, conjecture_00000007171_poly RatField, ?_⟩
  -- Witness `u = (1, 0)` on `RatField` for `n = 2, a = 0, c = 1`
  let u2 : Fin 2 → RatField := fun i => if i.1 = 0 then 1 else 0
  have hu2 : vecNormSq u2 = 1 := by
    change (0 + u2 ⟨0, by omega⟩ * u2 ⟨0, by omega⟩) + u2 ⟨1, by omega⟩ * u2 ⟨1, by omega⟩ = 1
    unfold u2
    simp [OrderedField.zero_add, OrderedField.one_mul, zero_mul_f, add_zero_f]
  have hc2 : ofNatF 2 * (0 : RatField) < 1 := by
    rw [mul_zero_f]; exact zero_lt_one_f
  exact ⟨matAdd (scalarMat 2 0) (symRankOne (1 - ofNatF 2 * 0) u2),
         rankOnePerturb_realizes_concSpec (by omega : 0 < 2) 0 1 hc2 u2 hu2⟩

end Conjecture00000007171

/-! ## Axiom Footprint Audit -/

#print axioms Conjecture00000007171.instOrderedFieldRat
#print axioms Conjecture00000007171.orderedField_nonvacuous
#print axioms Conjecture00000007171.bernoulli_ge
#print axioms Conjecture00000007171.bernoulli_strict
#print axioms Conjecture00000007171.am_gm_complete
#print axioms Conjecture00000007171.concSpec_majorizes_lowerTraceSimplex
#print axioms Conjecture00000007171.convex_sum_le_concSpec
#print axioms Conjecture00000007171.specSumSq_eq_concSpec_iff
#print axioms Conjecture00000007171.rankOnePerturb_realizes_concSpec
#print axioms Conjecture00000007171.refutation_R1_det_and_elemSymm2
#print axioms Conjecture00000007171.scalar_plus_rankAtMostOne_at_most_one_non_alpha
#print axioms Conjecture00000007171.boxSpec_majorizes_boxTracePolytope
#print axioms Conjecture00000007171.refutation_R2_box_interior
#print axioms Conjecture00000007171.refutation_R2_n3_and_n4
#print axioms Conjecture00000007171.symmetric_rankAtMostOne_frobSq_eq_trace_sq
#print axioms Conjecture00000007171.no_trace_preserving_symmetric_rankOne_perturbation
#print axioms Conjecture00000007171.traceless_rankAtMostOne_nilpotent
#print axioms Conjecture00000007171.robinMuirhead_rankTwo_witness
#print axioms Conjecture00000007171.conjecture_00000007171_disproved
