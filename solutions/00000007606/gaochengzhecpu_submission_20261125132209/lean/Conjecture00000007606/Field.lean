/-
  Conjecture 00000007606 — Algebraic & Field Foundations (Core Lean 4.19.0)

  Self-contained commutative field hierarchy (`FieldK`, `FieldCharNeTwo`,
  `OrderedFieldK`, `EuclideanFieldK`) with zero external dependencies, together
  with concrete unconditional instances:
    1. `F2`     — the field with two elements (characteristic 2, `+1 = -1`),
    2. `RatQ`   — exact rational numbers `ℚ` (characteristic 0 ordered field),
    3. `QSqrt2` — the quadratic field `ℚ(√2)` (characteristic ≠ 2).
-/

namespace Conjecture00000007606

/-- Self-contained commutative field structure in Core Lean 4. -/
class FieldK (K : Type) where
  zero : K
  one : K
  add : K → K → K
  neg : K → K
  mul : K → K → K
  inv : K → K
  add_assoc : ∀ a b c : K, add (add a b) c = add a (add b c)
  add_comm : ∀ a b : K, add a b = add b a
  zero_add : ∀ a : K, add zero a = a
  add_left_neg : ∀ a : K, add (neg a) a = zero
  mul_assoc : ∀ a b c : K, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b : K, mul a b = mul b a
  one_mul : ∀ a : K, mul one a = a
  mul_left_inv : ∀ a : K, a ≠ zero → mul (inv a) a = one
  left_distrib : ∀ a b c : K, mul a (add b c) = add (mul a b) (mul a c)
  zero_ne_one : zero ≠ one

/-- Field of characteristic different from 2 (`1 + 1 ≠ 0`). -/
class FieldCharNeTwo (K : Type) extends FieldK K where
  two_ne_zero : add one one ≠ zero

/-- Ordered field structure extending `FieldCharNeTwo`. -/
class OrderedFieldK (K : Type) extends FieldCharNeTwo K where
  le : K → K → Prop
  le_refl : ∀ a : K, le a a
  le_trans : ∀ a b c : K, le a b → le b c → le a c
  le_antisymm : ∀ a b : K, le a b → le b a → a = b
  le_total : ∀ a b : K, le a b ∨ le b a
  add_le_add_left : ∀ a b c : K, le a b → le (add c a) (add c b)
  mul_nonneg : ∀ a b : K, le zero a → le zero b → le zero (mul a b)
  zero_le_one : le zero one

/-- Euclidean ordered field (such as `ℝ` or real algebraic numbers `ℝ_alg`):
    an ordered field in which every non-negative element has a square root. -/
class EuclideanFieldK (E : Type) extends OrderedFieldK E where
  sqrt_exists : ∀ a : E, le zero a → ∃ s : E, le zero s ∧ mul s s = a

namespace FieldK

section RingLemmas
variable {K : Type} [F : FieldK K]

def sub (a b : K) : K := F.add a (F.neg b)
def two : K := F.add F.one F.one

theorem add_zero (a : K) : F.add a F.zero = a := by
  rw [F.add_comm, F.zero_add]

theorem add_right_neg (a : K) : F.add a (F.neg a) = F.zero := by
  rw [F.add_comm, F.add_left_neg]

theorem add_left_cancel {a b c : K} (h : F.add a b = F.add a c) : b = c := by
  have h1 : F.add (F.neg a) (F.add a b) = F.add (F.neg a) (F.add a c) :=
    congrArg (F.add (F.neg a)) h
  rw [← F.add_assoc, ← F.add_assoc, F.add_left_neg, F.zero_add, F.zero_add] at h1
  exact h1

theorem add_right_cancel {a b c : K} (h : F.add a c = F.add b c) : a = b := by
  apply add_left_cancel (a := c)
  rw [F.add_comm c a, F.add_comm c b]
  exact h

theorem neg_zero : F.neg (F.zero : K) = F.zero := by
  apply add_left_cancel (a := (F.zero : K))
  rw [add_right_neg, F.zero_add]

theorem neg_neg (a : K) : F.neg (F.neg a) = a := by
  apply add_left_cancel (a := F.neg a)
  rw [add_right_neg, F.add_left_neg]

theorem neg_eq_of_add_eq_zero {a b : K} (h : F.add a b = F.zero) : F.neg a = b := by
  apply add_left_cancel (a := a)
  rw [add_right_neg, h]

theorem neg_add (a b : K) : F.neg (F.add a b) = F.add (F.neg a) (F.neg b) := by
  apply neg_eq_of_add_eq_zero
  calc
    F.add (F.add a b) (F.add (F.neg a) (F.neg b))
      = F.add a (F.add b (F.add (F.neg b) (F.neg a))) := by
          rw [F.add_assoc, F.add_comm (F.neg a) (F.neg b)]
    _ = F.add a (F.add (F.add b (F.neg b)) (F.neg a)) := by
          rw [← F.add_assoc b (F.neg b) (F.neg a)]
    _ = F.add a (F.add F.zero (F.neg a)) := by rw [add_right_neg]
    _ = F.zero := by rw [F.zero_add, add_right_neg]

theorem mul_one (a : K) : F.mul a F.one = a := by
  rw [F.mul_comm, F.one_mul]

theorem right_distrib (a b c : K) : F.mul (F.add a b) c = F.add (F.mul a c) (F.mul b c) := by
  rw [F.mul_comm, F.left_distrib, F.mul_comm c a, F.mul_comm c b]

theorem mul_zero (a : K) : F.mul a F.zero = F.zero := by
  apply add_left_cancel (a := F.mul a F.zero)
  rw [← F.left_distrib, add_zero, add_zero]

theorem zero_mul (a : K) : F.mul F.zero a = F.zero := by
  rw [F.mul_comm, mul_zero]

theorem mul_neg (a b : K) : F.mul a (F.neg b) = F.neg (F.mul a b) := by
  symm
  apply neg_eq_of_add_eq_zero
  rw [← F.left_distrib, add_right_neg, mul_zero]

theorem neg_mul (a b : K) : F.mul (F.neg a) b = F.neg (F.mul a b) := by
  rw [F.mul_comm, mul_neg, F.mul_comm]

theorem neg_mul_neg (a b : K) : F.mul (F.neg a) (F.neg b) = F.mul a b := by
  rw [neg_mul, mul_neg, neg_neg]

theorem neg_one_mul (a : K) : F.mul (F.neg F.one) a = F.neg a := by
  rw [neg_mul, F.one_mul]

theorem sub_self (a : K) : sub a a = F.zero :=
  add_right_neg a

theorem sub_eq_zero {a b : K} : sub a b = F.zero ↔ a = b := by
  constructor
  · intro h
    have h1 : F.add (sub a b) b = F.add F.zero b := congrArg (fun x => F.add x b) h
    unfold sub at h1
    rw [F.add_assoc, F.add_left_neg, add_zero, F.zero_add] at h1
    exact h1
  · intro h
    rw [h]
    exact sub_self b

theorem mul_sub (a b c : K) : F.mul a (sub b c) = sub (F.mul a b) (F.mul a c) := by
  unfold sub
  rw [F.left_distrib, mul_neg]

theorem sub_mul (a b c : K) : F.mul (sub a b) c = sub (F.mul a c) (F.mul b c) := by
  unfold sub
  rw [right_distrib, neg_mul]

theorem mul_right_inv {a : K} (ha : a ≠ F.zero) : F.mul a (F.inv a) = F.one := by
  rw [F.mul_comm, F.mul_left_inv a ha]

theorem mul_eq_zero {a b : K} (h : F.mul a b = F.zero) : a = F.zero ∨ b = F.zero := by
  by_cases ha : a = F.zero
  · exact Or.inl ha
  · right
    have h1 : F.mul (F.inv a) (F.mul a b) = F.mul (F.inv a) F.zero :=
      congrArg (F.mul (F.inv a)) h
    rw [← F.mul_assoc, F.mul_left_inv a ha, F.one_mul, mul_zero] at h1
    exact h1

theorem mul_ne_zero {a b : K} (ha : a ≠ F.zero) (hb : b ≠ F.zero) : F.mul a b ≠ F.zero := by
  intro h
  cases mul_eq_zero h with
  | inl h0 => exact ha h0
  | inr h0 => exact hb h0

theorem inv_ne_zero {a : K} (ha : a ≠ F.zero) : F.inv a ≠ F.zero := by
  intro h0
  have h1 := F.mul_left_inv a ha
  rw [h0, zero_mul] at h1
  exact F.zero_ne_one h1

theorem mul_left_cancel {a b c : K} (ha : a ≠ F.zero) (h : F.mul a b = F.mul a c) : b = c := by
  have h1 : F.mul a (sub b c) = F.zero := by
    rw [mul_sub, sub_eq_zero.mpr h]
  cases mul_eq_zero h1 with
  | inl h0 => exact absurd h0 ha
  | inr h0 => exact sub_eq_zero.mp h0

theorem sq_eq_one_iff {a : K} : F.mul a a = F.one ↔ a = F.one ∨ a = F.neg F.one := by
  constructor
  · intro h
    have hdiff : F.mul (sub a F.one) (F.add a F.one) = F.zero := by
      calc
        F.mul (sub a F.one) (F.add a F.one)
          = sub (F.mul a (F.add a F.one)) (F.mul F.one (F.add a F.one)) := sub_mul _ _ _
        _ = sub (F.add (F.mul a a) a) (F.add a F.one) := by
              rw [F.left_distrib, mul_one, F.one_mul]
        _ = sub (F.add F.one a) (F.add a F.one) := by rw [h]
        _ = F.zero := by rw [F.add_comm F.one a]; exact sub_self _
    cases mul_eq_zero hdiff with
    | inl h1 => exact Or.inl (sub_eq_zero.mp h1)
    | inr h2 =>
        right
        have h3 := neg_eq_of_add_eq_zero (F.add_comm a F.one ▸ h2)
        exact h3.symm
  · intro h
    cases h with
    | inl h1 => rw [h1, F.one_mul]
    | inr h2 => rw [h2, neg_mul_neg, F.one_mul]

end RingLemmas

section CharNeTwoLemmas
variable {K : Type} [F : FieldCharNeTwo K]

theorem one_ne_neg_one : (F.one : K) ≠ F.neg F.one := by
  intro h
  have h1 : F.add F.one F.one = F.add (F.neg F.one) F.one :=
    congrArg (fun x => F.add x F.one) h
  rw [F.add_left_neg] at h1
  exact F.two_ne_zero h1

theorem eq_zero_of_eq_neg {a : K} (h : a = F.neg a) : a = F.zero := by
  have h1 : F.mul two a = F.zero := by
    unfold two
    rw [right_distrib, F.one_mul]
    calc
      F.add a a = F.add a (F.neg a) := congrArg (F.add a) h
      _ = F.zero := add_right_neg a
  cases mul_eq_zero h1 with
  | inl h2 => exact absurd h2 F.two_ne_zero
  | inr h2 => exact h2

theorem ne_neg_of_ne_zero {a : K} (ha : a ≠ F.zero) : a ≠ F.neg a :=
  fun h => ha (eq_zero_of_eq_neg h)

end CharNeTwoLemmas

section OrderedLemmas
variable {K : Type} [O : OrderedFieldK K]

theorem lt_irrefl_zero_one : ¬ O.le O.one O.zero := by
  intro h
  exact O.zero_ne_one (O.le_antisymm O.zero O.one O.zero_le_one h)

theorem neg_nonneg_of_le_zero {a : K} (h : O.le a O.zero) : O.le O.zero (O.neg a) := by
  have h1 := O.add_le_add_left a O.zero (O.neg a) h
  rw [O.add_left_neg, add_zero] at h1
  exact h1

theorem sq_nonneg (a : K) : O.le O.zero (O.mul a a) := by
  cases O.le_total O.zero a with
  | inl h => exact O.mul_nonneg a a h h
  | inr h =>
      have hn := neg_nonneg_of_le_zero h
      have hsq := O.mul_nonneg (O.neg a) (O.neg a) hn hn
      rw [neg_mul_neg] at hsq
      exact hsq

theorem two_pos : O.le O.zero (two : K) ∧ (two : K) ≠ O.zero := by
  refine ⟨?_, O.two_ne_zero⟩
  have h := O.add_le_add_left O.zero O.one O.one O.zero_le_one
  rw [add_zero] at h
  exact O.le_trans O.zero O.one two O.zero_le_one h

theorem inv_two_nonneg : O.le O.zero (O.inv (two : K)) := by
  cases O.le_total O.zero (O.inv (two : K)) with
  | inl h => exact h
  | inr h =>
      have h2nz : (two : K) ≠ O.zero := O.two_ne_zero
      have hn := neg_nonneg_of_le_zero h
      have hp := O.mul_nonneg two (O.neg (O.inv two)) two_pos.1 hn
      rw [mul_neg, mul_right_inv h2nz] at hp
      have h2 := O.add_le_add_left O.zero (O.neg O.one) O.one hp
      rw [add_zero, add_right_neg] at h2
      exact absurd h2 lt_irrefl_zero_one

/-- If `c^2 + s^2 = 1`, then `0 ≤ 1 + c`. -/
theorem one_add_nonneg_of_unit_circle {c s : K}
    (hcs : O.add (O.mul c c) (O.mul s s) = O.one) :
    O.le O.zero (O.add O.one c) := by
  cases O.le_total O.zero (O.add O.one c) with
  | inl h => exact h
  | inr h =>
      let u := O.neg (O.add O.one c)
      have hu : O.le O.zero u := neg_nonneg_of_le_zero h
      have h_id : O.add (O.mul u (O.add u two)) O.one = O.mul c c := by
        have hu_def : u = O.add (O.neg O.one) (O.neg c) := neg_add O.one c
        have hu2 : O.add u two = sub O.one c := by
          rw [hu_def]
          unfold two sub
          calc
            O.add (O.add (O.neg O.one) (O.neg c)) (O.add O.one O.one)
              = O.add (O.neg c) (O.add (O.neg O.one) (O.add O.one O.one)) := by
                  rw [O.add_comm (O.neg O.one) (O.neg c), O.add_assoc]
            _ = O.add (O.neg c) O.one := by
                  rw [← O.add_assoc (O.neg O.one) O.one O.one, O.add_left_neg, O.zero_add]
            _ = O.add O.one (O.neg c) := O.add_comm _ _
        rw [hu2]
        have hprod : O.mul u (sub O.one c) = sub (O.mul c c) O.one := by
          calc
            O.mul u (sub O.one c)
              = O.neg (O.mul (O.add O.one c) (sub O.one c)) := neg_mul _ _
            _ = O.neg (sub (O.mul (O.add O.one c) O.one) (O.mul (O.add O.one c) c)) := by
                  rw [mul_sub]
            _ = O.neg (sub (O.add O.one c) (O.add c (O.mul c c))) := by
                  rw [mul_one, right_distrib, O.one_mul]
            _ = sub (O.mul c c) O.one := by
                  unfold sub
                  rw [neg_add, neg_add, neg_neg]
                  calc
                    O.add (O.add (O.neg O.one) (O.neg c)) (O.add c (O.mul c c))
                      = O.add (O.neg O.one) (O.add (O.add (O.neg c) c) (O.mul c c)) := by
                          rw [O.add_assoc, ← O.add_assoc (O.neg c) c (O.mul c c)]
                    _ = O.add (O.neg O.one) (O.mul c c) := by
                          rw [O.add_left_neg, O.zero_add]
                    _ = O.add (O.mul c c) (O.neg O.one) := O.add_comm _ _
        rw [hprod]
        unfold sub
        rw [O.add_assoc, O.add_left_neg, add_zero]
      have hsum0 : O.add (O.mul u (O.add u two)) (O.mul s s) = O.zero := by
        apply add_right_cancel (c := O.one)
        rw [O.zero_add]
        calc
          O.add (O.add (O.mul u (O.add u two)) (O.mul s s)) O.one
            = O.add (O.add (O.mul u (O.add u two)) O.one) (O.mul s s) := by
                rw [O.add_assoc, O.add_comm (O.mul s s) O.one, ← O.add_assoc]
          _ = O.add (O.mul c c) (O.mul s s) := by rw [h_id]
          _ = O.one := hcs
      have hu2_nonneg : O.le O.zero (O.add u two) := by
        have h1 := O.add_le_add_left O.zero u two hu
        rw [add_zero, O.add_comm two u] at h1
        exact O.le_trans O.zero two (O.add u two) two_pos.1 h1
      have hterm1 : O.le O.zero (O.mul u (O.add u two)) := O.mul_nonneg _ _ hu hu2_nonneg
      have hterm2 : O.le O.zero (O.mul s s) := sq_nonneg s
      have hle0 : O.le (O.mul u (O.add u two)) O.zero := by
        have h1 := O.add_le_add_left O.zero (O.mul s s) (O.mul u (O.add u two)) hterm2
        rw [add_zero, hsum0] at h1
        exact h1
      have hterm1_eq0 : O.mul u (O.add u two) = O.zero :=
        O.le_antisymm _ _ hle0 hterm1
      cases mul_eq_zero hterm1_eq0 with
      | inl hu0 =>
          have h1 : O.add O.one c = O.zero := by
            have hnn := neg_neg (O.add O.one c)
            have hnu : O.neg u = O.zero := by rw [hu0, neg_zero]
            exact hnn.symm.trans hnu
          rw [h1]
          exact O.le_refl O.zero
      | inr hu2_eq0 =>
          have h2le : O.le two (O.add u two) := by
            have h1 := O.add_le_add_left O.zero u two hu
            rw [add_zero, O.add_comm two u] at h1
            exact h1
          rw [hu2_eq0] at h2le
          exact absurd (O.le_antisymm two O.zero h2le two_pos.1) O.two_ne_zero

end OrderedLemmas

end FieldK

/-! ### Concrete Instance 1: `F2` (Characteristic 2 Field `{0, 1}`) -/

inductive F2 : Type where
  | zero : F2
  | one : F2
  deriving DecidableEq

namespace F2

def add : F2 → F2 → F2
  | .zero, b => b
  | a, .zero => a
  | .one, .one => .zero

def mul : F2 → F2 → F2
  | .one, .one => .one
  | _, _ => .zero

instance : FieldK F2 where
  zero := .zero
  one := .one
  add := add
  neg := id
  mul := mul
  inv := id
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  zero_add := by intro a; cases a <;> rfl
  add_left_neg := by intro a; cases a <;> rfl
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  mul_comm := by intro a b; cases a <;> cases b <;> rfl
  one_mul := by intro a; cases a <;> rfl
  mul_left_inv := by
    intro a ha
    cases a with
    | zero => exact absurd rfl ha
    | one => rfl
  left_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  zero_ne_one := by decide

theorem char_two : FieldK.add F2.one F2.one = F2.zero := rfl

end F2

/-! ### Concrete Instance 2: `RatQ` (Exact Rational Numbers `ℚ`) -/

structure RawRat where
  num : Int
  den : Int
  den_pos : 0 < den

namespace RawRat

def Rel (p q : RawRat) : Prop := p.num * q.den = q.num * p.den

theorem rel_refl (p : RawRat) : Rel p p := rfl

theorem rel_symm {p q : RawRat} (h : Rel p q) : Rel q p := h.symm

theorem rel_trans {p q r : RawRat} (hpq : Rel p q) (hqr : Rel q r) : Rel p r := by
  unfold Rel at *
  have hq_nz : q.den ≠ 0 := by have := q.den_pos; omega
  have h1 : p.num * q.den * r.den = r.num * p.den * q.den := by
    calc
      p.num * q.den * r.den = q.num * p.den * r.den := by rw [hpq]
      _ = q.num * r.den * p.den := by
          rw [Int.mul_assoc, Int.mul_comm p.den r.den, ← Int.mul_assoc]
      _ = r.num * q.den * p.den := by rw [hqr]
      _ = r.num * p.den * q.den := by
          rw [Int.mul_assoc, Int.mul_comm q.den p.den, ← Int.mul_assoc]
  have hdiff : (p.num * r.den - r.num * p.den) * q.den = 0 := by
    have h2 : p.num * r.den * q.den = p.num * q.den * r.den := by
      rw [Int.mul_assoc, Int.mul_comm r.den q.den, ← Int.mul_assoc]
    rw [Int.sub_mul, h2, h1, Int.sub_self]
  cases Int.mul_eq_zero.mp hdiff with
  | inl h0 => exact Int.sub_eq_zero.mp h0
  | inr h0 => exact absurd h0 hq_nz

def add (p q : RawRat) : RawRat where
  num := p.num * q.den + q.num * p.den
  den := p.den * q.den
  den_pos := Int.mul_pos p.den_pos q.den_pos

def neg (p : RawRat) : RawRat where
  num := -p.num
  den := p.den
  den_pos := p.den_pos

def mul (p q : RawRat) : RawRat where
  num := p.num * q.num
  den := p.den * q.den
  den_pos := Int.mul_pos p.den_pos q.den_pos

def inv (p : RawRat) : RawRat :=
  if hpos : 0 < p.num then
    { num := p.den, den := p.num, den_pos := hpos }
  else if hneg : p.num < 0 then
    { num := -p.den, den := -p.num, den_pos := by omega }
  else
    { num := 0, den := 1, den_pos := by decide }

end RawRat

/-- Exact rational numbers `ℚ` constructed as `Quot RawRat.Rel`. -/
def RatQ : Type := Quot RawRat.Rel

namespace RatQ

def mkRat (n : Int) (d : Int) (hd : 0 < d := by decide) : RatQ :=
  Quot.mk RawRat.Rel ⟨n, d, hd⟩

def ofInt (n : Int) : RatQ := mkRat n 1

private def lift2 {α : Type} (f : RawRat → RawRat → α)
    (hf : ∀ a1 a2 b1 b2, RawRat.Rel a1 a2 → RawRat.Rel b1 b2 → f a1 b1 = f a2 b2) :
    RatQ → RatQ → α :=
  Quot.lift
    (fun a => Quot.lift (f a) (fun b1 b2 hb => hf a a b1 b2 (RawRat.rel_refl a) hb))
    (fun a1 a2 ha => funext (Quot.ind (fun b => hf a1 a2 b b ha (RawRat.rel_refl b))))

def eqBool : RatQ → RatQ → Bool :=
  lift2 (fun p q => decide (p.num * q.den = q.num * p.den)) (by
    intro a1 a2 b1 b2 ha hb
    have hiff : a1.num * b1.den = b1.num * a1.den ↔ a2.num * b2.den = b2.num * a2.den := by
      constructor
      · intro h
        exact RawRat.rel_trans (RawRat.rel_symm ha) (RawRat.rel_trans h hb)
      · intro h
        exact RawRat.rel_trans ha (RawRat.rel_trans h (RawRat.rel_symm hb))
    by_cases h1 : a1.num * b1.den = b1.num * a1.den
    · have h2 := hiff.mp h1
      simp [h1, h2]
    · have h2 : ¬ (a2.num * b2.den = b2.num * a2.den) := fun hc => h1 (hiff.mpr hc)
      simp [h1, h2])

theorem exact_rel {p q : RawRat} (h : Quot.mk RawRat.Rel p = Quot.mk RawRat.Rel q) :
    RawRat.Rel p q := by
  have hb : eqBool (Quot.mk RawRat.Rel p) (Quot.mk RawRat.Rel q) =
            eqBool (Quot.mk RawRat.Rel p) (Quot.mk RawRat.Rel p) := by rw [h]
  change decide (p.num * q.den = q.num * p.den) = decide (p.num * p.den = p.num * p.den) at hb
  simp at hb
  exact hb

private theorem add_well_def (a1 a2 b1 b2 : RawRat)
    (ha : RawRat.Rel a1 a2) (hb : RawRat.Rel b1 b2) :
    RawRat.Rel (RawRat.add a1 b1) (RawRat.add a2 b2) := by
  unfold RawRat.Rel RawRat.add at *
  dsimp only
  have t1 : a1.num * b1.den * (a2.den * b2.den) = a2.num * b2.den * (a1.den * b1.den) := by
    calc
      a1.num * b1.den * (a2.den * b2.den)
        = a1.num * a2.den * (b1.den * b2.den) := by
            rw [← Int.mul_assoc, Int.mul_assoc a1.num b1.den a2.den,
                Int.mul_comm b1.den a2.den, ← Int.mul_assoc a1.num a2.den b1.den, Int.mul_assoc]
      _ = a2.num * a1.den * (b1.den * b2.den) := by rw [ha]
      _ = a2.num * b2.den * (a1.den * b1.den) := by
            rw [Int.mul_comm b1.den b2.den, ← Int.mul_assoc,
                Int.mul_assoc a2.num a1.den b2.den, Int.mul_comm a1.den b2.den,
                ← Int.mul_assoc a2.num b2.den a1.den, Int.mul_assoc]
  have t2 : b1.num * a1.den * (a2.den * b2.den) = b2.num * a2.den * (a1.den * b1.den) := by
    calc
      b1.num * a1.den * (a2.den * b2.den)
        = b1.num * b2.den * (a1.den * a2.den) := by
            rw [Int.mul_comm a2.den b2.den, ← Int.mul_assoc,
                Int.mul_assoc b1.num a1.den b2.den, Int.mul_comm a1.den b2.den,
                ← Int.mul_assoc b1.num b2.den a1.den, Int.mul_assoc]
      _ = b2.num * b1.den * (a1.den * a2.den) := by rw [hb]
      _ = b2.num * a2.den * (a1.den * b1.den) := by
            rw [Int.mul_comm a1.den a2.den, ← Int.mul_assoc,
                Int.mul_assoc b2.num b1.den a2.den, Int.mul_comm b1.den a2.den,
                ← Int.mul_assoc b2.num a2.den b1.den, Int.mul_assoc, Int.mul_comm b1.den a1.den]
  rw [Int.add_mul, Int.add_mul, t1, t2]

def add : RatQ → RatQ → RatQ :=
  lift2 (fun p q => Quot.mk RawRat.Rel (RawRat.add p q))
    (fun a1 a2 b1 b2 ha hb => Quot.sound (add_well_def a1 a2 b1 b2 ha hb))

def neg : RatQ → RatQ :=
  Quot.lift (fun p => Quot.mk RawRat.Rel (RawRat.neg p)) (by
    intro p q h
    apply Quot.sound
    unfold RawRat.Rel RawRat.neg at *
    dsimp only
    rw [Int.neg_mul, Int.neg_mul, h])

def mul : RatQ → RatQ → RatQ :=
  lift2 (fun p q => Quot.mk RawRat.Rel (RawRat.mul p q)) (by
    intro a1 a2 b1 b2 ha hb
    apply Quot.sound
    unfold RawRat.Rel RawRat.mul at *
    dsimp only
    calc
      a1.num * b1.num * (a2.den * b2.den)
        = a1.num * a2.den * (b1.num * b2.den) := by
            rw [← Int.mul_assoc, Int.mul_assoc a1.num b1.num a2.den,
                Int.mul_comm b1.num a2.den, ← Int.mul_assoc a1.num a2.den b1.num, Int.mul_assoc]
      _ = a2.num * a1.den * (b2.num * b1.den) := by rw [ha, hb]
      _ = a2.num * b2.num * (a1.den * b1.den) := by
            rw [← Int.mul_assoc, Int.mul_assoc a2.num a1.den b2.num,
                Int.mul_comm a1.den b2.num, ← Int.mul_assoc a2.num b2.num a1.den, Int.mul_assoc])

def inv : RatQ → RatQ :=
  Quot.lift (fun p => Quot.mk RawRat.Rel (RawRat.inv p)) (by
    intro p q h
    apply Quot.sound
    unfold RawRat.Rel RawRat.inv at *
    have hp_d := p.den_pos
    have hq_d := q.den_pos
    by_cases hp1 : 0 < p.num
    · have hq1 : 0 < q.num := by
        have hmul : 0 < p.num * q.den := Int.mul_pos hp1 hq_d
        rw [h] at hmul
        by_cases hqn : 0 < q.num
        · exact hqn
        · have hle : q.num * p.den ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
          omega
      simp [hp1, hq1]
      rw [Int.mul_comm p.den q.num, ← h, Int.mul_comm]
    · by_cases hp2 : p.num < 0
      · have hq1 : ¬ (0 < q.num) := by
          intro hqp
          have hmul : 0 < q.num * p.den := Int.mul_pos hqp hp_d
          rw [← h] at hmul
          have hle : p.num * q.den ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
          omega
        have hq2 : q.num < 0 := by
          by_cases hqn : q.num < 0
          · exact hqn
          · have hqz : q.num = 0 := by omega
            rw [hqz, Int.zero_mul] at h
            cases Int.mul_eq_zero.mp h with
            | inl h0 => omega
            | inr h0 => omega
        simp [hp1, hp2, hq1, hq2]
        rw [Int.neg_mul_neg, Int.neg_mul_neg, Int.mul_comm p.den q.num, ← h, Int.mul_comm]
      · have hpz : p.num = 0 := by omega
        have hqz : q.num = 0 := by
          rw [hpz, Int.zero_mul] at h
          cases Int.mul_eq_zero.mp h.symm with
          | inl h0 => exact h0
          | inr h0 => omega
        have hq1 : ¬ (0 < q.num) := by omega
        have hq2 : ¬ (q.num < 0) := by omega
        simp [hp1, hp2, hq1, hq2])

def leProp : RatQ → RatQ → Prop :=
  lift2 (fun p q => p.num * q.den ≤ q.num * p.den) (by
    intro a1 a2 b1 b2 ha hb
    apply propext
    unfold RawRat.Rel at ha hb
    have ha1 := a1.den_pos; have ha2 := a2.den_pos
    have hb1 := b1.den_pos; have hb2 := b2.den_pos
    constructor
    · intro h
      have hpos : 0 < a1.den * b1.den := Int.mul_pos ha1 hb1
      have h1 : a1.num * b1.den * (a2.den * b2.den) ≤ b1.num * a1.den * (a2.den * b2.den) :=
        Int.mul_le_mul_of_nonneg_right h (by have := Int.mul_pos ha2 hb2; omega)
      have eqL : a1.num * b1.den * (a2.den * b2.den) = a2.num * b2.den * (a1.den * b1.den) := by
        calc
          a1.num * b1.den * (a2.den * b2.den)
            = a1.num * a2.den * (b1.den * b2.den) := by
                rw [← Int.mul_assoc, Int.mul_assoc a1.num b1.den a2.den,
                    Int.mul_comm b1.den a2.den, ← Int.mul_assoc a1.num a2.den b1.den, Int.mul_assoc]
          _ = a2.num * a1.den * (b1.den * b2.den) := by rw [ha]
          _ = a2.num * b2.den * (a1.den * b1.den) := by
                rw [Int.mul_comm b1.den b2.den, ← Int.mul_assoc,
                    Int.mul_assoc a2.num a1.den b2.den, Int.mul_comm a1.den b2.den,
                    ← Int.mul_assoc a2.num b2.den a1.den, Int.mul_assoc]
      have eqR : b1.num * a1.den * (a2.den * b2.den) = b2.num * a2.den * (a1.den * b1.den) := by
        calc
          b1.num * a1.den * (a2.den * b2.den)
            = b1.num * b2.den * (a1.den * a2.den) := by
                rw [Int.mul_comm a2.den b2.den, ← Int.mul_assoc,
                    Int.mul_assoc b1.num a1.den b2.den, Int.mul_comm a1.den b2.den,
                    ← Int.mul_assoc b1.num b2.den a1.den, Int.mul_assoc]
          _ = b2.num * b1.den * (a1.den * a2.den) := by rw [hb]
          _ = b2.num * a2.den * (a1.den * b1.den) := by
                rw [Int.mul_comm a1.den a2.den, ← Int.mul_assoc,
                    Int.mul_assoc b2.num b1.den a2.den, Int.mul_comm b1.den a2.den,
                    ← Int.mul_assoc b2.num a2.den b1.den, Int.mul_assoc, Int.mul_comm b1.den a1.den]
      rw [eqL, eqR] at h1
      by_cases hle : a2.num * b2.den ≤ b2.num * a2.den
      · exact hle
      · have hgt : b2.num * a2.den + 1 ≤ a2.num * b2.den := by omega
        have hm := Int.mul_le_mul_of_nonneg_right hgt (by omega : 0 ≤ a1.den * b1.den)
        rw [Int.add_mul, Int.one_mul] at hm
        omega
    · intro h
      have hpos : 0 < a2.den * b2.den := Int.mul_pos ha2 hb2
      have h1 : a2.num * b2.den * (a1.den * b1.den) ≤ b2.num * a2.den * (a1.den * b1.den) :=
        Int.mul_le_mul_of_nonneg_right h (by have := Int.mul_pos ha1 hb1; omega)
      have eqL : a2.num * b2.den * (a1.den * b1.den) = a1.num * b1.den * (a2.den * b2.den) := by
        calc
          a2.num * b2.den * (a1.den * b1.den)
            = a2.num * a1.den * (b2.den * b1.den) := by
                rw [← Int.mul_assoc, Int.mul_assoc a2.num b2.den a1.den,
                    Int.mul_comm b2.den a1.den, ← Int.mul_assoc a2.num a1.den b2.den, Int.mul_assoc]
          _ = a1.num * a2.den * (b2.den * b1.den) := by rw [← ha]
          _ = a1.num * b1.den * (a2.den * b2.den) := by
                rw [Int.mul_comm b2.den b1.den, ← Int.mul_assoc,
                    Int.mul_assoc a1.num a2.den b1.den, Int.mul_comm a2.den b1.den,
                    ← Int.mul_assoc a1.num b1.den a2.den, Int.mul_assoc]
      have eqR : b2.num * a2.den * (a1.den * b1.den) = b1.num * a1.den * (a2.den * b2.den) := by
        calc
          b2.num * a2.den * (a1.den * b1.den)
            = b2.num * b1.den * (a2.den * a1.den) := by
                rw [Int.mul_comm a1.den b1.den, ← Int.mul_assoc,
                    Int.mul_assoc b2.num a2.den b1.den, Int.mul_comm a2.den b1.den,
                    ← Int.mul_assoc b2.num b1.den a2.den, Int.mul_assoc]
          _ = b1.num * b2.den * (a2.den * a1.den) := by rw [← hb]
          _ = b1.num * a1.den * (a2.den * b2.den) := by
                rw [Int.mul_comm a2.den a1.den, ← Int.mul_assoc,
                    Int.mul_assoc b1.num b2.den a1.den, Int.mul_comm b2.den a1.den,
                    ← Int.mul_assoc b1.num a1.den b2.den, Int.mul_assoc, Int.mul_comm b2.den a2.den]
      rw [eqL, eqR] at h1
      by_cases hle : a1.num * b1.den ≤ b1.num * a1.den
      · exact hle
      · have hgt : b1.num * a1.den + 1 ≤ a1.num * b1.den := by omega
        have hm := Int.mul_le_mul_of_nonneg_right hgt (by omega : 0 ≤ a2.den * b2.den)
        rw [Int.add_mul, Int.one_mul] at hm
        omega)

instance : OrderedFieldK RatQ where
  zero := ofInt 0
  one := ofInt 1
  add := add
  neg := neg
  mul := mul
  inv := inv
  add_assoc := Quot.ind fun p => Quot.ind fun q => Quot.ind fun r => by
    apply Quot.sound
    unfold RawRat.Rel RawRat.add; dsimp only
    rw [← Int.mul_assoc p.den q.den r.den]
    apply congrArg (· * (p.den * q.den * r.den))
    rw [Int.add_mul, Int.add_mul,
        Int.mul_assoc p.num q.den r.den,
        Int.mul_assoc q.num p.den r.den, Int.mul_comm p.den r.den,
        ← Int.mul_assoc q.num r.den p.den,
        Int.mul_comm p.den q.den, ← Int.mul_assoc r.num q.den p.den,
        Int.add_assoc]
  add_comm := Quot.ind fun p => Quot.ind fun q => by
    apply Quot.sound
    unfold RawRat.Rel RawRat.add; dsimp only
    rw [Int.add_comm (p.num * q.den) (q.num * p.den), Int.mul_comm p.den q.den]
  zero_add := Quot.ind fun p => by
    apply Quot.sound
    unfold RawRat.Rel RawRat.add; dsimp only
    rw [Int.zero_mul, Int.zero_add, Int.mul_one, Int.one_mul]
  add_left_neg := Quot.ind fun p => by
    apply Quot.sound
    unfold RawRat.Rel RawRat.add RawRat.neg; dsimp only
    rw [Int.neg_mul, Int.add_left_neg, Int.zero_mul, Int.zero_mul]
  mul_assoc := Quot.ind fun p => Quot.ind fun q => Quot.ind fun r => by
    apply Quot.sound
    unfold RawRat.Rel RawRat.mul; dsimp only
    rw [Int.mul_assoc p.num q.num r.num, Int.mul_assoc p.den q.den r.den]
  mul_comm := Quot.ind fun p => Quot.ind fun q => by
    apply Quot.sound
    unfold RawRat.Rel RawRat.mul; dsimp only
    rw [Int.mul_comm p.num q.num, Int.mul_comm p.den q.den]
  one_mul := Quot.ind fun p => by
    apply Quot.sound
    unfold RawRat.Rel RawRat.mul; dsimp only
    rw [Int.one_mul, Int.one_mul]
  mul_left_inv := Quot.ind fun p ha => by
    have hp_nz : p.num ≠ 0 := by
      intro h0
      apply ha
      apply Quot.sound
      unfold RawRat.Rel; dsimp only
      rw [h0, Int.mul_one, Int.zero_mul]
    apply Quot.sound
    unfold RawRat.Rel RawRat.mul RawRat.inv
    by_cases hp1 : 0 < p.num
    · simp [hp1]
      rw [Int.mul_comm p.den p.num]
    · have hp2 : p.num < 0 := by omega
      simp [hp1, hp2]
      rw [Int.neg_mul, Int.neg_mul, Int.mul_comm p.den p.num]
  left_distrib := Quot.ind fun p => Quot.ind fun q => Quot.ind fun r => by
    apply Quot.sound
    unfold RawRat.Rel RawRat.mul RawRat.add; dsimp only
    rw [Int.mul_add, Int.add_mul, Int.add_mul]
    have e1 : p.num * (q.num * r.den) * (p.den * q.den * (p.den * r.den)) =
              p.num * q.num * (p.den * r.den) * (p.den * (q.den * r.den)) := by
      calc
        p.num * (q.num * r.den) * (p.den * q.den * (p.den * r.den))
          = p.num * q.num * r.den * (p.den * r.den * (p.den * q.den)) := by
              rw [← Int.mul_assoc p.num q.num r.den,
                  Int.mul_comm (p.den * q.den) (p.den * r.den)]
        _ = p.num * q.num * (r.den * (p.den * r.den * (p.den * q.den))) := by
              rw [Int.mul_assoc (p.num * q.num)]
        _ = p.num * q.num * (p.den * r.den * (r.den * (p.den * q.den))) := by
              rw [← Int.mul_assoc r.den (p.den * r.den),
                  Int.mul_comm r.den (p.den * r.den), Int.mul_assoc (p.den * r.den)]
        _ = p.num * q.num * (p.den * r.den) * (p.den * (q.den * r.den)) := by
              rw [← Int.mul_assoc (p.num * q.num) (p.den * r.den),
                  ← Int.mul_assoc r.den p.den q.den, Int.mul_comm r.den p.den,
                  Int.mul_assoc p.den r.den q.den, Int.mul_comm r.den q.den]
    have e2 : p.num * (r.num * q.den) * (p.den * q.den * (p.den * r.den)) =
              p.num * r.num * (p.den * q.den) * (p.den * (q.den * r.den)) := by
      calc
        p.num * (r.num * q.den) * (p.den * q.den * (p.den * r.den))
          = p.num * r.num * (q.den * (p.den * q.den * (p.den * r.den))) := by
              rw [← Int.mul_assoc p.num r.num q.den, Int.mul_assoc (p.num * r.num)]
        _ = p.num * r.num * (p.den * q.den * (q.den * (p.den * r.den))) := by
              rw [← Int.mul_assoc q.den (p.den * q.den),
                  Int.mul_comm q.den (p.den * q.den), Int.mul_assoc (p.den * q.den)]
        _ = p.num * r.num * (p.den * q.den) * (p.den * (q.den * r.den)) := by
              rw [← Int.mul_assoc (p.num * r.num) (p.den * q.den),
                  ← Int.mul_assoc q.den p.den r.den, Int.mul_comm q.den p.den,
                  Int.mul_assoc p.den q.den r.den]
    rw [e1, e2]
  zero_ne_one := fun h => by
    have hr := exact_rel h
    unfold RawRat.Rel at hr; dsimp only at hr; omega
  two_ne_zero := fun h => by
    have hr := exact_rel h
    unfold RawRat.Rel RawRat.add at hr; dsimp only at hr; omega
  le := leProp
  le_refl := Quot.ind fun p => Int.le_refl (p.num * p.den)
  le_trans := Quot.ind fun p => Quot.ind fun q => Quot.ind fun r hpq hqr => by
    change p.num * q.den ≤ q.num * p.den at hpq
    change q.num * r.den ≤ r.num * q.den at hqr
    change p.num * r.den ≤ r.num * p.den
    have hqd := q.den_pos; have hrd := r.den_pos; have hpd := p.den_pos
    have h1 : p.num * q.den * r.den ≤ q.num * p.den * r.den :=
      Int.mul_le_mul_of_nonneg_right hpq (by omega)
    have h2 : q.num * r.den * p.den ≤ r.num * q.den * p.den :=
      Int.mul_le_mul_of_nonneg_right hqr (by omega)
    have eq1 : q.num * p.den * r.den = q.num * r.den * p.den := by
      rw [Int.mul_assoc, Int.mul_comm p.den r.den, ← Int.mul_assoc]
    rw [eq1] at h1
    have h3 : p.num * q.den * r.den ≤ r.num * q.den * p.den := Int.le_trans h1 h2
    have eqL : p.num * q.den * r.den = p.num * r.den * q.den := by
      rw [Int.mul_assoc, Int.mul_comm q.den r.den, ← Int.mul_assoc]
    have eqR : r.num * q.den * p.den = r.num * p.den * q.den := by
      rw [Int.mul_assoc, Int.mul_comm q.den p.den, ← Int.mul_assoc]
    rw [eqL, eqR] at h3
    by_cases hle : p.num * r.den ≤ r.num * p.den
    · exact hle
    · have hgt : r.num * p.den + 1 ≤ p.num * r.den := by omega
      have hm := Int.mul_le_mul_of_nonneg_right hgt (by omega : 0 ≤ q.den)
      rw [Int.add_mul, Int.one_mul] at hm
      omega
  le_antisymm := Quot.ind fun p => Quot.ind fun q h1 h2 => by
    change p.num * q.den ≤ q.num * p.den at h1
    change q.num * p.den ≤ p.num * q.den at h2
    apply Quot.sound
    unfold RawRat.Rel
    omega
  le_total := Quot.ind fun p => Quot.ind fun q => by
    change p.num * q.den ≤ q.num * p.den ∨ q.num * p.den ≤ p.num * q.den
    omega
  add_le_add_left := Quot.ind fun p => Quot.ind fun q => Quot.ind fun r hpq => by
    change p.num * q.den ≤ q.num * p.den at hpq
    change (r.num * p.den + p.num * r.den) * (r.den * q.den) ≤
           (r.num * q.den + q.num * r.den) * (r.den * p.den)
    have hrd := r.den_pos
    have hrr : 0 ≤ r.den * r.den := by have := Int.mul_pos hrd hrd; omega
    have eL1 : r.num * p.den * (r.den * q.den) = r.num * q.den * (r.den * p.den) := by
      rw [← Int.mul_assoc, Int.mul_assoc r.num p.den r.den, Int.mul_comm p.den r.den,
          ← Int.mul_assoc r.num r.den p.den, Int.mul_assoc (r.num * r.den) p.den q.den,
          Int.mul_comm p.den q.den, ← Int.mul_assoc (r.num * r.den) q.den p.den,
          Int.mul_assoc r.num r.den q.den, Int.mul_comm r.den q.den,
          ← Int.mul_assoc r.num q.den r.den, Int.mul_assoc]
    have eL2 : p.num * r.den * (r.den * q.den) = p.num * q.den * (r.den * r.den) := by
      calc
        p.num * r.den * (r.den * q.den)
          = p.num * (r.den * (q.den * r.den)) := by
              rw [Int.mul_assoc p.num r.den, Int.mul_comm r.den q.den]
        _ = p.num * (q.den * (r.den * r.den)) := by
              rw [← Int.mul_assoc r.den q.den r.den, Int.mul_comm r.den q.den,
                  Int.mul_assoc q.den r.den r.den]
        _ = p.num * q.den * (r.den * r.den) := (Int.mul_assoc _ _ _).symm
    have eR2 : q.num * r.den * (r.den * p.den) = q.num * p.den * (r.den * r.den) := by
      calc
        q.num * r.den * (r.den * p.den)
          = q.num * (r.den * (p.den * r.den)) := by
              rw [Int.mul_assoc q.num r.den, Int.mul_comm r.den p.den]
        _ = q.num * (p.den * (r.den * r.den)) := by
              rw [← Int.mul_assoc r.den p.den r.den, Int.mul_comm r.den p.den,
                  Int.mul_assoc p.den r.den r.den]
        _ = q.num * p.den * (r.den * r.den) := (Int.mul_assoc _ _ _).symm
    rw [Int.add_mul, Int.add_mul, eL1, eL2, eR2]
    have hm := Int.mul_le_mul_of_nonneg_right hpq hrr
    omega
  mul_nonneg := Quot.ind fun p => Quot.ind fun q hp hq => by
    change 0 * p.den ≤ p.num * 1 at hp
    change 0 * q.den ≤ q.num * 1 at hq
    change 0 * (p.den * q.den) ≤ p.num * q.num * 1
    rw [Int.zero_mul, Int.mul_one] at hp hq ⊢
    exact Int.mul_nonneg hp hq
  zero_le_one := by
    change (0 : Int) * 1 ≤ 1 * 1
    decide

theorem ofInt_inj {m n : Int} (h : ofInt m = ofInt n) : m = n := by
  have hr := exact_rel h
  unfold RawRat.Rel at hr
  dsimp only at hr
  omega

/-- Classical infinite-descent proof that `2 * n^2 ≠ d^2` for `d ≠ 0`. -/
private theorem no_nat_two_sq_eq_sq : ∀ d : Nat, d ≠ 0 → ∀ n : Nat, 2 * (n * n) ≠ d * d := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro hd n heq
    have hd_even : d % 2 = 0 := by
      by_cases hmod : d % 2 = 0
      · exact hmod
      · let k := d / 2
        have hd_div : d = 2 * k + 1 := by omega
        have hsq : d * d = 2 * (2 * (k * k) + 2 * k) + 1 := by
          calc
            d * d = (2 * k + 1) * (2 * k + 1) := by rw [hd_div]
            _ = (2 * k + 1) * (2 * k) + (2 * k + 1) * 1 := Nat.mul_add _ _ _
            _ = 2 * k * (2 * k) + 1 * (2 * k) + (2 * k + 1) := by
                  rw [Nat.add_mul, Nat.mul_one]
            _ = 2 * (2 * (k * k) + 2 * k) + 1 := by
                  have hkk : 2 * k * (2 * k) = 2 * (2 * (k * k)) := by
                    calc
                      2 * k * (2 * k) = 2 * (k * (2 * k)) := Nat.mul_assoc 2 k (2 * k)
                      _ = 2 * (2 * k * k) := by rw [Nat.mul_comm k (2 * k)]
                      _ = 2 * (2 * (k * k)) := by rw [Nat.mul_assoc 2 k k]
                  rw [hkk, Nat.one_mul]
                  omega
        omega
    let d' := d / 2
    have hd_eq : d = 2 * d' := by omega
    have hd'_nz : d' ≠ 0 := by omega
    have hn_sq : 2 * (d' * d') = n * n := by
      have hsub : 2 * (n * n) = (2 * d') * (2 * d') := by rw [← hd_eq]; exact heq
      have h4 : (2 * d') * (2 * d') = 2 * (2 * (d' * d')) := by
        calc
          (2 * d') * (2 * d') = 2 * (d' * (2 * d')) := Nat.mul_assoc 2 d' (2 * d')
          _ = 2 * (2 * d' * d') := by rw [Nat.mul_comm d' (2 * d')]
          _ = 2 * (2 * (d' * d')) := by rw [Nat.mul_assoc 2 d' d']
      rw [h4] at hsub
      omega
    have hn_nz : n ≠ 0 := by
      intro h0
      rw [h0] at hn_sq
      have hd'_pos : 0 < d' := by omega
      have hpos : 0 < d' * d' := Nat.mul_pos hd'_pos hd'_pos
      omega
    have hn_lt : n < d := by
      by_cases hlt : n < d
      · exact hlt
      · have hle : d ≤ n := by omega
        have hsq_le : d * d ≤ n * n := Nat.mul_le_mul hle hle
        have hpos : 0 < n * n := Nat.mul_pos (by omega) (by omega)
        omega
    exact ih n hn_lt hn_nz d' hn_sq

/-- No two rational numbers satisfy `a^2 = 2 * b^2` unless `a = 0` and `b = 0`. -/
theorem no_rat_sq_eq_two_sq : ∀ (a b : RatQ),
    FieldK.mul a a = FieldK.mul FieldK.two (FieldK.mul b b) →
    a = FieldK.zero ∧ b = FieldK.zero :=
  Quot.ind fun p => Quot.ind fun q h => by
    have hr := exact_rel h
    unfold RawRat.Rel RawRat.mul RawRat.add at hr
    dsimp only at hr
    have h_int : 2 * ((q.num * p.den) * (q.num * p.den)) = (p.num * q.den) * (p.num * q.den) := by
      have eL : (1 * 1 + 1 * 1 : Int) * (q.num * q.num) * (p.den * p.den) =
                2 * ((q.num * p.den) * (q.num * p.den)) := by
        have h11 : (1 * 1 + 1 * 1 : Int) = 2 := rfl
        rw [h11, Int.mul_assoc 2 (q.num * q.num) (p.den * p.den)]
        congr 1
        rw [← Int.mul_assoc, Int.mul_assoc q.num q.num p.den, Int.mul_comm q.num p.den,
            ← Int.mul_assoc q.num p.den q.num, Int.mul_assoc, Int.mul_comm p.den q.num]
      have eR : p.num * p.num * (1 * 1 * (q.den * q.den)) =
                (p.num * q.den) * (p.num * q.den) := by
        have h1 : (1 * 1 : Int) * (q.den * q.den) = q.den * q.den := Int.one_mul _
        rw [h1, ← Int.mul_assoc, Int.mul_assoc p.num p.num q.den, Int.mul_comm p.num q.den,
            ← Int.mul_assoc p.num q.den p.num, Int.mul_assoc, Int.mul_comm q.den p.num]
      rw [← eL, ← eR]
      exact hr.symm
    let dNat := (p.num * q.den).natAbs
    let nNat := (q.num * p.den).natAbs
    have hsq_abs : ∀ z : Int, z * z = ((z.natAbs * z.natAbs : Nat) : Int) := fun z => by
      rw [Int.ofNat_mul]
      cases Int.natAbs_eq z with
      | inl hz => conv => lhs; rw [hz]
      | inr hz =>
          conv => lhs; rw [hz]
          exact Int.neg_mul_neg _ _
    have h_nat_int : ((2 * (nNat * nNat) : Nat) : Int) = ((dNat * dNat : Nat) : Int) := by
      have h2_cast : ((2 * (nNat * nNat) : Nat) : Int) = 2 * ((nNat * nNat : Nat) : Int) :=
        Int.ofNat_mul 2 (nNat * nNat)
      rw [h2_cast, ← hsq_abs (q.num * p.den), ← hsq_abs (p.num * q.den)]
      exact h_int
    have h_nat : 2 * (nNat * nNat) = dNat * dNat := Int.ofNat.inj h_nat_int
    by_cases hd0 : dNat = 0
    · rw [hd0] at h_nat
      have hn0 : nNat = 0 := by
        by_cases hnz : nNat = 0
        · exact hnz
        · have hp : 0 < nNat * nNat := Nat.mul_pos (by omega) (by omega)
          omega
      have hpz : p.num = 0 := by
        have hpq0 : p.num * q.den = 0 := by omega
        cases Int.mul_eq_zero.mp hpq0 with
        | inl h0 => exact h0
        | inr h0 => have := q.den_pos; omega
      have hqz : q.num = 0 := by
        have hqp0 : q.num * p.den = 0 := by omega
        cases Int.mul_eq_zero.mp hqp0 with
        | inl h0 => exact h0
        | inr h0 => have := p.den_pos; omega
      constructor
      · apply Quot.sound; unfold RawRat.Rel; dsimp only; rw [hpz]; omega
      · apply Quot.sound; unfold RawRat.Rel; dsimp only; rw [hqz]; omega
    · exact absurd h_nat (no_nat_two_sq_eq_sq dNat hd0 nNat)

theorem no_rat_two_sq_eq_one (q : RatQ) :
    FieldK.mul FieldK.two (FieldK.mul q q) ≠ FieldK.one := by
  intro h
  have h0 := no_rat_sq_eq_two_sq FieldK.one q (by rw [FieldK.one_mul, h])
  exact FieldK.zero_ne_one h0.1.symm

end RatQ

/-! ### Concrete Instance 3: `QSqrt2` (Quadratic Field `ℚ(√2)`) -/

/-- Elements `re + im * √2` of `ℚ(√2)`. -/
structure QSqrt2 where
  re : RatQ
  im : RatQ

namespace QSqrt2

private abbrev z : RatQ := FieldK.zero
private abbrev o : RatQ := FieldK.one
private abbrev twoQ : RatQ := FieldK.two

@[ext]
theorem ext {x y : QSqrt2} (h1 : x.re = y.re) (h2 : x.im = y.im) : x = y := by
  cases x; cases y; simp at *; exact ⟨h1, h2⟩

def zero : QSqrt2 := ⟨z, z⟩
def one : QSqrt2 := ⟨o, z⟩
def sqrt2 : QSqrt2 := ⟨z, o⟩

def add (x y : QSqrt2) : QSqrt2 := ⟨FieldK.add x.re y.re, FieldK.add x.im y.im⟩
def neg (x : QSqrt2) : QSqrt2 := ⟨FieldK.neg x.re, FieldK.neg x.im⟩
def mul (x y : QSqrt2) : QSqrt2 :=
  ⟨FieldK.add (FieldK.mul x.re y.re) (FieldK.mul twoQ (FieldK.mul x.im y.im)),
   FieldK.add (FieldK.mul x.re y.im) (FieldK.mul x.im y.re)⟩

def normQ (x : QSqrt2) : RatQ :=
  FieldK.sub (FieldK.mul x.re x.re) (FieldK.mul twoQ (FieldK.mul x.im x.im))

theorem normQ_ne_zero {x : QSqrt2} (hx : x ≠ zero) : normQ x ≠ z := by
  intro h0
  have heq := FieldK.sub_eq_zero.mp h0
  have hab := RatQ.no_rat_sq_eq_two_sq x.re x.im heq
  apply hx
  exact ext hab.1 hab.2

def inv (x : QSqrt2) : QSqrt2 :=
  let d := FieldK.inv (normQ x)
  ⟨FieldK.mul x.re d, FieldK.neg (FieldK.mul x.im d)⟩

instance : FieldCharNeTwo QSqrt2 where
  zero := zero
  one := one
  add := add
  neg := neg
  mul := mul
  inv := inv
  add_assoc := fun a b c => ext (FieldK.add_assoc _ _ _) (FieldK.add_assoc _ _ _)
  add_comm := fun a b => ext (FieldK.add_comm _ _) (FieldK.add_comm _ _)
  zero_add := fun a => ext (FieldK.zero_add _) (FieldK.zero_add _)
  add_left_neg := fun a => ext (FieldK.add_left_neg _) (FieldK.add_left_neg _)
  mul_assoc := fun a b c => by
    apply ext <;> dsimp [mul]
    · have lhs_eq :
          FieldK.add (FieldK.mul (FieldK.add (FieldK.mul a.re b.re) (FieldK.mul twoQ (FieldK.mul a.im b.im))) c.re)
            (FieldK.mul twoQ (FieldK.mul (FieldK.add (FieldK.mul a.re b.im) (FieldK.mul a.im b.re)) c.im)) =
          FieldK.add
            (FieldK.add (FieldK.mul a.re (FieldK.mul b.re c.re))
                        (FieldK.mul twoQ (FieldK.mul a.im (FieldK.mul b.im c.re))))
            (FieldK.add (FieldK.mul twoQ (FieldK.mul a.re (FieldK.mul b.im c.im)))
                        (FieldK.mul twoQ (FieldK.mul a.im (FieldK.mul b.re c.im)))) := by
        rw [FieldK.right_distrib, FieldK.right_distrib, FieldK.left_distrib twoQ,
            FieldK.mul_assoc a.re b.re c.re,
            FieldK.mul_assoc twoQ (FieldK.mul a.im b.im) c.re,
            FieldK.mul_assoc a.im b.im c.re,
            FieldK.mul_assoc a.re b.im c.im,
            FieldK.mul_assoc a.im b.re c.im]
      have rhs_eq :
          FieldK.add (FieldK.mul a.re (FieldK.add (FieldK.mul b.re c.re) (FieldK.mul twoQ (FieldK.mul b.im c.im))))
            (FieldK.mul twoQ (FieldK.mul a.im (FieldK.add (FieldK.mul b.re c.im) (FieldK.mul b.im c.re)))) =
          FieldK.add
            (FieldK.add (FieldK.mul a.re (FieldK.mul b.re c.re))
                        (FieldK.mul twoQ (FieldK.mul a.re (FieldK.mul b.im c.im))))
            (FieldK.add (FieldK.mul twoQ (FieldK.mul a.im (FieldK.mul b.re c.im)))
                        (FieldK.mul twoQ (FieldK.mul a.im (FieldK.mul b.im c.re)))) := by
        rw [FieldK.left_distrib a.re, FieldK.left_distrib a.im, FieldK.left_distrib twoQ,
            ← FieldK.mul_assoc a.re twoQ (FieldK.mul b.im c.im),
            FieldK.mul_comm a.re twoQ,
            FieldK.mul_assoc twoQ a.re (FieldK.mul b.im c.im)]
      rw [lhs_eq, rhs_eq]
      let A := FieldK.mul a.re (FieldK.mul b.re c.re)
      let B := FieldK.mul twoQ (FieldK.mul a.im (FieldK.mul b.im c.re))
      let C := FieldK.mul twoQ (FieldK.mul a.re (FieldK.mul b.im c.im))
      let D := FieldK.mul twoQ (FieldK.mul a.im (FieldK.mul b.re c.im))
      change FieldK.add (FieldK.add A B) (FieldK.add C D) =
             FieldK.add (FieldK.add A C) (FieldK.add D B)
      rw [FieldK.add_assoc A B (FieldK.add C D),
          FieldK.add_comm B (FieldK.add C D),
          FieldK.add_assoc C D B,
          ← FieldK.add_assoc A C (FieldK.add D B)]
    · have lhs_eq :
          FieldK.add (FieldK.mul (FieldK.add (FieldK.mul a.re b.re) (FieldK.mul twoQ (FieldK.mul a.im b.im))) c.im)
            (FieldK.mul (FieldK.add (FieldK.mul a.re b.im) (FieldK.mul a.im b.re)) c.re) =
          FieldK.add
            (FieldK.add (FieldK.mul a.re (FieldK.mul b.re c.im))
                        (FieldK.mul twoQ (FieldK.mul a.im (FieldK.mul b.im c.im))))
            (FieldK.add (FieldK.mul a.re (FieldK.mul b.im c.re))
                        (FieldK.mul a.im (FieldK.mul b.re c.re))) := by
        rw [FieldK.right_distrib, FieldK.right_distrib,
            FieldK.mul_assoc a.re b.re c.im,
            FieldK.mul_assoc twoQ (FieldK.mul a.im b.im) c.im,
            FieldK.mul_assoc a.im b.im c.im,
            FieldK.mul_assoc a.re b.im c.re,
            FieldK.mul_assoc a.im b.re c.re]
      have rhs_eq :
          FieldK.add (FieldK.mul a.re (FieldK.add (FieldK.mul b.re c.im) (FieldK.mul b.im c.re)))
            (FieldK.mul a.im (FieldK.add (FieldK.mul b.re c.re) (FieldK.mul twoQ (FieldK.mul b.im c.im)))) =
          FieldK.add
            (FieldK.add (FieldK.mul a.re (FieldK.mul b.re c.im))
                        (FieldK.mul a.re (FieldK.mul b.im c.re)))
            (FieldK.add (FieldK.mul a.im (FieldK.mul b.re c.re))
                        (FieldK.mul twoQ (FieldK.mul a.im (FieldK.mul b.im c.im)))) := by
        rw [FieldK.left_distrib a.re, FieldK.left_distrib a.im,
            ← FieldK.mul_assoc a.im twoQ (FieldK.mul b.im c.im),
            FieldK.mul_comm a.im twoQ,
            FieldK.mul_assoc twoQ a.im (FieldK.mul b.im c.im)]
      rw [lhs_eq, rhs_eq]
      let A := FieldK.mul a.re (FieldK.mul b.re c.im)
      let B := FieldK.mul twoQ (FieldK.mul a.im (FieldK.mul b.im c.im))
      let C := FieldK.mul a.re (FieldK.mul b.im c.re)
      let D := FieldK.mul a.im (FieldK.mul b.re c.re)
      change FieldK.add (FieldK.add A B) (FieldK.add C D) =
             FieldK.add (FieldK.add A C) (FieldK.add D B)
      rw [FieldK.add_assoc A B (FieldK.add C D),
          FieldK.add_comm B (FieldK.add C D),
          FieldK.add_assoc C D B,
          ← FieldK.add_assoc A C (FieldK.add D B)]
  mul_comm := fun a b => by
    apply ext <;> dsimp [mul]
    · rw [FieldK.mul_comm a.re b.re, FieldK.mul_comm a.im b.im]
    · rw [FieldK.mul_comm a.re b.im, FieldK.mul_comm a.im b.re, FieldK.add_comm]
  one_mul := fun a => by
    apply ext <;> dsimp [mul, one]
    · rw [FieldK.one_mul, FieldK.zero_mul, FieldK.mul_zero, FieldK.add_zero]
    · rw [FieldK.one_mul, FieldK.zero_mul, FieldK.add_zero]
  mul_left_inv := fun a ha => by
    have hdnz := normQ_ne_zero ha
    apply ext <;> dsimp [mul, inv, one]
    · let d := FieldK.inv (normQ a)
      change FieldK.add (FieldK.mul (FieldK.mul a.re d) a.re)
                        (FieldK.mul twoQ (FieldK.mul (FieldK.neg (FieldK.mul a.im d)) a.im)) = o
      have e1 : FieldK.mul (FieldK.mul a.re d) a.re = FieldK.mul (FieldK.mul a.re a.re) d := by
        rw [FieldK.mul_assoc, FieldK.mul_comm d a.re, ← FieldK.mul_assoc]
      have e2 : FieldK.mul twoQ (FieldK.mul (FieldK.neg (FieldK.mul a.im d)) a.im) =
                FieldK.neg (FieldK.mul (FieldK.mul twoQ (FieldK.mul a.im a.im)) d) := by
        rw [FieldK.neg_mul, FieldK.mul_neg,
            FieldK.mul_assoc a.im d a.im, FieldK.mul_comm d a.im,
            ← FieldK.mul_assoc a.im a.im d, ← FieldK.mul_assoc twoQ (FieldK.mul a.im a.im) d]
      rw [e1, e2]
      change FieldK.sub (FieldK.mul (FieldK.mul a.re a.re) d)
                        (FieldK.mul (FieldK.mul twoQ (FieldK.mul a.im a.im)) d) = o
      rw [← FieldK.sub_mul]
      exact FieldK.mul_right_inv hdnz
    · let d := FieldK.inv (normQ a)
      change FieldK.add (FieldK.mul (FieldK.mul a.re d) a.im)
                        (FieldK.mul (FieldK.neg (FieldK.mul a.im d)) a.re) = z
      have e1 : FieldK.mul (FieldK.mul a.re d) a.im = FieldK.mul (FieldK.mul a.re a.im) d := by
        rw [FieldK.mul_assoc, FieldK.mul_comm d a.im, ← FieldK.mul_assoc]
      have e2 : FieldK.mul (FieldK.neg (FieldK.mul a.im d)) a.re =
                FieldK.neg (FieldK.mul (FieldK.mul a.re a.im) d) := by
        rw [FieldK.neg_mul, FieldK.mul_assoc, FieldK.mul_comm d a.re,
            ← FieldK.mul_assoc, FieldK.mul_comm a.im a.re]
      rw [e1, e2, FieldK.add_right_neg]
  left_distrib := fun a b c => by
    apply ext <;> dsimp [mul, add]
    · rw [FieldK.left_distrib a.re, FieldK.left_distrib a.im, FieldK.left_distrib twoQ]
      let A := FieldK.mul a.re b.re
      let B := FieldK.mul a.re c.re
      let C := FieldK.mul twoQ (FieldK.mul a.im b.im)
      let D := FieldK.mul twoQ (FieldK.mul a.im c.im)
      change FieldK.add (FieldK.add A B) (FieldK.add C D) =
             FieldK.add (FieldK.add A C) (FieldK.add B D)
      rw [FieldK.add_assoc A B (FieldK.add C D),
          ← FieldK.add_assoc B C D, FieldK.add_comm B C,
          FieldK.add_assoc C B D, ← FieldK.add_assoc A C (FieldK.add B D)]
    · rw [FieldK.left_distrib a.re, FieldK.left_distrib a.im]
      let A := FieldK.mul a.re b.im
      let B := FieldK.mul a.re c.im
      let C := FieldK.mul a.im b.re
      let D := FieldK.mul a.im c.re
      change FieldK.add (FieldK.add A B) (FieldK.add C D) =
             FieldK.add (FieldK.add A C) (FieldK.add B D)
      rw [FieldK.add_assoc A B (FieldK.add C D),
          ← FieldK.add_assoc B C D, FieldK.add_comm B C,
          FieldK.add_assoc C B D, ← FieldK.add_assoc A C (FieldK.add B D)]
  zero_ne_one := fun h => FieldK.zero_ne_one (congrArg QSqrt2.re h)
  two_ne_zero := fun h => FieldCharNeTwo.two_ne_zero (congrArg QSqrt2.re h)

theorem sqrt2_sq : mul sqrt2 sqrt2 = ⟨twoQ, z⟩ := by
  apply ext <;> dsimp [mul, sqrt2]
  · rw [FieldK.zero_mul, FieldK.one_mul, FieldK.mul_one, FieldK.zero_add]
  · rw [FieldK.zero_mul, FieldK.mul_zero, FieldK.add_zero]

end QSqrt2

end Conjecture00000007606
