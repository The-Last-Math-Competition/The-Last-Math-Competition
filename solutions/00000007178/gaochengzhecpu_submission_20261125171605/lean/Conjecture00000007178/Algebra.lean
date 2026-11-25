/-
  Conjecture 00000007178 — Algebraic Foundations in Core Lean 4.19.0
  Self-contained commutative ring and field hierarchy with explicit instances
  F2 (|F2| = 2, char = 2), F3 (|F3| = 3, char = 3), and F4 (|F4| = 4, char = 2).
-/

namespace Conjecture00000007178

universe u

/-- Multiplicative unit typeclass in Core Lean 4. -/
class One (α : Type u) where
  one : α

instance (priority := 100) [Zero α] : OfNat α 0 where
  ofNat := Zero.zero

instance (priority := 100) [One α] : OfNat α 1 where
  ofNat := One.one

/-- Multiplicative inverse typeclass in Core Lean 4. -/
class Inv (α : Type u) where
  inv : α → α

postfix:max "⁻¹" => Inv.inv

/-- Self-contained commutative ring typeclass in Core Lean 4. -/
class CommRingR (R : Type u) extends Zero R, One R, Add R, Mul R, Neg R, Sub R where
  add_assoc : ∀ a b c : R, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : R, a + b = b + a
  zero_add : ∀ a : R, 0 + a = a
  add_zero : ∀ a : R, a + 0 = a
  neg_add_cancel : ∀ a : R, -a + a = 0
  sub_eq_add_neg : ∀ a b : R, a - b = a + (-b)
  mul_assoc : ∀ a b c : R, (a * b) * c = a * (b * c)
  mul_comm : ∀ a b : R, a * b = b * a
  one_mul : ∀ a : R, 1 * a = a
  mul_one : ∀ a : R, a * 1 = a
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

/-- Self-contained field typeclass in Core Lean 4. -/
class FieldR (F : Type u) extends CommRingR F, Inv F where
  zero_ne_one : (0 : F) ≠ 1
  mul_inv_cancel : ∀ a : F, a ≠ 0 → a * a⁻¹ = 1
  inv_zero : (0 : F)⁻¹ = 0

namespace CommRingR

section BasicLemmas
variable {R : Type u} [CommRingR R]

theorem add_neg_cancel (a : R) : a + (-a) = 0 := by
  rw [add_comm, neg_add_cancel]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  have h1 : -a + (a + b) = -a + (a + c) := congrArg (fun x => -a + x) h
  rw [← add_assoc, neg_add_cancel, zero_add, ← add_assoc, neg_add_cancel, zero_add] at h1
  exact h1

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  apply add_left_cancel (a := b)
  rw [add_comm b a, h, add_comm b c]

theorem zero_mul (a : R) : (0 : R) * a = 0 := by
  apply add_left_cancel (a := (0 : R) * a)
  rw [← right_distrib, zero_add, add_zero]

theorem mul_zero (a : R) : a * (0 : R) = 0 := by
  rw [mul_comm, zero_mul]

theorem neg_zero : -(0 : R) = 0 := by
  apply add_left_cancel (a := (0 : R))
  rw [add_neg_cancel, add_zero]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  apply add_left_cancel (a := a)
  rw [add_neg_cancel, h]

theorem neg_neg (a : R) : -(-a) = a :=
  neg_eq_of_add_eq_zero (neg_add_cancel a)

theorem neg_mul (a b : R) : (-a) * b = -(a * b) := by
  symm
  apply neg_eq_of_add_eq_zero
  rw [← right_distrib, add_neg_cancel, zero_mul]

theorem mul_neg (a b : R) : a * (-b) = -(a * b) := by
  rw [mul_comm, neg_mul, mul_comm]

theorem neg_mul_neg (a b : R) : (-a) * (-b) = a * b := by
  rw [neg_mul, mul_neg, neg_neg]

theorem neg_one_mul (a : R) : (-1 : R) * a = -a := by
  rw [neg_mul, one_mul]

theorem sub_self (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg, add_neg_cancel]

theorem sub_zero (a : R) : a - (0 : R) = a := by
  rw [sub_eq_add_neg, neg_zero, add_zero]

theorem zero_sub (a : R) : (0 : R) - a = -a := by
  rw [sub_eq_add_neg, zero_add]

theorem sub_eq_zero {a b : R} : a - b = 0 ↔ a = b := by
  constructor
  · intro h
    apply add_right_cancel (b := -b)
    rw [← sub_eq_add_neg, h, add_neg_cancel]
  · intro h
    rw [h, sub_self]

theorem mul_sub (a b c : R) : a * (b - c) = a * b - a * c := by
  rw [sub_eq_add_neg, left_distrib, mul_neg, ← sub_eq_add_neg]

theorem sub_mul (a b c : R) : (a - b) * c = a * c - b * c := by
  rw [sub_eq_add_neg, right_distrib, neg_mul, ← sub_eq_add_neg]

theorem neg_add (a b : R) : -(a + b) = -a + (-b) := by
  apply neg_eq_of_add_eq_zero
  calc
    (a + b) + (-a + -b) = a + (b + (-b + -a)) := by
      rw [add_comm (-a) (-b), add_assoc]
    _ = a + ((b + -b) + -a) := by rw [← add_assoc b (-b) (-a)]
    _ = a + ((0 : R) + -a) := by rw [add_neg_cancel]
    _ = a + -a := by rw [zero_add]
    _ = 0 := add_neg_cancel a

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  have h' : b + a = 0 := by rw [add_comm, h]
  exact (neg_eq_of_add_eq_zero h').symm

end BasicLemmas
end CommRingR

namespace FieldR

section FieldLemmas
variable {F : Type u} [FieldR F]
open CommRingR

theorem one_ne_zero : (1 : F) ≠ 0 :=
  fun h => FieldR.zero_ne_one h.symm

theorem inv_mul_cancel {a : F} (ha : a ≠ 0) : a⁻¹ * a = 1 := by
  rw [mul_comm, FieldR.mul_inv_cancel a ha]

theorem mul_eq_zero {a b : F} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    calc
      b = (1 : F) * b := (one_mul b).symm
      _ = (a⁻¹ * a) * b := by rw [inv_mul_cancel ha]
      _ = a⁻¹ * (a * b) := by rw [mul_assoc]
      _ = a⁻¹ * (0 : F) := by rw [h]
      _ = 0 := mul_zero a⁻¹

theorem mul_ne_zero {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro h
  cases mul_eq_zero h with
  | inl h0 => exact ha h0
  | inr h0 => exact hb h0

theorem inv_ne_zero {a : F} (ha : a ≠ 0) : a⁻¹ ≠ 0 := by
  intro h
  have h1 : a * a⁻¹ = 1 := FieldR.mul_inv_cancel a ha
  rw [h, mul_zero] at h1
  exact FieldR.zero_ne_one h1

theorem mul_left_cancel {a b c : F} (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  have h0 : a * (b - c) = 0 := by
    rw [mul_sub, h, sub_self]
  cases mul_eq_zero h0 with
  | inl h1 => exact absurd h1 ha
  | inr h1 => exact (sub_eq_zero.mp h1)

theorem mul_right_cancel {a b c : F} (hb : b ≠ 0) (h : a * b = c * b) : a = c := by
  apply mul_left_cancel hb
  rw [mul_comm b a, h, mul_comm b c]

theorem neg_ne_zero {a : F} (ha : a ≠ 0) : -a ≠ 0 := by
  intro h
  apply ha
  calc
    a = -(-a) := (neg_neg a).symm
    _ = -(0 : F) := by rw [h]
    _ = 0 := neg_zero

theorem neg_one_ne_zero : (-1 : F) ≠ 0 :=
  neg_ne_zero one_ne_zero

theorem neg_one_ne_one (hchar : (1 : F) + 1 ≠ 0) : (-1 : F) ≠ 1 := by
  intro h
  apply hchar
  calc
    (1 : F) + 1 = (-1 : F) + 1 := by rw [h]
    _ = 0 := neg_add_cancel 1

/-- In every field of cardinality at least 3 (witnessed by `α ≠ 0` and `α ≠ 1`),
there exists `β ≠ 0` with `1 + β ≠ 0`. -/
theorem exists_nonzero_one_add_ne_zero
    (hcard : ∃ α : F, α ≠ 0 ∧ α ≠ 1) :
    ∃ β : F, β ≠ 0 ∧ (1 : F) + β ≠ 0 := by
  rcases hcard with ⟨α, hα0, hα1⟩
  by_cases hsum : (1 : F) + α = 0
  · refine ⟨1, one_ne_zero, ?_⟩
    intro htwo
    have hα_eq_neg1 : α = -1 := by
      have h' : α + 1 = 0 := by rw [add_comm, hsum]
      exact eq_neg_of_add_eq_zero h'
    have hneg1_eq_1 : (-1 : F) = 1 :=
      neg_eq_of_add_eq_zero htwo
    exact hα1 (hα_eq_neg1.trans hneg1_eq_1)
  · exact ⟨α, hα0, hsum⟩

end FieldLemmas
end FieldR

/-! ### Concrete Finite Fields: `F2`, `F3`, and `F4` -/

/-- The binary field `𝔽₂`. -/
inductive F2 where
  | zero : F2
  | one  : F2
  deriving DecidableEq, Repr

namespace F2

def add : F2 → F2 → F2
  | zero, x => x
  | x, zero => x
  | one, one => zero

def mul : F2 → F2 → F2
  | one, one => one
  | _, _ => zero

instance : Zero F2 := ⟨zero⟩
instance : One F2 := ⟨one⟩
instance : Add F2 := ⟨add⟩
instance : Mul F2 := ⟨mul⟩
instance : Neg F2 := ⟨id⟩
instance : Sub F2 := ⟨add⟩
instance : Inv F2 := ⟨id⟩

instance : FieldR F2 where
  add_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl
  zero_add a := by cases a <;> rfl
  add_zero a := by cases a <;> rfl
  neg_add_cancel a := by cases a <;> rfl
  sub_eq_add_neg a b := by cases a <;> cases b <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_comm a b := by cases a <;> cases b <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  left_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  right_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  zero_ne_one := by decide
  mul_inv_cancel a ha := by cases a <;> first | contradiction | rfl
  inv_zero := rfl

theorem char_two : (1 : F2) + 1 = 0 := rfl

theorem eq_one_of_ne_zero {x : F2} (hx : x ≠ 0) : x = 1 := by
  cases x with
  | zero => exact absurd rfl hx
  | one => rfl

end F2

/-- The ternary field `𝔽₃`. -/
inductive F3 where
  | zero : F3
  | one  : F3
  | two  : F3
  deriving DecidableEq, Repr

namespace F3

def toNat : F3 → Nat
  | zero => 0
  | one  => 1
  | two  => 2

def ofMod3 (n : Nat) : F3 :=
  match n % 3 with
  | 0 => zero
  | 1 => one
  | _ => two

def add (a b : F3) : F3 := ofMod3 (toNat a + toNat b)
def mul (a b : F3) : F3 := ofMod3 (toNat a * toNat b)

def neg : F3 → F3
  | zero => zero
  | one  => two
  | two  => one

def sub (a b : F3) : F3 := add a (neg b)

def inv : F3 → F3
  | zero => zero
  | one  => one
  | two  => two

instance : Zero F3 := ⟨zero⟩
instance : One F3 := ⟨one⟩
instance : Add F3 := ⟨add⟩
instance : Mul F3 := ⟨mul⟩
instance : Neg F3 := ⟨neg⟩
instance : Sub F3 := ⟨sub⟩
instance : Inv F3 := ⟨inv⟩

instance : FieldR F3 where
  add_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl
  zero_add a := by cases a <;> rfl
  add_zero a := by cases a <;> rfl
  neg_add_cancel a := by cases a <;> rfl
  sub_eq_add_neg a b := by cases a <;> cases b <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_comm a b := by cases a <;> cases b <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  left_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  right_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  zero_ne_one := by decide
  mul_inv_cancel a ha := by cases a <;> first | contradiction | rfl
  inv_zero := rfl

theorem char_ne_two : (1 : F3) + 1 ≠ 0 := by decide

theorem card_ge_three : ∃ α : F3, α ≠ 0 ∧ α ≠ 1 :=
  ⟨F3.two, by decide, by decide⟩

end F3

/-- The four-element field `𝔽₄ = 𝔽₂[ω]/(ω² + ω + 1)`, of characteristic `2` and size `4`. -/
inductive F4 where
  | zero   : F4
  | one    : F4
  | omega  : F4
  | omega1 : F4
  deriving DecidableEq, Repr

namespace F4

def add : F4 → F4 → F4
  | zero, x => x
  | x, zero => x
  | one, one => zero
  | omega, omega => zero
  | omega1, omega1 => zero
  | one, omega => omega1
  | omega, one => omega1
  | one, omega1 => omega
  | omega1, one => omega
  | omega, omega1 => one
  | omega1, omega => one

def mul : F4 → F4 → F4
  | zero, _ => zero
  | _, zero => zero
  | one, x => x
  | x, one => x
  | omega, omega => omega1
  | omega, omega1 => one
  | omega1, omega => one
  | omega1, omega1 => omega

def inv : F4 → F4
  | zero => zero
  | one => one
  | omega => omega1
  | omega1 => omega

instance : Zero F4 := ⟨zero⟩
instance : One F4 := ⟨one⟩
instance : Add F4 := ⟨add⟩
instance : Mul F4 := ⟨mul⟩
instance : Neg F4 := ⟨id⟩
instance : Sub F4 := ⟨add⟩
instance : Inv F4 := ⟨inv⟩

instance : FieldR F4 where
  add_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl
  zero_add a := by cases a <;> rfl
  add_zero a := by cases a <;> rfl
  neg_add_cancel a := by cases a <;> rfl
  sub_eq_add_neg a b := by cases a <;> cases b <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_comm a b := by cases a <;> cases b <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  left_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  right_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  zero_ne_one := by decide
  mul_inv_cancel a ha := by cases a <;> first | contradiction | rfl
  inv_zero := rfl

theorem char_two : (1 : F4) + 1 = 0 := rfl

theorem card_ge_three : ∃ α : F4, α ≠ 0 ∧ α ≠ 1 :=
  ⟨F4.omega, by decide, by decide⟩

end F4

end Conjecture00000007178
