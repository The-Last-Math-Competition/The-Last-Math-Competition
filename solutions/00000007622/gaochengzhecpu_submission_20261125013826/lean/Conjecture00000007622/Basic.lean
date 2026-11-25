/-
  Conjecture 00000007622 — Foundational Algebraic Structures
  Self-contained CommRingOps, FieldOps, CharNeTwoField, OrderedField,
  and an explicit axiom-free construction of the rational field QRat (ℚ)
  in Core Lean 4.19.0.
-/

namespace Conjecture00000007622

/-- Self-contained commutative unital ring with `1 ≠ 0`. -/
class CommRingOps (R : Type) extends Add R, Sub R, Neg R, Mul R where
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
  one_ne_zero : one ≠ zero

instance [CommRingOps R] : OfNat R 0 := ⟨CommRingOps.zero⟩
instance [CommRingOps R] : OfNat R 1 := ⟨CommRingOps.one⟩

section RingLemmas
variable {R : Type} [CommRingOps R]

@[simp] theorem r_zero_def : (CommRingOps.zero : R) = 0 := rfl
@[simp] theorem r_one_def : (CommRingOps.one : R) = 1 := rfl

@[simp] theorem r_zero_add (a : R) : 0 + a = a := CommRingOps.zero_add a
@[simp] theorem r_add_zero (a : R) : a + 0 = a := CommRingOps.add_zero a
@[simp] theorem r_one_mul (a : R) : 1 * a = a := CommRingOps.one_mul a
@[simp] theorem r_mul_one (a : R) : a * 1 = a := CommRingOps.mul_one a
@[simp] theorem r_neg_add_cancel (a : R) : -a + a = 0 := CommRingOps.neg_add_cancel a

theorem r_one_ne_zero : (1 : R) ≠ 0 := CommRingOps.one_ne_zero

theorem r_add_neg_cancel (a : R) : a + -a = 0 := by
  rw [CommRingOps.add_comm, r_neg_add_cancel]

@[simp] theorem r_add_neg_cancel_simp (a : R) : a + -a = 0 := r_add_neg_cancel a

theorem r_add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  have h1 : -a + (a + b) = -a + (a + c) := congrArg (-a + ·) h
  rw [← CommRingOps.add_assoc, ← CommRingOps.add_assoc, r_neg_add_cancel,
      r_zero_add, r_zero_add] at h1
  exact h1

theorem r_add_right_cancel {a b c : R} (h : b + a = c + a) : b = c := by
  apply r_add_left_cancel (a := a)
  rw [CommRingOps.add_comm a b, CommRingOps.add_comm a c]
  exact h

theorem r_add_left_comm (a b c : R) : a + (b + c) = b + (a + c) := by
  rw [← CommRingOps.add_assoc, CommRingOps.add_comm a b, CommRingOps.add_assoc]

theorem r_mul_left_comm (a b c : R) : a * (b * c) = b * (a * c) := by
  rw [← CommRingOps.mul_assoc, CommRingOps.mul_comm a b, CommRingOps.mul_assoc]

@[simp] theorem r_neg_zero : -(0 : R) = 0 := by
  apply r_add_left_cancel (a := (0 : R))
  rw [r_add_neg_cancel, r_add_zero]

@[simp] theorem r_neg_neg (a : R) : - -a = a := by
  apply r_add_left_cancel (a := -a)
  rw [r_add_neg_cancel, r_neg_add_cancel]

theorem r_neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  apply r_add_left_cancel (a := a)
  rw [r_add_neg_cancel, h]

theorem r_neg_add (a b : R) : -(a + b) = -a + -b := by
  apply r_neg_eq_of_add_eq_zero
  calc
    (a + b) + (-a + -b) = a + (b + (-b + -a)) := by
      rw [CommRingOps.add_comm (-a) (-b), CommRingOps.add_assoc]
    _ = a + ((b + -b) + -a) := by rw [← CommRingOps.add_assoc b (-b) (-a)]
    _ = a + (0 + -a) := by rw [r_add_neg_cancel]
    _ = a + -a := by rw [r_zero_add]
    _ = 0 := r_add_neg_cancel a

@[simp] theorem r_mul_zero (a : R) : a * 0 = 0 := by
  apply r_add_left_cancel (a := a * 0)
  rw [← CommRingOps.left_distrib, r_add_zero, r_add_zero]

@[simp] theorem r_zero_mul (a : R) : 0 * a = 0 := by
  rw [CommRingOps.mul_comm, r_mul_zero]

theorem r_neg_mul (a b : R) : -a * b = -(a * b) := by
  symm
  apply r_neg_eq_of_add_eq_zero
  rw [← CommRingOps.right_distrib, r_add_neg_cancel, r_zero_mul]

theorem r_mul_neg (a b : R) : a * -b = -(a * b) := by
  rw [CommRingOps.mul_comm, r_neg_mul, CommRingOps.mul_comm]

@[simp] theorem r_neg_mul_neg (a b : R) : -a * -b = a * b := by
  rw [r_neg_mul, r_mul_neg, r_neg_neg]

theorem r_neg_one_mul (a : R) : (-1 : R) * a = -a := by
  rw [r_neg_mul, r_one_mul]

@[simp] theorem r_sub_self (a : R) : a - a = 0 := by
  rw [CommRingOps.sub_eq_add_neg, r_add_neg_cancel]

@[simp] theorem r_sub_zero (a : R) : a - 0 = a := by
  rw [CommRingOps.sub_eq_add_neg, r_neg_zero, r_add_zero]

theorem r_sub_eq_zero {a b : R} : a - b = 0 ↔ a = b := by
  constructor
  · intro h
    apply r_add_right_cancel (a := -b)
    rw [← CommRingOps.sub_eq_add_neg, h]
    exact (r_add_neg_cancel b).symm
  · intro h
    rw [h, r_sub_self]

theorem r_neg_eq_zero {a : R} : -a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have h1 : - -a = -(0 : R) := congrArg (Neg.neg) h
    rw [r_neg_neg, r_neg_zero] at h1
    exact h1
  · intro h
    rw [h, r_neg_zero]

def twoR (R : Type) [CommRingOps R] : R := 1 + 1

theorem r_two_mul (a : R) : twoR R * a = a + a := by
  unfold twoR
  rw [CommRingOps.right_distrib, r_one_mul]

end RingLemmas

/-- Self-contained field structure extending `CommRingOps`. -/
class FieldOps (F : Type) extends CommRingOps F where
  inv : F → F
  mul_inv_cancel : ∀ {a : F}, a ≠ 0 → a * inv a = 1

postfix:max "⁻¹" => FieldOps.inv

section FieldLemmas
variable {F : Type} [FieldOps F]

theorem f_mul_inv_cancel {a : F} (ha : a ≠ 0) : a * a⁻¹ = 1 :=
  FieldOps.mul_inv_cancel ha

theorem f_inv_mul_cancel {a : F} (ha : a ≠ 0) : a⁻¹ * a = 1 := by
  rw [CommRingOps.mul_comm, FieldOps.mul_inv_cancel ha]

theorem f_mul_eq_zero {a b : F} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      calc
        b = 1 * b := (r_one_mul b).symm
        _ = (a⁻¹ * a) * b := by rw [f_inv_mul_cancel ha]
        _ = a⁻¹ * (a * b) := CommRingOps.mul_assoc a⁻¹ a b
        _ = a⁻¹ * 0 := by rw [h]
        _ = 0 := r_mul_zero a⁻¹
  · intro h
    cases h with
    | inl ha => rw [ha, r_zero_mul]
    | inr hb => rw [hb, r_mul_zero]

theorem f_sq_eq_zero {a : F} : a * a = 0 ↔ a = 0 := by
  rw [f_mul_eq_zero]
  exact ⟨fun h => h.elim id id, Or.inl⟩

theorem f_inv_ne_zero {a : F} (ha : a ≠ 0) : a⁻¹ ≠ 0 := by
  intro hinv
  have h1 : a * a⁻¹ = 1 := FieldOps.mul_inv_cancel ha
  rw [hinv, r_mul_zero] at h1
  exact r_one_ne_zero h1.symm

end FieldLemmas

/-- Field of characteristic not equal to 2 (`1 + 1 ≠ 0`). -/
class CharNeTwoField (F : Type) extends FieldOps F where
  two_ne_zero : (1 : F) + 1 ≠ 0

section CharNeTwoLemmas
variable {F : Type} [CharNeTwoField F]

def halfF (F : Type) [CharNeTwoField F] : F := (twoR F)⁻¹

theorem twoR_ne_zero : twoR F ≠ 0 := CharNeTwoField.two_ne_zero

theorem two_mul_half : twoR F * halfF F = 1 :=
  FieldOps.mul_inv_cancel twoR_ne_zero

theorem half_mul_two : halfF F * twoR F = 1 :=
  f_inv_mul_cancel twoR_ne_zero

theorem half_ne_zero : halfF F ≠ 0 :=
  f_inv_ne_zero twoR_ne_zero

theorem half_add_half : halfF F + halfF F = 1 := by
  rw [← r_two_mul, two_mul_half]

end CharNeTwoLemmas

/-- Ordered field axiomatized via its strict positive cone `Pos`.
    Every ordered field (including both ℚ and ℝ) satisfies `OrderedField`. -/
class OrderedField (F : Type) extends FieldOps F where
  Pos : F → Prop
  one_pos : Pos 1
  not_pos_zero : ¬ Pos 0
  add_pos : ∀ {a b : F}, Pos a → Pos b → Pos (a + b)
  mul_pos : ∀ {a b : F}, Pos a → Pos b → Pos (a * b)
  trichotomy : ∀ a : F, Pos a ∨ a = 0 ∨ Pos (-a)

section OrderedFieldLemmas
variable {F : Type} [OrderedField F]

def NonnegF (a : F) : Prop := a = 0 ∨ OrderedField.Pos a

theorem pos_ne_zero {a : F} (h : OrderedField.Pos a) : a ≠ 0 := by
  intro h0
  rw [h0] at h
  exact OrderedField.not_pos_zero h

instance orderedFieldToCharNeTwo : CharNeTwoField F where
  two_ne_zero := pos_ne_zero (OrderedField.add_pos OrderedField.one_pos OrderedField.one_pos)

theorem sq_pos_of_ne_zero {a : F} (ha : a ≠ 0) : OrderedField.Pos (a * a) := by
  rcases OrderedField.trichotomy a with hp | h0 | hn
  · exact OrderedField.mul_pos hp hp
  · exact absurd h0 ha
  · have hsq : (-a) * (-a) = a * a := r_neg_mul_neg a a
    rw [← hsq]
    exact OrderedField.mul_pos hn hn

theorem sq_nonneg (a : F) : NonnegF (a * a) := by
  by_cases ha : a = 0
  · left; rw [ha, r_mul_zero]
  · right; exact sq_pos_of_ne_zero ha

theorem nonneg_zero : NonnegF (0 : F) := Or.inl rfl

theorem add_nonneg {a b : F} (ha : NonnegF a) (hb : NonnegF b) : NonnegF (a + b) := by
  rcases ha with rfl | hpa
  · rw [r_zero_add]; exact hb
  · rcases hb with rfl | hpb
    · rw [r_add_zero]; exact Or.inr hpa
    · exact Or.inr (OrderedField.add_pos hpa hpb)

theorem add_eq_zero_of_nonneg {a b : F}
    (ha : NonnegF a) (hb : NonnegF b) (hab : a + b = 0) : a = 0 ∧ b = 0 := by
  rcases ha with rfl | hpa
  · rw [r_zero_add] at hab
    exact ⟨rfl, hab⟩
  · exfalso
    rcases hb with rfl | hpb
    · rw [r_add_zero] at hab
      exact pos_ne_zero hpa hab
    · exact pos_ne_zero (OrderedField.add_pos hpa hpb) hab

theorem sum_two_sq_eq_zero {a b : F} (h : a * a + b * b = 0) : a = 0 ∧ b = 0 := by
  have ⟨ha, hb⟩ := add_eq_zero_of_nonneg (sq_nonneg a) (sq_nonneg b) h
  exact ⟨f_sq_eq_zero.mp ha, f_sq_eq_zero.mp hb⟩

theorem sum_four_sq_eq_zero {a b c d : F}
    (h : (a * a + b * b) + (c * c + d * d) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have ⟨h1, h2⟩ := add_eq_zero_of_nonneg
    (add_nonneg (sq_nonneg a) (sq_nonneg b))
    (add_nonneg (sq_nonneg c) (sq_nonneg d)) h
  have ⟨ha, hb⟩ := sum_two_sq_eq_zero h1
  have ⟨hc, hd⟩ := sum_two_sq_eq_zero h2
  exact ⟨ha, hb, hc, hd⟩

end OrderedFieldLemmas

/-! ### Explicit Construction of `QRat` (ℚ) in Core Lean 4 -/

/-- Unreduced fraction with strictly positive denominator. -/
structure RawRat where
  num : Int
  den : Int
  den_pos : 0 < den

namespace RawRat

def Equiv (x y : RawRat) : Prop := x.num * y.den = y.num * x.den

theorem equiv_refl (x : RawRat) : Equiv x x := rfl

theorem equiv_symm {x y : RawRat} (h : Equiv x y) : Equiv y x := h.symm

theorem equiv_trans {x y z : RawRat} (hxy : Equiv x y) (hyz : Equiv y z) : Equiv x z := by
  unfold Equiv at *
  have hyp : 0 < y.den := y.den_pos
  have hy_ne : y.den ≠ 0 := by omega
  apply Int.eq_of_mul_eq_mul_right hy_ne
  calc
    (x.num * z.den) * y.den = (x.num * y.den) * z.den := by
      rw [Int.mul_assoc, Int.mul_comm z.den y.den, ← Int.mul_assoc]
    _ = (y.num * x.den) * z.den := by rw [hxy]
    _ = (y.num * z.den) * x.den := by
      rw [Int.mul_assoc, Int.mul_comm x.den z.den, ← Int.mul_assoc]
    _ = (z.num * y.den) * x.den := by rw [hyz]
    _ = (z.num * x.den) * y.den := by
      rw [Int.mul_assoc, Int.mul_comm y.den x.den, ← Int.mul_assoc]

def zero : RawRat := ⟨0, 1, by decide⟩
def one : RawRat := ⟨1, 1, by decide⟩

def neg (x : RawRat) : RawRat := ⟨-x.num, x.den, x.den_pos⟩

def add (x y : RawRat) : RawRat :=
  ⟨x.num * y.den + y.num * x.den, x.den * y.den, Int.mul_pos x.den_pos y.den_pos⟩

def mul (x y : RawRat) : RawRat :=
  ⟨x.num * y.num, x.den * y.den, Int.mul_pos x.den_pos y.den_pos⟩

def inv (x : RawRat) : RawRat :=
  if hpos : 0 < x.num then
    ⟨x.den, x.num, hpos⟩
  else if hneg : x.num < 0 then
    ⟨-x.den, -x.num, by omega⟩
  else
    ⟨0, 1, by decide⟩

theorem neg_congr {x x' : RawRat} (hx : Equiv x x') : Equiv (neg x) (neg x') := by
  unfold Equiv neg at *
  simp only [Int.neg_mul, hx]

theorem add_congr {x x' y y' : RawRat} (hx : Equiv x x') (hy : Equiv y y') :
    Equiv (add x y) (add x' y') := by
  unfold Equiv add at *
  dsimp only
  calc
    (x.num * y.den + y.num * x.den) * (x'.den * y'.den)
      = (x.num * x'.den) * (y.den * y'.den) + (y.num * y'.den) * (x.den * x'.den) := by
        rw [Int.add_mul]
        congr 1
        · rw [Int.mul_assoc, ← Int.mul_assoc y.den x'.den y'.den,
              Int.mul_comm y.den x'.den, Int.mul_assoc x'.den y.den y'.den, ← Int.mul_assoc]
        · rw [Int.mul_assoc, ← Int.mul_assoc x.den x'.den y'.den,
              Int.mul_comm (x.den * x'.den) y'.den, ← Int.mul_assoc]
    _ = (x'.num * x.den) * (y.den * y'.den) + (y'.num * y.den) * (x.den * x'.den) := by
        rw [hx, hy]
    _ = (x'.num * y'.den + y'.num * x'.den) * (x.den * y.den) := by
        rw [Int.add_mul]
        congr 1
        · rw [Int.mul_assoc, ← Int.mul_assoc x.den y.den y'.den,
              Int.mul_comm (x.den * y.den) y'.den, ← Int.mul_assoc]
        · rw [Int.mul_assoc, Int.mul_comm x.den x'.den,
              Int.mul_left_comm y.den x'.den x.den, Int.mul_comm y.den x.den,
              ← Int.mul_assoc y'.num x'.den (x.den * y.den)]

theorem mul_congr {x x' y y' : RawRat} (hx : Equiv x x') (hy : Equiv y y') :
    Equiv (mul x y) (mul x' y') := by
  unfold Equiv mul at *
  dsimp only
  calc
    (x.num * y.num) * (x'.den * y'.den)
      = (x.num * x'.den) * (y.num * y'.den) := by
        rw [Int.mul_assoc, ← Int.mul_assoc y.num x'.den y'.den,
            Int.mul_comm y.num x'.den, Int.mul_assoc x'.den y.num y'.den, ← Int.mul_assoc]
    _ = (x'.num * x.den) * (y'.num * y.den) := by rw [hx, hy]
    _ = (x'.num * y'.num) * (x.den * y.den) := by
        rw [Int.mul_assoc, ← Int.mul_assoc x.den y'.num y.den,
            Int.mul_comm x.den y'.num, Int.mul_assoc y'.num x.den y.den, ← Int.mul_assoc]

theorem pos_iff_of_equiv {x y : RawRat} (h : Equiv x y) : (0 < x.num) ↔ (0 < y.num) := by
  unfold Equiv at h
  have hxd : 0 < x.den := x.den_pos
  have hyd : 0 < y.den := y.den_pos
  constructor
  · intro hx
    have hprod : 0 < x.num * y.den := Int.mul_pos hx hyd
    rw [h] at hprod
    by_cases hy : 0 < y.num
    · exact hy
    · exfalso
      have hle : y.num * x.den ≤ 0 := by
        have h1 : (-y.num) * x.den ≥ 0 := by
          by_cases hz : y.num = 0
          · rw [hz]; simp
          · have hpos : 0 < -y.num := by omega
            exact Int.le_of_lt (Int.mul_pos hpos hxd)
        rw [Int.neg_mul] at h1
        omega
      omega
  · intro hy
    have hprod : 0 < y.num * x.den := Int.mul_pos hy hxd
    rw [← h] at hprod
    by_cases hx : 0 < x.num
    · exact hx
    · exfalso
      have hle : x.num * y.den ≤ 0 := by
        have h1 : (-x.num) * y.den ≥ 0 := by
          by_cases hz : x.num = 0
          · rw [hz]; simp
          · have hpos : 0 < -x.num := by omega
            exact Int.le_of_lt (Int.mul_pos hpos hyd)
        rw [Int.neg_mul] at h1
        omega
      omega

theorem neg_iff_of_equiv {x y : RawRat} (h : Equiv x y) : (x.num < 0) ↔ (y.num < 0) := by
  have hneg : Equiv (neg x) (neg y) := neg_congr h
  have hp := pos_iff_of_equiv hneg
  dsimp only [neg] at hp
  omega

theorem inv_congr {x y : RawRat} (h : Equiv x y) : Equiv (inv x) (inv y) := by
  unfold inv
  by_cases hxp : 0 < x.num
  · have hyp : 0 < y.num := (pos_iff_of_equiv h).mp hxp
    rw [dif_pos hxp, dif_pos hyp]
    unfold Equiv at *
    dsimp only
    rw [Int.mul_comm x.den y.num, ← h, Int.mul_comm x.num y.den]
  · rw [dif_neg hxp]
    have hyp : ¬ (0 < y.num) := fun hy => hxp ((pos_iff_of_equiv h).mpr hy)
    rw [dif_neg hyp]
    by_cases hxn : x.num < 0
    · have hyn : y.num < 0 := (neg_iff_of_equiv h).mp hxn
      rw [dif_pos hxn, dif_pos hyn]
      unfold Equiv at *
      dsimp only
      rw [Int.neg_mul, Int.mul_neg, Int.neg_mul, Int.mul_neg]
      congr 1
      rw [Int.mul_comm x.den y.num, ← h, Int.mul_comm x.num y.den]
    · have hyn : ¬ (y.num < 0) := fun hy => hxn ((neg_iff_of_equiv h).mpr hy)
      rw [dif_neg hxn, dif_neg hyn]
      rfl

end RawRat

/-- Exact rational numbers `ℚ = Quot RawRat.Equiv`. -/
def QRat : Type := Quot RawRat.Equiv

namespace QRat

def mk (x : RawRat) : QRat := Quot.mk RawRat.Equiv x
def ofInt (n : Int) : QRat := mk ⟨n, 1, by decide⟩

theorem sound {x y : RawRat} (h : RawRat.Equiv x y) : mk x = mk y := Quot.sound h

private theorem exact_equiv {x y : RawRat} (h : mk x = mk y) : RawRat.Equiv x y := by
  let rel : QRat → Prop := Quot.lift (fun z => RawRat.Equiv x z)
    (fun _ _ hab => propext ⟨fun hxa => RawRat.equiv_trans hxa hab,
                             fun hxb => RawRat.equiv_trans hxb (RawRat.equiv_symm hab)⟩)
  have hxx : rel (mk x) := RawRat.equiv_refl x
  rw [h] at hxx
  exact hxx

def zero : QRat := mk RawRat.zero
def one : QRat := mk RawRat.one

def neg : QRat → QRat :=
  Quot.lift (fun x => mk (RawRat.neg x)) (fun _ _ h => sound (RawRat.neg_congr h))

def add : QRat → QRat → QRat :=
  Quot.lift
    (fun x => Quot.lift (fun y => mk (RawRat.add x y))
      (fun _ _ hy => sound (RawRat.add_congr (RawRat.equiv_refl x) hy)))
    (fun _ _ hx => funext fun q => Quot.inductionOn q fun y =>
      sound (RawRat.add_congr hx (RawRat.equiv_refl y)))

def sub (a b : QRat) : QRat := add a (neg b)

def mul : QRat → QRat → QRat :=
  Quot.lift
    (fun x => Quot.lift (fun y => mk (RawRat.mul x y))
      (fun _ _ hy => sound (RawRat.mul_congr (RawRat.equiv_refl x) hy)))
    (fun _ _ hx => funext fun q => Quot.inductionOn q fun y =>
      sound (RawRat.mul_congr hx (RawRat.equiv_refl y)))

def inv : QRat → QRat :=
  Quot.lift (fun x => mk (RawRat.inv x)) (fun _ _ h => sound (RawRat.inv_congr h))

def Pos : QRat → Prop :=
  Quot.lift (fun x => 0 < x.num) (fun _ _ h => propext (RawRat.pos_iff_of_equiv h))

instance : Neg QRat := ⟨neg⟩
instance : Add QRat := ⟨add⟩
instance : Sub QRat := ⟨sub⟩
instance : Mul QRat := ⟨mul⟩

private theorem int_ring_add_assoc (a b c d e f : Int) :
    ((a * d + c * b) * f + e * (b * d)) * (b * (d * f)) =
    (a * (d * f) + (c * f + e * d) * b) * (b * d * f) := by
  have hb : b * (d * f) = b * d * f := (Int.mul_assoc b d f).symm
  rw [hb]
  congr 1
  rw [Int.add_mul, Int.add_mul, Int.add_assoc]
  congr 1
  · exact Int.mul_assoc a d f
  · rw [Int.mul_assoc c b f, Int.mul_comm b f, ← Int.mul_assoc c f b,
        Int.mul_comm b d, ← Int.mul_assoc e d b]

private theorem int_ring_distrib (a b c d e f : Int) :
    a * (c * f + e * d) * (b * d * (b * f)) =
    (a * c * (b * f) + a * e * (b * d)) * (b * (d * f)) := by
  rw [Int.mul_add, Int.add_mul, Int.add_mul]
  congr 1
  · calc
      a * (c * f) * (b * d * (b * f))
        = (a * c) * (f * ((b * d) * (b * f))) := by
          rw [← Int.mul_assoc a c f, Int.mul_assoc (a * c)]
      _ = (a * c) * ((b * f) * (b * (d * f))) := by
          congr 1
          rw [Int.mul_comm f _, Int.mul_assoc (b * d) (b * f) f,
              Int.mul_left_comm (b * d) (b * f) f, Int.mul_assoc b d f]
      _ = a * c * (b * f) * (b * (d * f)) := (Int.mul_assoc _ _ _).symm
  · calc
      a * (e * d) * (b * d * (b * f))
        = (a * e) * (d * ((b * d) * (b * f))) := by
          rw [← Int.mul_assoc a e d, Int.mul_assoc (a * e)]
      _ = (a * e) * ((b * d) * (b * (d * f))) := by
          congr 1
          rw [Int.mul_left_comm d (b * d) (b * f), Int.mul_left_comm d b f]
      _ = a * e * (b * d) * (b * (d * f)) := (Int.mul_assoc _ _ _).symm

instance : OrderedField QRat where
  zero := zero
  one := one
  inv := inv
  add_assoc a b c := Quot.inductionOn a fun x => Quot.inductionOn b fun y =>
    Quot.inductionOn c fun z => sound (int_ring_add_assoc x.num x.den y.num y.den z.num z.den)
  add_comm a b := Quot.inductionOn a fun x => Quot.inductionOn b fun y => sound (by
    unfold RawRat.Equiv RawRat.add
    dsimp only
    rw [Int.add_comm (x.num * y.den), Int.mul_comm y.den x.den])
  zero_add a := Quot.inductionOn a fun x => sound (by
    unfold RawRat.Equiv RawRat.add RawRat.zero
    dsimp only
    simp)
  add_zero a := Quot.inductionOn a fun x => sound (by
    unfold RawRat.Equiv RawRat.add RawRat.zero
    dsimp only
    simp)
  neg_add_cancel a := Quot.inductionOn a fun x => sound (by
    unfold RawRat.Equiv RawRat.add RawRat.neg RawRat.zero
    dsimp only
    rw [Int.neg_mul]
    omega)
  sub_eq_add_neg _ _ := rfl
  mul_assoc a b c := Quot.inductionOn a fun x => Quot.inductionOn b fun y =>
    Quot.inductionOn c fun z => sound (by
      unfold RawRat.Equiv RawRat.mul
      dsimp only
      rw [Int.mul_assoc x.num y.num z.num, Int.mul_assoc x.den y.den z.den])
  mul_comm a b := Quot.inductionOn a fun x => Quot.inductionOn b fun y => sound (by
    unfold RawRat.Equiv RawRat.mul
    dsimp only
    rw [Int.mul_comm x.num y.num, Int.mul_comm y.den x.den])
  one_mul a := Quot.inductionOn a fun x => sound (by
    unfold RawRat.Equiv RawRat.mul RawRat.one
    dsimp only
    simp)
  mul_one a := Quot.inductionOn a fun x => sound (by
    unfold RawRat.Equiv RawRat.mul RawRat.one
    dsimp only
    simp)
  left_distrib a b c := Quot.inductionOn a fun x => Quot.inductionOn b fun y =>
    Quot.inductionOn c fun z => sound (int_ring_distrib x.num x.den y.num y.den z.num z.den)
  right_distrib a b c := Quot.inductionOn a fun x => Quot.inductionOn b fun y =>
    Quot.inductionOn c fun z => sound (by
      have h1 : mul (mk (RawRat.add x y)) (mk z) = mul (mk z) (mk (RawRat.add x y)) := sound (by
        unfold RawRat.Equiv RawRat.mul; dsimp only
        rw [Int.mul_comm _ z.num, Int.mul_comm z.den _])
      have h2 : mul (mk z) (mk (RawRat.add x y)) =
                add (mk (RawRat.mul z x)) (mk (RawRat.mul z y)) :=
        sound (int_ring_distrib z.num z.den x.num x.den y.num y.den)
      have h3 : RawRat.Equiv (RawRat.add (RawRat.mul z x) (RawRat.mul z y))
                             (RawRat.add (RawRat.mul x z) (RawRat.mul y z)) := by
        apply RawRat.add_congr
        · unfold RawRat.Equiv RawRat.mul; dsimp only
          rw [Int.mul_comm z.num x.num, Int.mul_comm x.den z.den]
        · unfold RawRat.Equiv RawRat.mul; dsimp only
          rw [Int.mul_comm z.num y.num, Int.mul_comm y.den z.den]
      exact exact_equiv ((h1.trans h2).trans (sound h3)))
  one_ne_zero h := by
    have heq : RawRat.Equiv RawRat.one RawRat.zero := exact_equiv h
    unfold RawRat.Equiv RawRat.one RawRat.zero at heq
    dsimp only at heq
    omega
  mul_inv_cancel {a} ha := Quot.inductionOn
    (motive := fun q => q ≠ zero → mul q (inv q) = one) a
    (fun x hax => by
      apply sound
      unfold RawRat.inv
      by_cases hpos : 0 < x.num
      · rw [dif_pos hpos]
        unfold RawRat.Equiv RawRat.mul RawRat.one
        dsimp only
        rw [Int.mul_one, Int.one_mul, Int.mul_comm]
      · rw [dif_neg hpos]
        by_cases hneg : x.num < 0
        · rw [dif_pos hneg]
          unfold RawRat.Equiv RawRat.mul RawRat.one
          dsimp only
          rw [Int.mul_one, Int.one_mul, Int.mul_neg, Int.mul_neg, Int.mul_comm]
        · exfalso
          apply hax
          apply sound
          unfold RawRat.Equiv RawRat.zero
          dsimp only
          omega) ha
  Pos := Pos
  one_pos := show 0 < RawRat.one.num by decide
  not_pos_zero := show ¬ (0 < RawRat.zero.num) by decide
  add_pos {a b} ha hb := Quot.inductionOn a (motive := fun q => Pos q → Pos (add q b))
    (fun x hx => Quot.inductionOn b (motive := fun r => Pos r → Pos (add (mk x) r))
      (fun y hy => Int.add_pos (Int.mul_pos hx y.den_pos) (Int.mul_pos hy x.den_pos)) hb) ha
  mul_pos {a b} ha hb := Quot.inductionOn a (motive := fun q => Pos q → Pos (mul q b))
    (fun x hx => Quot.inductionOn b (motive := fun r => Pos r → Pos (mul (mk x) r))
      (fun y hy => Int.mul_pos hx hy) hb) ha
  trichotomy a := Quot.inductionOn a fun x => by
    change (0 < x.num) ∨ (mk x = mk RawRat.zero) ∨ (0 < -x.num)
    by_cases hp : 0 < x.num
    · exact Or.inl hp
    · by_cases hz : x.num = 0
      · right; left
        apply sound
        unfold RawRat.Equiv RawRat.zero
        dsimp only
        omega
      · right; right; omega

end QRat

end Conjecture00000007622
