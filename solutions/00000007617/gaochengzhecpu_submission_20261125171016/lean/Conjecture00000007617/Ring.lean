/-
  Conjecture 00000007617 — Commutative Ring, Integral Domain, Exact Rationals,
  and Bezout Polynomial Identity Foundations
  Core Lean 4.19.0 only (zero external dependencies).
-/

namespace Conjecture00000007617

/-- Self-contained commutative ring typeclass for zero-dependency algebra. -/
class CRing (R : Type) where
  zero : R
  one : R
  add : R → R → R
  neg : R → R
  mul : R → R → R
  add_assoc : ∀ a b c : R, add (add a b) c = add a (add b c)
  add_comm : ∀ a b : R, add a b = add b a
  zero_add : ∀ a : R, add zero a = a
  add_left_neg : ∀ a : R, add (neg a) a = zero
  mul_assoc : ∀ a b c : R, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b : R, mul a b = mul b a
  one_mul : ∀ a : R, mul one a = a
  left_distrib : ∀ a b c : R, mul a (add b c) = add (mul a b) (mul a c)

namespace CRing

section BasicLemmas
variable {R : Type} [CRing R]

def sub (a b : R) : R := add a (neg b)

theorem add_zero (a : R) : add a zero = a := by
  rw [add_comm, zero_add]

theorem add_right_neg (a : R) : add a (neg a) = zero := by
  rw [add_comm, add_left_neg]

theorem mul_one (a : R) : mul a one = a := by
  rw [mul_comm, one_mul]

theorem right_distrib (a b c : R) : mul (add a b) c = add (mul a c) (mul b c) := by
  rw [mul_comm, left_distrib, mul_comm c a, mul_comm c b]

theorem add_left_cancel {a b c : R} (h : add a b = add a c) : b = c := by
  have h1 : add (neg a) (add a b) = add (neg a) (add a c) := congrArg (add (neg a)) h
  rw [← add_assoc, ← add_assoc, add_left_neg, zero_add, zero_add] at h1
  exact h1

theorem add_right_cancel {a b c : R} (h : add a c = add b c) : a = b := by
  apply add_left_cancel (a := c)
  rw [add_comm c a, add_comm c b]
  exact h

theorem mul_zero (a : R) : mul a zero = zero := by
  apply add_left_cancel (a := mul a zero)
  rw [← left_distrib, add_zero, add_zero]

theorem zero_mul (a : R) : mul zero a = zero := by
  rw [mul_comm, mul_zero]

theorem neg_eq_of_add_eq_zero {a b : R} (h : add a b = zero) : neg a = b := by
  apply add_left_cancel (a := a)
  rw [add_right_neg, h]

theorem neg_zero : neg (zero : R) = zero := by
  apply neg_eq_of_add_eq_zero
  exact zero_add zero

theorem neg_neg (a : R) : neg (neg a) = a := by
  apply neg_eq_of_add_eq_zero
  exact add_left_neg a

theorem neg_add (a b : R) : neg (add a b) = add (neg a) (neg b) := by
  apply neg_eq_of_add_eq_zero
  calc
    add (add a b) (add (neg a) (neg b))
      = add a (add b (add (neg b) (neg a))) := by
          rw [add_assoc, add_comm (neg a) (neg b)]
    _ = add a (add (add b (neg b)) (neg a)) := by rw [← add_assoc b]
    _ = add a (add zero (neg a)) := by rw [add_right_neg]
    _ = add a (neg a) := by rw [zero_add]
    _ = zero := add_right_neg a

theorem mul_neg (a b : R) : mul a (neg b) = neg (mul a b) := by
  apply Eq.symm
  apply neg_eq_of_add_eq_zero
  rw [← left_distrib, add_right_neg, mul_zero]

theorem neg_mul (a b : R) : mul (neg a) b = neg (mul a b) := by
  rw [mul_comm, mul_neg, mul_comm]

theorem neg_mul_neg (a b : R) : mul (neg a) (neg b) = mul a b := by
  rw [neg_mul, mul_neg, neg_neg]

theorem sub_self (a : R) : sub a a = zero :=
  add_right_neg a

theorem sub_eq_zero_iff {a b : R} : sub a b = zero ↔ a = b := by
  constructor
  · intro h
    have h1 : add (add a (neg b)) b = add zero b := congrArg (fun z => add z b) h
    rw [add_assoc, add_left_neg, add_zero, zero_add] at h1
    exact h1
  · intro h
    rw [h]
    exact sub_self b

theorem add_add_add_comm (a b c d : R) :
    add (add a b) (add c d) = add (add a c) (add b d) := by
  calc
    add (add a b) (add c d) = add a (add b (add c d)) := add_assoc a b (add c d)
    _ = add a (add (add b c) d) := by rw [← add_assoc b c d]
    _ = add a (add (add c b) d) := by rw [add_comm b c]
    _ = add a (add c (add b d)) := by rw [add_assoc c b d]
    _ = add (add a c) (add b d) := Eq.symm (add_assoc a c (add b d))

end BasicLemmas
end CRing

/-- Integral domain extension of `CRing`. -/
class IDomain (R : Type) extends CRing R where
  one_ne_zero : CRing.one ≠ (CRing.zero : R)
  mul_eq_zero : ∀ {a b : R}, CRing.mul a b = CRing.zero → a = CRing.zero ∨ b = CRing.zero

/-! ### `Int` as a `CRing` and `IDomain` -/

instance : CRing Int where
  zero := 0
  one := 1
  add := (· + ·)
  neg := (- ·)
  mul := (· * ·)
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  zero_add := Int.zero_add
  add_left_neg := fun _ => by omega
  mul_assoc := Int.mul_assoc
  mul_comm := Int.mul_comm
  one_mul := Int.one_mul
  left_distrib := Int.mul_add

theorem int_mul_eq_zero {a b : Int} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    by_cases hb : b = 0
    · exact hb
    · exfalso
      by_cases ha_pos : 0 < a
      · by_cases hb_pos : 0 < b
        · have hp : 0 < a * b := Int.mul_pos ha_pos hb_pos
          omega
        · have hb_neg : 0 < -b := by omega
          have hp : 0 < a * (-b) := Int.mul_pos ha_pos hb_neg
          have heq : a * (-b) = -(a * b) := Int.mul_neg a b
          omega
      · have ha_neg : 0 < -a := by omega
        by_cases hb_pos : 0 < b
        · have hp : 0 < (-a) * b := Int.mul_pos ha_neg hb_pos
          have heq : (-a) * b = -(a * b) := Int.neg_mul a b
          omega
        · have hb_neg : 0 < -b := by omega
          have hp : 0 < (-a) * (-b) := Int.mul_pos ha_neg hb_neg
          have heq : (-a) * (-b) = a * b := by
            rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
          omega

theorem int_mul_right_cancel {a b c : Int} (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  have hd : (a + -b) * c = 0 := by
    rw [Int.add_mul, Int.neg_mul, h]
    omega
  cases int_mul_eq_zero hd with
  | inl hab => omega
  | inr hcz => exact absurd hcz hc

instance : IDomain Int where
  one_ne_zero := by decide
  mul_eq_zero := int_mul_eq_zero

/-! ### Self-Contained Exact Rationals `QRat` as `CRing` and `IDomain` -/

structure RawRat where
  num : Int
  den : Nat
  denPos : 0 < den

namespace RawRat

def denInt (r : RawRat) : Int := (r.den : Int)

theorem denInt_pos (r : RawRat) : 0 < r.denInt := by
  unfold denInt
  have h := r.denPos
  omega

theorem denInt_ne_zero (r : RawRat) : r.denInt ≠ 0 := by
  have h := denInt_pos r
  omega

def Rel (a b : RawRat) : Prop :=
  a.num * b.denInt = b.num * a.denInt

theorem rel_refl (a : RawRat) : Rel a a := rfl

theorem rel_symm {a b : RawRat} (h : Rel a b) : Rel b a := Eq.symm h

theorem rel_trans {a b c : RawRat} (hab : Rel a b) (hbc : Rel b c) : Rel a c := by
  unfold Rel at *
  apply int_mul_right_cancel (denInt_ne_zero b)
  calc
    (a.num * c.denInt) * b.denInt
      = (a.num * b.denInt) * c.denInt := by
          rw [Int.mul_assoc, Int.mul_comm c.denInt b.denInt, ← Int.mul_assoc]
    _ = (b.num * a.denInt) * c.denInt := by rw [hab]
    _ = (b.num * c.denInt) * a.denInt := by
          rw [Int.mul_assoc, Int.mul_comm a.denInt c.denInt, ← Int.mul_assoc]
    _ = (c.num * b.denInt) * a.denInt := by rw [hbc]
    _ = (c.num * a.denInt) * b.denInt := by
          rw [Int.mul_assoc, Int.mul_comm b.denInt a.denInt, ← Int.mul_assoc]

def add (a b : RawRat) : RawRat where
  num := a.num * b.denInt + b.num * a.denInt
  den := a.den * b.den
  denPos := Nat.mul_pos a.denPos b.denPos

def neg (a : RawRat) : RawRat where
  num := -a.num
  den := a.den
  denPos := a.denPos

def mul (a b : RawRat) : RawRat where
  num := a.num * b.num
  den := a.den * b.den
  denPos := Nat.mul_pos a.denPos b.denPos

theorem add_denInt (a b : RawRat) : (add a b).denInt = a.denInt * b.denInt :=
  Int.natCast_mul a.den b.den

theorem mul_denInt (a b : RawRat) : (mul a b).denInt = a.denInt * b.denInt :=
  Int.natCast_mul a.den b.den

private theorem mul4_swap23 (w x y z : Int) : (w * x) * (y * z) = (w * y) * (x * z) := by
  calc
    (w * x) * (y * z) = w * (x * (y * z)) := Int.mul_assoc w x (y * z)
    _ = w * ((x * y) * z) := by rw [← Int.mul_assoc x y z]
    _ = w * ((y * x) * z) := by rw [Int.mul_comm x y]
    _ = w * (y * (x * z)) := by rw [Int.mul_assoc y x z]
    _ = (w * y) * (x * z) := Eq.symm (Int.mul_assoc w y (x * z))

theorem add_congr {a1 a2 b1 b2 : RawRat} (ha : Rel a1 a2) (hb : Rel b1 b2) :
    Rel (add a1 b1) (add a2 b2) := by
  unfold Rel at *
  rw [add_denInt, add_denInt]
  simp only [add]
  rw [Int.add_mul, Int.add_mul]
  have h1 : (a1.num * b1.denInt) * (a2.denInt * b2.denInt) =
      (a2.num * b2.denInt) * (a1.denInt * b1.denInt) := by
    calc
      (a1.num * b1.denInt) * (a2.denInt * b2.denInt)
        = (a1.num * a2.denInt) * (b1.denInt * b2.denInt) := mul4_swap23 _ _ _ _
      _ = (a2.num * a1.denInt) * (b2.denInt * b1.denInt) := by
          rw [ha, Int.mul_comm b1.denInt b2.denInt]
      _ = (a2.num * b2.denInt) * (a1.denInt * b1.denInt) := mul4_swap23 _ _ _ _
  have h2 : (b1.num * a1.denInt) * (a2.denInt * b2.denInt) =
      (b2.num * a2.denInt) * (a1.denInt * b1.denInt) := by
    calc
      (b1.num * a1.denInt) * (a2.denInt * b2.denInt)
        = (b1.num * a1.denInt) * (b2.denInt * a2.denInt) := by rw [Int.mul_comm a2.denInt b2.denInt]
      _ = (b1.num * b2.denInt) * (a1.denInt * a2.denInt) := mul4_swap23 _ _ _ _
      _ = (b2.num * b1.denInt) * (a2.denInt * a1.denInt) := by
          rw [hb, Int.mul_comm a1.denInt a2.denInt]
      _ = (b2.num * a2.denInt) * (b1.denInt * a1.denInt) := mul4_swap23 _ _ _ _
      _ = (b2.num * a2.denInt) * (a1.denInt * b1.denInt) := by rw [Int.mul_comm b1.denInt a1.denInt]
  rw [h1, h2]

theorem neg_congr {a1 a2 : RawRat} (ha : Rel a1 a2) : Rel (neg a1) (neg a2) := by
  unfold Rel neg at *
  simp only [denInt] at *
  rw [Int.neg_mul, Int.neg_mul, ha]

theorem mul_congr {a1 a2 b1 b2 : RawRat} (ha : Rel a1 a2) (hb : Rel b1 b2) :
    Rel (mul a1 b1) (mul a2 b2) := by
  unfold Rel at *
  rw [mul_denInt, mul_denInt]
  simp only [mul]
  calc
    (a1.num * b1.num) * (a2.denInt * b2.denInt)
      = (a1.num * a2.denInt) * (b1.num * b2.denInt) := mul4_swap23 _ _ _ _
    _ = (a2.num * a1.denInt) * (b2.num * b1.denInt) := by rw [ha, hb]
    _ = (a2.num * b2.num) * (a1.denInt * b1.denInt) := mul4_swap23 _ _ _ _

end RawRat

/-- Exact rational number type `ℚ` constructed directly via `Quot`. -/
def QRat : Type := Quot RawRat.Rel

namespace QRat

def mk (num : Int) (den : Nat) (h : 0 < den) : QRat :=
  Quot.mk RawRat.Rel ⟨num, den, h⟩

def ofInt (n : Int) : QRat :=
  mk n 1 (by decide)

def zero : QRat := ofInt 0
def one : QRat := ofInt 1

def add : QRat → QRat → QRat :=
  fun x y =>
    Quot.lift
      (fun a =>
        Quot.lift (fun b => Quot.mk RawRat.Rel (RawRat.add a b))
          (fun _ _ hb => Quot.sound (RawRat.add_congr (RawRat.rel_refl a) hb)) y)
      (fun a1 a2 ha => by
        refine Quot.inductionOn y (fun b => ?_)
        exact Quot.sound (RawRat.add_congr ha (RawRat.rel_refl b)))
      x

def neg : QRat → QRat :=
  Quot.lift (fun a => Quot.mk RawRat.Rel (RawRat.neg a))
    (fun _ _ ha => Quot.sound (RawRat.neg_congr ha))

def mul : QRat → QRat → QRat :=
  fun x y =>
    Quot.lift
      (fun a =>
        Quot.lift (fun b => Quot.mk RawRat.Rel (RawRat.mul a b))
          (fun _ _ hb => Quot.sound (RawRat.mul_congr (RawRat.rel_refl a) hb)) y)
      (fun a1 a2 ha => by
        refine Quot.inductionOn y (fun b => ?_)
        exact Quot.sound (RawRat.mul_congr ha (RawRat.rel_refl b)))
      x

/-- Decidable Boolean cross-multiplication test `x = p / q` (`q > 0`). -/
def eqFracBool (p : Int) (q : Int) : QRat → Bool :=
  Quot.lift (fun r => decide (r.num * q = p * r.denInt)) (by
    intro a b hab
    unfold RawRat.Rel at hab
    have hiff : (a.num * q = p * a.denInt) ↔ (b.num * q = p * b.denInt) := by
      constructor
      · intro ha
        apply int_mul_right_cancel (RawRat.denInt_ne_zero a)
        calc
          (b.num * q) * a.denInt = (b.num * a.denInt) * q := by
            rw [Int.mul_assoc, Int.mul_comm q a.denInt, ← Int.mul_assoc]
          _ = (a.num * b.denInt) * q := by rw [← hab]
          _ = (a.num * q) * b.denInt := by
            rw [Int.mul_assoc, Int.mul_comm b.denInt q, ← Int.mul_assoc]
          _ = (p * a.denInt) * b.denInt := by rw [ha]
          _ = (p * b.denInt) * a.denInt := by
            rw [Int.mul_assoc, Int.mul_comm a.denInt b.denInt, ← Int.mul_assoc]
      · intro hb
        apply int_mul_right_cancel (RawRat.denInt_ne_zero b)
        calc
          (a.num * q) * b.denInt = (a.num * b.denInt) * q := by
            rw [Int.mul_assoc, Int.mul_comm q b.denInt, ← Int.mul_assoc]
          _ = (b.num * a.denInt) * q := by rw [hab]
          _ = (b.num * q) * a.denInt := by
            rw [Int.mul_assoc, Int.mul_comm a.denInt q, ← Int.mul_assoc]
          _ = (p * b.denInt) * a.denInt := by rw [hb]
          _ = (p * a.denInt) * b.denInt := by
            rw [Int.mul_assoc, Int.mul_comm b.denInt a.denInt, ← Int.mul_assoc]
    by_cases h1 : a.num * q = p * a.denInt
    · have h2 : b.num * q = p * b.denInt := hiff.mp h1
      simp [h1, h2]
    · have h2 : ¬ (b.num * q = p * b.denInt) := fun hb => h1 (hiff.mpr hb)
      simp [h1, h2])

theorem ne_of_eqFracBool_diff {x y : QRat} (p q : Int)
    (h : eqFracBool p q x ≠ eqFracBool p q y) : x ≠ y := by
  intro heq
  rw [heq] at h
  exact h rfl

theorem eq_zero_iff (r : RawRat) : Quot.mk RawRat.Rel r = zero ↔ r.num = 0 := by
  constructor
  · intro h
    have hz : eqFracBool 0 1 (Quot.mk RawRat.Rel r) = eqFracBool 0 1 zero :=
      congrArg (eqFracBool 0 1) h
    have hz' : decide (r.num * 1 = 0 * r.denInt) = true := hz
    have hprop : r.num * 1 = 0 * r.denInt := of_decide_eq_true hz'
    omega
  · intro hn
    apply Quot.sound
    unfold RawRat.Rel
    change r.num * 1 = 0 * r.denInt
    omega

private theorem add_assoc_thm (a b c : QRat) : add (add a b) c = add a (add b c) := by
  refine Quot.inductionOn a (fun ra => Quot.inductionOn b (fun rb => Quot.inductionOn c (fun rc => ?_)))
  change Quot.mk RawRat.Rel (RawRat.add (RawRat.add ra rb) rc) =
    Quot.mk RawRat.Rel (RawRat.add ra (RawRat.add rb rc))
  apply Quot.sound
  unfold RawRat.Rel
  simp only [RawRat.add, RawRat.denInt, Int.natCast_mul]
  rw [Int.add_mul, Int.add_mul, Int.add_mul, Int.add_mul, Int.add_mul, Int.add_mul]
  have t1 :
      ra.num * ↑rb.den * ↑rc.den * (↑ra.den * (↑rb.den * ↑rc.den)) =
      ra.num * (↑rb.den * ↑rc.den) * (↑ra.den * ↑rb.den * ↑rc.den) := by
    simp only [Int.mul_assoc]
  have t2 :
      rb.num * ↑ra.den * ↑rc.den * (↑ra.den * (↑rb.den * ↑rc.den)) =
      rb.num * ↑rc.den * ↑ra.den * (↑ra.den * ↑rb.den * ↑rc.den) := by
    rw [Int.mul_assoc rb.num (↑ra.den) (↑rc.den), Int.mul_comm (↑ra.den) (↑rc.den),
        ← Int.mul_assoc rb.num (↑rc.den) (↑ra.den)]
    simp only [Int.mul_assoc]
  have t3 :
      rc.num * (↑ra.den * ↑rb.den) * (↑ra.den * (↑rb.den * ↑rc.den)) =
      rc.num * ↑rb.den * ↑ra.den * (↑ra.den * ↑rb.den * ↑rc.den) := by
    have hswap : rc.num * (↑ra.den * ↑rb.den) = rc.num * ↑rb.den * ↑ra.den := by
      rw [Int.mul_comm (↑ra.den) (↑rb.den), Int.mul_assoc]
    rw [hswap, Int.mul_assoc (↑ra.den) (↑rb.den) (↑rc.den)]
  rw [t1, t2, t3, Int.add_assoc]

private theorem add_comm_thm (a b : QRat) : add a b = add b a := by
  refine Quot.inductionOn a (fun ra => Quot.inductionOn b (fun rb => ?_))
  change Quot.mk RawRat.Rel (RawRat.add ra rb) = Quot.mk RawRat.Rel (RawRat.add rb ra)
  apply Quot.sound
  unfold RawRat.Rel
  rw [RawRat.add_denInt, RawRat.add_denInt]
  simp only [RawRat.add]
  rw [Int.add_comm (ra.num * rb.denInt), Int.mul_comm ra.denInt rb.denInt]

private theorem zero_add_thm (a : QRat) : add zero a = a := by
  refine Quot.inductionOn a (fun ra => ?_)
  change Quot.mk RawRat.Rel (RawRat.add ⟨0, 1, _⟩ ra) = Quot.mk RawRat.Rel ra
  apply Quot.sound
  unfold RawRat.Rel
  simp only [RawRat.add, RawRat.denInt, Int.natCast_mul]
  have h1 : ((1 : Nat) : Int) = 1 := rfl
  rw [h1, Int.zero_mul, Int.zero_add, Int.mul_one, Int.one_mul]

private theorem add_left_neg_thm (a : QRat) : add (neg a) a = zero := by
  refine Quot.inductionOn a (fun ra => ?_)
  change Quot.mk RawRat.Rel (RawRat.add (RawRat.neg ra) ra) = Quot.mk RawRat.Rel ⟨0, 1, _⟩
  apply Quot.sound
  unfold RawRat.Rel
  simp only [RawRat.add, RawRat.neg, RawRat.denInt, Int.natCast_mul]
  rw [Int.neg_mul]
  omega

private theorem mul_assoc_thm (a b c : QRat) : mul (mul a b) c = mul a (mul b c) := by
  refine Quot.inductionOn a (fun ra => Quot.inductionOn b (fun rb => Quot.inductionOn c (fun rc => ?_)))
  change Quot.mk RawRat.Rel (RawRat.mul (RawRat.mul ra rb) rc) =
    Quot.mk RawRat.Rel (RawRat.mul ra (RawRat.mul rb rc))
  apply Quot.sound
  unfold RawRat.Rel
  simp only [RawRat.mul, RawRat.denInt, Int.natCast_mul, Int.mul_assoc]

private theorem mul_comm_thm (a b : QRat) : mul a b = mul b a := by
  refine Quot.inductionOn a (fun ra => Quot.inductionOn b (fun rb => ?_))
  change Quot.mk RawRat.Rel (RawRat.mul ra rb) = Quot.mk RawRat.Rel (RawRat.mul rb ra)
  apply Quot.sound
  unfold RawRat.Rel
  rw [RawRat.mul_denInt, RawRat.mul_denInt]
  simp only [RawRat.mul]
  rw [Int.mul_comm ra.num rb.num, Int.mul_comm ra.denInt rb.denInt]

private theorem one_mul_thm (a : QRat) : mul one a = a := by
  refine Quot.inductionOn a (fun ra => ?_)
  change Quot.mk RawRat.Rel (RawRat.mul ⟨1, 1, _⟩ ra) = Quot.mk RawRat.Rel ra
  apply Quot.sound
  unfold RawRat.Rel
  simp only [RawRat.mul, RawRat.denInt, Int.natCast_mul]
  have h1 : ((1 : Nat) : Int) = 1 := rfl
  rw [h1, Int.one_mul, Int.one_mul]

private theorem left_distrib_thm (a b c : QRat) :
    mul a (add b c) = add (mul a b) (mul a c) := by
  refine Quot.inductionOn a (fun ra => Quot.inductionOn b (fun rb => Quot.inductionOn c (fun rc => ?_)))
  change Quot.mk RawRat.Rel (RawRat.mul ra (RawRat.add rb rc)) =
    Quot.mk RawRat.Rel (RawRat.add (RawRat.mul ra rb) (RawRat.mul ra rc))
  apply Quot.sound
  unfold RawRat.Rel
  simp only [RawRat.mul, RawRat.add, RawRat.denInt, Int.natCast_mul]
  calc
    ra.num * (rb.num * ↑rc.den + rc.num * ↑rb.den) * (↑ra.den * ↑rb.den * (↑ra.den * ↑rc.den))
      = (ra.num * rb.num * ↑rc.den + ra.num * rc.num * ↑rb.den) *
          (↑ra.den * (↑ra.den * (↑rb.den * ↑rc.den))) := by
          rw [Int.mul_add]
          congr 1
          · simp only [Int.mul_assoc]
          · simp only [Int.mul_assoc]
            congr 1
            rw [← Int.mul_assoc (↑rb.den), Int.mul_comm (↑rb.den) (↑ra.den), Int.mul_assoc (↑ra.den)]
    _ = (ra.num * rb.num * (↑ra.den * ↑rc.den) + ra.num * rc.num * (↑ra.den * ↑rb.den)) *
          (↑ra.den * (↑rb.den * ↑rc.den)) := by
          rw [Int.add_mul, Int.add_mul]
          congr 1
          · simp only [Int.mul_assoc]
            congr 2
            rw [← Int.mul_assoc (↑rc.den), Int.mul_comm (↑rc.den) (↑ra.den), Int.mul_assoc (↑ra.den)]
          · simp only [Int.mul_assoc]
            congr 2
            rw [← Int.mul_assoc (↑rb.den), Int.mul_comm (↑rb.den) (↑ra.den), Int.mul_assoc (↑ra.den)]

instance : CRing QRat where
  zero := zero
  one := one
  add := add
  neg := neg
  mul := mul
  add_assoc := add_assoc_thm
  add_comm := add_comm_thm
  zero_add := zero_add_thm
  add_left_neg := add_left_neg_thm
  mul_assoc := mul_assoc_thm
  mul_comm := mul_comm_thm
  one_mul := one_mul_thm
  left_distrib := left_distrib_thm

instance : IDomain QRat where
  one_ne_zero := by
    apply ne_of_eqFracBool_diff 0 1
    decide
  mul_eq_zero := by
    intro a b
    refine Quot.inductionOn a (fun ra => Quot.inductionOn b (fun rb => ?_))
    intro h
    have h' : Quot.mk RawRat.Rel (RawRat.mul ra rb) = zero := h
    have hz : (RawRat.mul ra rb).num = 0 := (eq_zero_iff (RawRat.mul ra rb)).mp h'
    simp only [RawRat.mul] at hz
    cases int_mul_eq_zero hz with
    | inl ha0 => exact Or.inl ((eq_zero_iff ra).mpr ha0)
    | inr hb0 => exact Or.inr ((eq_zero_iff rb).mpr hb0)

end QRat

/-! ### Univariate Polynomials & Bezout Synthetic Root Counting over Integral Domains -/

/-- Horner evaluation of a polynomial `a_0 + a_1 t + ... + a_d t^d` represented as `List R`. -/
def evalPoly {R : Type} [CRing R] : List R → R → R
  | [], _ => CRing.zero
  | a :: p, t => CRing.add a (CRing.mul t (evalPoly p t))

/-- Bezout synthetic division of `P(t) - P(r)` by `(t - r)`. -/
def polyDivRoot {R : Type} [CRing R] : List R → R → List R
  | [], _ => []
  | [_], _ => []
  | _ :: b :: q, r => evalPoly (b :: q) r :: polyDivRoot (b :: q) r

theorem polyDivRoot_length_succ {R : Type} [CRing R] :
    ∀ (a : R) (p : List R) (r : R), (polyDivRoot (a :: p) r).length + 1 = (a :: p).length
  | _, [], _ => rfl
  | a, b :: q, r => by
      have ih := polyDivRoot_length_succ b q r
      have h1 : (polyDivRoot (a :: b :: q) r).length = (polyDivRoot (b :: q) r).length + 1 := rfl
      have h2 : (a :: b :: q).length = (b :: q).length + 1 := rfl
      omega

theorem evalPoly_sub_eq_mul_div {R : Type} [CRing R] :
    ∀ (p : List R) (t r : R),
      CRing.sub (evalPoly p t) (evalPoly p r) =
        CRing.mul (CRing.sub t r) (evalPoly (polyDivRoot p r) t)
  | [], t, r => by
      simp [evalPoly, polyDivRoot, CRing.sub_self, CRing.mul_zero]
  | [a], t, r => by
      simp [evalPoly, polyDivRoot, CRing.mul_zero, CRing.add_zero, CRing.sub_self]
  | a :: b :: q, t, r => by
      have ih := evalPoly_sub_eq_mul_div (b :: q) t r
      let ft := evalPoly (b :: q) t
      let fr := evalPoly (b :: q) r
      let qt := evalPoly (polyDivRoot (b :: q) r) t
      have hft : ft = CRing.add fr (CRing.mul (CRing.sub t r) qt) := by
        have h1 : CRing.add (CRing.sub ft fr) fr =
            CRing.add (CRing.mul (CRing.sub t r) qt) fr :=
          congrArg (fun z => CRing.add z fr) ih
        unfold CRing.sub at h1
        rw [CRing.add_assoc ft (CRing.neg fr) fr, CRing.add_left_neg, CRing.add_zero,
            CRing.add_comm _ fr] at h1
        exact h1
      change CRing.sub (CRing.add a (CRing.mul t ft)) (CRing.add a (CRing.mul r fr)) =
        CRing.mul (CRing.sub t r) (CRing.add fr (CRing.mul t qt))
      calc
        CRing.sub (CRing.add a (CRing.mul t ft)) (CRing.add a (CRing.mul r fr))
          = CRing.sub (CRing.mul t ft) (CRing.mul r fr) := by
              unfold CRing.sub
              rw [CRing.neg_add, CRing.add_comm a (CRing.mul t ft),
                  CRing.add_assoc (CRing.mul t ft) a,
                  ← CRing.add_assoc a (CRing.neg a), CRing.add_right_neg, CRing.zero_add]
        _ = CRing.sub (CRing.mul t (CRing.add fr (CRing.mul (CRing.sub t r) qt))) (CRing.mul r fr) := by
              rw [hft]
        _ = CRing.add (CRing.sub (CRing.mul t fr) (CRing.mul r fr))
              (CRing.mul t (CRing.mul (CRing.sub t r) qt)) := by
              rw [CRing.left_distrib]
              unfold CRing.sub
              rw [CRing.add_assoc, CRing.add_comm (CRing.mul t (CRing.mul _ qt)) (CRing.neg _),
                  ← CRing.add_assoc]
        _ = CRing.add (CRing.mul (CRing.sub t r) fr)
              (CRing.mul (CRing.sub t r) (CRing.mul t qt)) := by
              have hsub : CRing.sub (CRing.mul t fr) (CRing.mul r fr) =
                  CRing.mul (CRing.sub t r) fr := by
                unfold CRing.sub
                rw [CRing.right_distrib, CRing.neg_mul]
              rw [hsub, ← CRing.mul_assoc t, CRing.mul_comm t (CRing.sub t r), CRing.mul_assoc]
        _ = CRing.mul (CRing.sub t r) (CRing.add fr (CRing.mul t qt)) :=
              Eq.symm (CRing.left_distrib _ _ _)

/-- Pairwise distinctness of a list of evaluation points. -/
def PairwiseNe {α : Type} : List α → Prop
  | [] => True
  | r :: rs => (∀ s, s ∈ rs → s ≠ r) ∧ PairwiseNe rs

/-- Over any integral domain, a polynomial of coefficient length `≤ roots.length`
    vanishing on pairwise distinct `roots` vanishes identically at every `t : R`. -/
theorem evalPoly_eq_zero_of_roots {R : Type} [IDomain R] :
    ∀ (roots : List R) (p : List R),
      PairwiseNe roots →
      p.length ≤ roots.length →
      (∀ s, s ∈ roots → evalPoly p s = CRing.zero) →
      ∀ t : R, evalPoly p t = CRing.zero
  | [], p, _, hlen, _, _ => by
      cases p with
      | nil => rfl
      | cons a q =>
          have hc : (a :: q).length = q.length + 1 := rfl
          have hn : ([] : List R).length = 0 := rfl
          omega
  | _ :: _, [], _, _, _, _ => rfl
  | r :: rs, a :: q, hnd, hlen, hroots, t => by
      let p' := polyDivRoot (a :: q) r
      have hp_len : p'.length + 1 = (a :: q).length := polyDivRoot_length_succ a q r
      have hlen_aq : (a :: q).length = q.length + 1 := rfl
      have hlen_rrs : (r :: rs).length = rs.length + 1 := rfl
      have hlen' : p'.length ≤ rs.length := by omega
      have hr0 : evalPoly (a :: q) r = CRing.zero :=
        hroots r (List.Mem.head rs)
      have hroots' : ∀ s, s ∈ rs → evalPoly p' s = CRing.zero := by
        intro s hs
        have hs0 : evalPoly (a :: q) s = CRing.zero :=
          hroots s (List.Mem.tail r hs)
        have hdiv := evalPoly_sub_eq_mul_div (a :: q) s r
        rw [hs0, hr0, CRing.sub_self] at hdiv
        have hsr_ne : CRing.sub s r ≠ CRing.zero := by
          intro hzero
          exact hnd.1 s hs (CRing.sub_eq_zero_iff.mp hzero)
        cases IDomain.mul_eq_zero (Eq.symm hdiv) with
        | inl hbad => exact absurd hbad hsr_ne
        | inr hok => exact hok
      have hq_zero : evalPoly p' t = CRing.zero :=
        evalPoly_eq_zero_of_roots rs p' hnd.2 hlen' hroots' t
      have hdiv_t := evalPoly_sub_eq_mul_div (a :: q) t r
      rw [hr0, hq_zero, CRing.mul_zero] at hdiv_t
      exact CRing.sub_eq_zero_iff.mp hdiv_t

end Conjecture00000007617
