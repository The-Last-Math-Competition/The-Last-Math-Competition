/-
  CliffordDecomp/RatQ.lean
  Self-contained construction of CommRing2 (commutative rings with 1/2) and the exact
  field of rational numbers RatQ in Core Lean 4.19.0 with zero external dependencies.
-/

namespace CliffordDecomp

/-- Typeclass for `1` so `CommRing2` can extend `Zero K` and `One K` cleanly. -/
class One (K : Type u) where
  one : K

instance [One K] : OfNat K 1 where
  ofNat := One.one

/-- A commutative ring in which `2 = 1 + 1` has a multiplicative inverse `half`.
    Every field of characteristic ≠ 2 (in particular ℚ and ℝ) satisfies `CommRing2`. -/
class CommRing2 (K : Type u)
    extends Add K, Sub K, Neg K, Mul K, Zero K, One K where
  half : K
  add_assoc : ∀ a b c : K, a + b + c = a + (b + c)
  add_comm : ∀ a b : K, a + b = b + a
  zero_add : ∀ a : K, 0 + a = a
  add_zero : ∀ a : K, a + 0 = a
  neg_add_cancel : ∀ a : K, -a + a = 0
  sub_eq_add_neg : ∀ a b : K, a - b = a + -b
  mul_assoc : ∀ a b c : K, a * b * c = a * (b * c)
  mul_comm : ∀ a b : K, a * b = b * a
  one_mul : ∀ a : K, 1 * a = a
  mul_one : ∀ a : K, a * 1 = a
  left_distrib : ∀ a b c : K, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : K, (a + b) * c = a * c + b * c
  two_mul_half : ((1 : K) + 1) * half = 1

namespace CommRing2

section BasicLemmas
variable {K : Type u} [CommRing2 K]

def two : K := (1 : K) + 1

theorem add_left_comm (a b c : K) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, add_comm a b, add_assoc]

theorem mul_left_comm (a b c : K) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm a b, mul_assoc]

theorem add_neg_cancel (a : K) : a + -a = 0 := by
  rw [add_comm, neg_add_cancel]

theorem add_left_cancel {a b c : K} (h : a + b = a + c) : b = c := by
  have h1 : -a + (a + b) = -a + (a + c) := congrArg (-a + ·) h
  rw [← add_assoc, neg_add_cancel, zero_add, ← add_assoc, neg_add_cancel, zero_add] at h1
  exact h1

theorem add_right_cancel {a b c : K} (h : a + c = b + c) : a = b := by
  apply add_left_cancel (a := c)
  rw [add_comm c a, add_comm c b]
  exact h

theorem zero_mul (a : K) : (0 : K) * a = 0 := by
  apply add_left_cancel (a := (0 : K) * a)
  rw [← right_distrib, add_zero, add_zero]

theorem mul_zero (a : K) : a * (0 : K) = 0 := by
  rw [mul_comm, zero_mul]

theorem neg_zero : -(0 : K) = 0 := by
  apply add_left_cancel (a := (0 : K))
  rw [add_neg_cancel, add_zero]

theorem neg_neg (a : K) : -(-a) = a := by
  apply add_left_cancel (a := -a)
  rw [add_neg_cancel, neg_add_cancel]

theorem neg_eq_neg_one_mul (a : K) : -a = (-1 : K) * a := by
  apply add_left_cancel (a := a)
  rw [add_neg_cancel]
  have h : a + -(1 : K) * a = ((1 : K) + -(1 : K)) * a := by
    rw [right_distrib, one_mul]
  rw [h, add_neg_cancel, zero_mul]

theorem neg_mul (a b : K) : (-a) * b = -(a * b) := by
  apply add_left_cancel (a := a * b)
  rw [add_neg_cancel, ← right_distrib, add_neg_cancel, zero_mul]

theorem mul_neg (a b : K) : a * (-b) = -(a * b) := by
  rw [mul_comm, neg_mul, mul_comm]

theorem neg_mul_neg (a b : K) : (-a) * (-b) = a * b := by
  rw [neg_mul, mul_neg, neg_neg]

theorem neg_add (a b : K) : -(a + b) = -a + -b := by
  apply add_left_cancel (a := a + b)
  rw [add_neg_cancel]
  symm
  calc
    a + b + (-a + -b) = a + (b + (-b + -a)) := by
      rw [add_comm (-a) (-b), add_assoc]
    _ = a + (0 + -a) := by rw [← add_assoc b (-b) (-a), add_neg_cancel]
    _ = a + -a := by rw [zero_add]
    _ = 0 := add_neg_cancel a

theorem sub_self (a : K) : a - a = 0 := by
  rw [sub_eq_add_neg, add_neg_cancel]

theorem sub_zero (a : K) : a - (0 : K) = a := by
  rw [sub_eq_add_neg, neg_zero, add_zero]

theorem zero_sub (a : K) : (0 : K) - a = -a := by
  rw [sub_eq_add_neg, zero_add]

theorem neg_sub (a b : K) : -(a - b) = b - a := by
  rw [sub_eq_add_neg, neg_add, neg_neg, add_comm, ← sub_eq_add_neg]

theorem mul_sub (a b c : K) : a * (b - c) = a * b - a * c := by
  rw [sub_eq_add_neg, left_distrib, mul_neg, ← sub_eq_add_neg]

theorem sub_mul (a b c : K) : (a - b) * c = a * c - b * c := by
  rw [sub_eq_add_neg, right_distrib, neg_mul, ← sub_eq_add_neg]

theorem half_mul_two : (half : K) * ((1 : K) + 1) = 1 := by
  rw [mul_comm, two_mul_half]

theorem half_add_half : (half : K) + half = 1 := by
  calc
    (half : K) + half = (1 : K) * half + (1 : K) * half := by rw [one_mul]
    _ = ((1 : K) + 1) * half := by rw [← right_distrib]
    _ = 1 := two_mul_half

theorem mul_two (a : K) : a * ((1 : K) + 1) = a + a := by
  rw [left_distrib, mul_one]

theorem two_mul (a : K) : ((1 : K) + 1) * a = a + a := by
  rw [right_distrib, one_mul]

theorem half_mul_add_self (a : K) : (half : K) * (a + a) = a := by
  rw [← two_mul, ← mul_assoc, half_mul_two, one_mul]

theorem eq_zero_of_add_self_eq_zero {a : K} (h : a + a = 0) : a = 0 := by
  have h1 : (half : K) * (a + a) = (half : K) * 0 := congrArg (half * ·) h
  rw [half_mul_add_self, mul_zero] at h1
  exact h1

/-- Sign `(-1)^m` in `K`. -/
def signPow (K : Type u) [CommRing2 K] : Nat → K
  | 0 => 1
  | m + 1 => -(signPow K m)

theorem signPow_add (a b : Nat) : signPow K (a + b) = signPow K a * signPow K b := by
  induction b with
  | zero =>
    simp [signPow, mul_one]
  | succ b ih =>
    rw [Nat.add_succ]
    simp only [signPow]
    rw [ih, mul_neg]

theorem signPow_sq (m : Nat) : signPow K m * signPow K m = 1 := by
  induction m with
  | zero =>
    simp [signPow, one_mul]
  | succ m ih =>
    simp only [signPow]
    rw [neg_mul_neg, ih]

theorem signPow_even (k : Nat) : signPow K (2 * k) = 1 := by
  induction k with
  | zero =>
    simp [signPow]
  | succ k ih =>
    have h : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h]
    simp only [signPow, neg_neg]
    exact ih

theorem signPow_odd (k : Nat) : signPow K (2 * k + 1) = -(1 : K) := by
  rw [signPow_add, signPow_even, one_mul]
  rfl

end BasicLemmas
end CommRing2

/-! ### Exact Field of Rational Numbers `RatQ` -/

/-- Unreduced fraction `num / den` with `den > 0`. -/
structure RawRat where
  num : Int
  den : Nat
  den_pos : 0 < den
  deriving DecidableEq

namespace RawRat

private theorem int_mul_left_comm (a b c : Int) : a * (b * c) = b * (a * c) := by
  rw [← Int.mul_assoc, Int.mul_comm a b, Int.mul_assoc]

def Equiv (a b : RawRat) : Prop :=
  a.num * (b.den : Int) = b.num * (a.den : Int)

theorem den_int_pos (a : RawRat) : (0 : Int) < (a.den : Int) :=
  Int.ofNat_lt.mpr a.den_pos

theorem den_int_ne_zero (a : RawRat) : (a.den : Int) ≠ 0 := by
  have h := den_int_pos a
  omega

theorem equiv_refl (a : RawRat) : Equiv a a := rfl

theorem equiv_symm {a b : RawRat} (h : Equiv a b) : Equiv b a := h.symm

private theorem int_mul_cancel_right {x y z : Int} (hz : z ≠ 0) (h : x * z = y * z) : x = y := by
  have hdiff : (x - y) * z = 0 := by
    rw [Int.sub_mul, h, Int.sub_self]
  cases Int.mul_eq_zero.mp hdiff with
  | inl hxy => omega
  | inr hzz => exact absurd hzz hz

theorem equiv_trans {a b c : RawRat} (hab : Equiv a b) (hbc : Equiv b c) : Equiv a c := by
  unfold Equiv at *
  apply int_mul_cancel_right (den_int_ne_zero b)
  calc
    a.num * (c.den : Int) * (b.den : Int)
      = (a.num * (b.den : Int)) * (c.den : Int) := by
          simp only [Int.mul_assoc, int_mul_left_comm, Int.mul_comm]
    _ = (b.num * (a.den : Int)) * (c.den : Int) := by rw [hab]
    _ = (b.num * (c.den : Int)) * (a.den : Int) := by
          simp only [Int.mul_assoc, int_mul_left_comm, Int.mul_comm]
    _ = (c.num * (b.den : Int)) * (a.den : Int) := by rw [hbc]
    _ = c.num * (a.den : Int) * (b.den : Int) := by
          simp only [Int.mul_assoc, int_mul_left_comm, Int.mul_comm]

def ofInt (n : Int) : RawRat := ⟨n, 1, Nat.zero_lt_one⟩
def half : RawRat := ⟨1, 2, by decide⟩

def neg (a : RawRat) : RawRat := ⟨-a.num, a.den, a.den_pos⟩

def add (a b : RawRat) : RawRat :=
  ⟨a.num * (b.den : Int) + b.num * (a.den : Int), a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

def mul (a b : RawRat) : RawRat :=
  ⟨a.num * b.num, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

def inv (a : RawRat) : RawRat :=
  if hpos : 0 < a.num then
    ⟨(a.den : Int), a.num.toNat, by omega⟩
  else if hneg : a.num < 0 then
    ⟨-(a.den : Int), (-a.num).toNat, by omega⟩
  else
    ofInt 0

theorem neg_congr {a b : RawRat} (h : Equiv a b) : Equiv (neg a) (neg b) := by
  unfold Equiv neg at *
  dsimp
  rw [Int.neg_mul, Int.neg_mul, h]

theorem add_congr {a₁ a₂ b₁ b₂ : RawRat} (ha : Equiv a₁ a₂) (hb : Equiv b₁ b₂) :
    Equiv (add a₁ b₁) (add a₂ b₂) := by
  unfold Equiv add at *
  dsimp
  push_cast
  have t1 : a₁.num * (b₁.den : Int) * ((a₂.den : Int) * (b₂.den : Int)) =
            a₂.num * (b₂.den : Int) * ((a₁.den : Int) * (b₁.den : Int)) := by
    calc
      a₁.num * (b₁.den : Int) * ((a₂.den : Int) * (b₂.den : Int))
        = (a₁.num * (a₂.den : Int)) * ((b₁.den : Int) * (b₂.den : Int)) := by
            simp only [Int.mul_assoc, int_mul_left_comm, Int.mul_comm]
      _ = (a₂.num * (a₁.den : Int)) * ((b₁.den : Int) * (b₂.den : Int)) := by rw [ha]
      _ = a₂.num * (b₂.den : Int) * ((a₁.den : Int) * (b₁.den : Int)) := by
            simp only [Int.mul_assoc, int_mul_left_comm, Int.mul_comm]
  have t2 : b₁.num * (a₁.den : Int) * ((a₂.den : Int) * (b₂.den : Int)) =
            b₂.num * (a₂.den : Int) * ((a₁.den : Int) * (b₁.den : Int)) := by
    calc
      b₁.num * (a₁.den : Int) * ((a₂.den : Int) * (b₂.den : Int))
        = (b₁.num * (b₂.den : Int)) * ((a₁.den : Int) * (a₂.den : Int)) := by
            simp only [Int.mul_assoc, int_mul_left_comm, Int.mul_comm]
      _ = (b₂.num * (b₁.den : Int)) * ((a₁.den : Int) * (a₂.den : Int)) := by rw [hb]
      _ = b₂.num * (a₂.den : Int) * ((a₁.den : Int) * (b₁.den : Int)) := by
            simp only [Int.mul_assoc, int_mul_left_comm, Int.mul_comm]
  rw [Int.add_mul, Int.add_mul, t1, t2]

theorem mul_congr {a₁ a₂ b₁ b₂ : RawRat} (ha : Equiv a₁ a₂) (hb : Equiv b₁ b₂) :
    Equiv (mul a₁ b₁) (mul a₂ b₂) := by
  unfold Equiv mul at *
  dsimp
  push_cast
  calc
    a₁.num * b₁.num * ((a₂.den : Int) * (b₂.den : Int))
      = (a₁.num * (a₂.den : Int)) * (b₁.num * (b₂.den : Int)) := by
          simp only [Int.mul_assoc, int_mul_left_comm, Int.mul_comm]
    _ = (a₂.num * (a₁.den : Int)) * (b₂.num * (b₁.den : Int)) := by rw [ha, hb]
    _ = a₂.num * b₂.num * ((a₁.den : Int) * (b₁.den : Int)) := by
          simp only [Int.mul_assoc, int_mul_left_comm, Int.mul_comm]

theorem num_pos_iff_of_equiv {a b : RawRat} (h : Equiv a b) : 0 < a.num ↔ 0 < b.num := by
  unfold Equiv at h
  have ha := den_int_pos a
  have hb := den_int_pos b
  constructor <;> intro hp
  · have hprod : 0 < a.num * (b.den : Int) := Int.mul_pos hp hb
    rw [h] at hprod
    if hpb : 0 < b.num then
      exact hpb
    else
      have hle : b.num ≤ 0 := by omega
      have hle2 : b.num * (a.den : Int) ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg hle (by omega)
      omega
  · have hprod : 0 < b.num * (a.den : Int) := Int.mul_pos hp ha
    rw [← h] at hprod
    if hpa : 0 < a.num then
      exact hpa
    else
      have hle : a.num ≤ 0 := by omega
      have hle2 : a.num * (b.den : Int) ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg hle (by omega)
      omega

theorem num_neg_iff_of_equiv {a b : RawRat} (h : Equiv a b) : a.num < 0 ↔ b.num < 0 := by
  have hneg : Equiv (neg a) (neg b) := neg_congr h
  have hp := num_pos_iff_of_equiv hneg
  dsimp [neg] at hp
  omega

theorem inv_congr {a b : RawRat} (h : Equiv a b) : Equiv (inv a) (inv b) := by
  have hpos_iff := num_pos_iff_of_equiv h
  have hneg_iff := num_neg_iff_of_equiv h
  unfold inv
  by_cases hp : 0 < a.num
  · have hpb : 0 < b.num := hpos_iff.mp hp
    rw [dif_pos hp, dif_pos hpb]
    unfold Equiv at *
    dsimp
    have ha_nat : ((a.num.toNat : Nat) : Int) = a.num := Int.toNat_of_nonneg (by omega)
    have hb_nat : ((b.num.toNat : Nat) : Int) = b.num := Int.toNat_of_nonneg (by omega)
    rw [ha_nat, hb_nat]
    calc
      (a.den : Int) * b.num = b.num * (a.den : Int) := Int.mul_comm _ _
      _ = a.num * (b.den : Int) := h.symm
      _ = (b.den : Int) * a.num := Int.mul_comm _ _
  · rw [dif_neg hp]
    have hnpb : ¬ (0 < b.num) := fun hpb => hp (hpos_iff.mpr hpb)
    rw [dif_neg hnpb]
    by_cases hn : a.num < 0
    · have hnb : b.num < 0 := hneg_iff.mp hn
      rw [dif_pos hn, dif_pos hnb]
      unfold Equiv at *
      dsimp
      have ha_nat : (((-a.num).toNat : Nat) : Int) = -a.num := Int.toNat_of_nonneg (by omega)
      have hb_nat : (((-b.num).toNat : Nat) : Int) = -b.num := Int.toNat_of_nonneg (by omega)
      rw [ha_nat, hb_nat]
      calc
        -(a.den : Int) * -b.num = b.num * (a.den : Int) := by
          rw [Int.neg_mul, Int.mul_neg, Int.neg_neg, Int.mul_comm]
        _ = a.num * (b.den : Int) := h.symm
        _ = -(b.den : Int) * -a.num := by
          rw [Int.neg_mul, Int.mul_neg, Int.neg_neg, Int.mul_comm]
    · have hnnb : ¬ (b.num < 0) := fun hnb => hn (hneg_iff.mpr hnb)
      rw [dif_neg hn, dif_neg hnnb]
      rfl

end RawRat

/-- Exact rational numbers `ℚ = Quot RawRat.Equiv`. -/
def RatQ : Type := Quot RawRat.Equiv

namespace RatQ

def mk (r : RawRat) : RatQ := Quot.mk RawRat.Equiv r

def frac (num : Int) (den : Nat) (h : 0 < den := by decide) : RatQ :=
  mk ⟨num, den, h⟩

def ofInt (n : Int) : RatQ := mk (RawRat.ofInt n)

theorem mk_eq_iff {a b : RawRat} : mk a = mk b ↔ RawRat.Equiv a b := by
  constructor
  · intro h
    let P : RatQ → Prop := Quot.lift (fun x => RawRat.Equiv a x) (fun x y hxy =>
      propext ⟨fun hax => RawRat.equiv_trans hax hxy,
               fun hay => RawRat.equiv_trans hay (RawRat.equiv_symm hxy)⟩)
    have ha : P (mk a) := RawRat.equiv_refl a
    rw [h] at ha
    exact ha
  · exact Quot.sound

def neg : RatQ → RatQ :=
  Quot.lift (fun a => mk (RawRat.neg a)) (fun _ _ h => Quot.sound (RawRat.neg_congr h))

def add : RatQ → RatQ → RatQ :=
  Quot.lift
    (fun a => Quot.lift (fun b => mk (RawRat.add a b))
      (fun _ _ hb => Quot.sound (RawRat.add_congr (RawRat.equiv_refl a) hb)))
    (fun _ _ ha => funext fun q => Quot.inductionOn q fun b =>
      Quot.sound (RawRat.add_congr ha (RawRat.equiv_refl b)))

def mul : RatQ → RatQ → RatQ :=
  Quot.lift
    (fun a => Quot.lift (fun b => mk (RawRat.mul a b))
      (fun _ _ hb => Quot.sound (RawRat.mul_congr (RawRat.equiv_refl a) hb)))
    (fun _ _ ha => funext fun q => Quot.inductionOn q fun b =>
      Quot.sound (RawRat.mul_congr ha (RawRat.equiv_refl b)))

def sub (x y : RatQ) : RatQ := add x (neg y)

def inv : RatQ → RatQ :=
  Quot.lift (fun a => mk (RawRat.inv a)) (fun _ _ h => Quot.sound (RawRat.inv_congr h))

def half : RatQ := mk RawRat.half

instance : Zero RatQ := ⟨ofInt (Int.ofNat 0)⟩
instance : One RatQ := ⟨ofInt (Int.ofNat 1)⟩
instance : Add RatQ := ⟨add⟩
instance : Neg RatQ := ⟨neg⟩
instance : Sub RatQ := ⟨sub⟩
instance : Mul RatQ := ⟨mul⟩
instance (n : Nat) : OfNat RatQ n := ⟨ofInt (Int.ofNat n)⟩

/-- Strict positivity `0 < x` on `RatQ`. -/
def IsPos : RatQ → Prop :=
  Quot.lift (fun a => 0 < a.num) (fun _ _ h => propext (RawRat.num_pos_iff_of_equiv h))

/-- Boolean zero test on `RatQ` for fast computational inequality proofs. -/
def isZero : RatQ → Bool :=
  Quot.lift (fun a => decide (a.num = 0)) (fun a b h => by
    have hp := RawRat.num_pos_iff_of_equiv h
    have hn := RawRat.num_neg_iff_of_equiv h
    by_cases hz : a.num = 0
    · have hzb : b.num = 0 := by omega
      simp [hz, hzb]
    · have hnzb : b.num ≠ 0 := by omega
      simp [hz, hnzb])

theorem isZero_iff (x : RatQ) : isZero x = true ↔ x = 0 := by
  refine Quot.inductionOn x fun a => ?_
  change decide (a.num = 0) = true ↔ mk a = mk (RawRat.ofInt 0)
  rw [mk_eq_iff]
  unfold RawRat.Equiv RawRat.ofInt
  dsimp
  simp only [Int.mul_one, Int.zero_mul, decide_eq_true_eq]

theorem ne_of_sub_isZero_false {x y : RatQ} (h : isZero (x - y) = false) : x ≠ y := by
  intro hxy
  rw [hxy] at h
  refine Quot.inductionOn y (fun a ha => ?_) h
  change decide ((a.num * (a.den : Int) + (-a.num) * (a.den : Int)) = 0) = false at ha
  rw [Int.neg_mul, Int.add_right_neg] at ha
  contradiction

private theorem int_mul_left_comm (a b c : Int) : a * (b * c) = b * (a * c) := by
  rw [← Int.mul_assoc, Int.mul_comm a b, Int.mul_assoc]

private theorem add_assoc_thm (x y z : RatQ) : x + y + z = x + (y + z) := by
  refine Quot.inductionOn x fun a => Quot.inductionOn y fun b => Quot.inductionOn z fun c => ?_
  apply Quot.sound
  unfold RawRat.Equiv RawRat.add
  dsimp
  push_cast
  have lhs_eq :
      (a.num * (b.den : Int) + b.num * (a.den : Int)) * (c.den : Int) +
      c.num * ((a.den : Int) * (b.den : Int))
      = a.num * ((b.den : Int) * (c.den : Int)) +
        (b.num * (c.den : Int) + c.num * (b.den : Int)) * (a.den : Int) := by
    rw [Int.add_mul, Int.add_mul, Int.add_assoc]
    have m1 : a.num * (b.den : Int) * (c.den : Int) = a.num * ((b.den : Int) * (c.den : Int)) :=
      Int.mul_assoc _ _ _
    have m2 : b.num * (a.den : Int) * (c.den : Int) = b.num * (c.den : Int) * (a.den : Int) := by
      simp only [Int.mul_assoc, int_mul_left_comm, Int.mul_comm]
    have m3 : c.num * ((a.den : Int) * (b.den : Int)) = c.num * (b.den : Int) * (a.den : Int) := by
      simp only [Int.mul_assoc, int_mul_left_comm, Int.mul_comm]
    rw [m1, m2, m3]
  rw [lhs_eq, Int.mul_assoc (a.den : Int) (b.den : Int) (c.den : Int)]

private theorem add_comm_thm (x y : RatQ) : x + y = y + x := by
  refine Quot.inductionOn x fun a => Quot.inductionOn y fun b => ?_
  apply Quot.sound
  unfold RawRat.Equiv RawRat.add
  dsimp
  push_cast
  rw [Int.add_comm (a.num * (b.den : Int)), Int.mul_comm (a.den : Int) (b.den : Int)]

private theorem zero_add_thm (x : RatQ) : 0 + x = x := by
  refine Quot.inductionOn x fun a => ?_
  apply Quot.sound
  change ((RawRat.ofInt 0).add a).Equiv a
  unfold RawRat.Equiv RawRat.add RawRat.ofInt
  dsimp
  simp [Int.zero_mul, Int.one_mul, Int.zero_add]

private theorem add_zero_thm (x : RatQ) : x + 0 = x := by
  rw [add_comm_thm, zero_add_thm]

private theorem neg_add_cancel_thm (x : RatQ) : -x + x = 0 := by
  refine Quot.inductionOn x fun a => ?_
  apply Quot.sound
  change (a.neg.add a).Equiv (RawRat.ofInt 0)
  unfold RawRat.Equiv RawRat.add RawRat.neg RawRat.ofInt
  dsimp
  rw [Int.neg_mul, Int.add_left_neg, Int.zero_mul, Int.zero_mul]

private theorem mul_assoc_thm (x y z : RatQ) : x * y * z = x * (y * z) := by
  refine Quot.inductionOn x fun a => Quot.inductionOn y fun b => Quot.inductionOn z fun c => ?_
  apply Quot.sound
  unfold RawRat.Equiv RawRat.mul
  dsimp
  push_cast
  rw [Int.mul_assoc a.num b.num c.num, Int.mul_assoc (a.den : Int) (b.den : Int) (c.den : Int)]

private theorem mul_comm_thm (x y : RatQ) : x * y = y * x := by
  refine Quot.inductionOn x fun a => Quot.inductionOn y fun b => ?_
  apply Quot.sound
  unfold RawRat.Equiv RawRat.mul
  dsimp
  push_cast
  rw [Int.mul_comm a.num b.num, Int.mul_comm (a.den : Int) (b.den : Int)]

private theorem one_mul_thm (x : RatQ) : 1 * x = x := by
  refine Quot.inductionOn x fun a => ?_
  apply Quot.sound
  change ((RawRat.ofInt 1).mul a).Equiv a
  unfold RawRat.Equiv RawRat.mul RawRat.ofInt
  dsimp
  simp [Int.one_mul]

private theorem mul_one_thm (x : RatQ) : x * 1 = x := by
  rw [mul_comm_thm, one_mul_thm]

private theorem left_distrib_thm (x y z : RatQ) : x * (y + z) = x * y + x * z := by
  refine Quot.inductionOn x fun a => Quot.inductionOn y fun b => Quot.inductionOn z fun c => ?_
  apply Quot.sound
  unfold RawRat.Equiv RawRat.mul RawRat.add
  dsimp
  push_cast
  rw [Int.mul_add, Int.add_mul, Int.add_mul]
  have p1 :
      a.num * (b.num * (c.den : Int)) *
        ((a.den : Int) * (b.den : Int) * ((a.den : Int) * (c.den : Int)))
      = a.num * b.num * ((a.den : Int) * (c.den : Int)) *
        ((a.den : Int) * ((b.den : Int) * (c.den : Int))) := by
    simp only [Int.mul_assoc, int_mul_left_comm, Int.mul_comm]
  have p2 :
      a.num * (c.num * (b.den : Int)) *
        ((a.den : Int) * (b.den : Int) * ((a.den : Int) * (c.den : Int)))
      = a.num * c.num * ((a.den : Int) * (b.den : Int)) *
        ((a.den : Int) * ((b.den : Int) * (c.den : Int))) := by
    simp only [Int.mul_assoc, int_mul_left_comm, Int.mul_comm]
  rw [p1, p2]

private theorem right_distrib_thm (x y z : RatQ) : (x + y) * z = x * z + y * z := by
  rw [mul_comm_thm, left_distrib_thm, mul_comm_thm x z, mul_comm_thm y z]

private theorem two_mul_half_thm : ((1 : RatQ) + 1) * half = 1 := by
  apply Quot.sound
  rfl

instance : CommRing2 RatQ where
  half := half
  add_assoc := add_assoc_thm
  add_comm := add_comm_thm
  zero_add := zero_add_thm
  add_zero := add_zero_thm
  neg_add_cancel := neg_add_cancel_thm
  sub_eq_add_neg := fun _ _ => rfl
  mul_assoc := mul_assoc_thm
  mul_comm := mul_comm_thm
  one_mul := one_mul_thm
  mul_one := mul_one_thm
  left_distrib := left_distrib_thm
  right_distrib := right_distrib_thm
  two_mul_half := two_mul_half_thm

/-- Multiplicative inverse property confirming `RatQ` is a genuine field. -/
theorem mul_inv_cancel {x : RatQ} (hx : x ≠ 0) : x * inv x = 1 := by
  refine Quot.inductionOn x (fun a ha => ?_) hx
  have hnum : a.num ≠ 0 := by
    intro hz
    apply ha
    apply Quot.sound
    change a.Equiv (RawRat.ofInt 0)
    unfold RawRat.Equiv RawRat.ofInt
    dsimp
    simp [hz]
  apply Quot.sound
  change (a.mul a.inv).Equiv (RawRat.ofInt 1)
  unfold RawRat.Equiv RawRat.mul RawRat.inv RawRat.ofInt
  by_cases hp : 0 < a.num
  · rw [dif_pos hp]
    dsimp
    push_cast
    have hnat : ((a.num.toNat : Nat) : Int) = a.num := Int.toNat_of_nonneg (by omega)
    rw [hnat, Int.mul_one, Int.one_mul, Int.mul_comm]
  · rw [dif_neg hp]
    have hn : a.num < 0 := by omega
    rw [dif_pos hn]
    dsimp
    push_cast
    have hnat : (((-a.num).toNat : Nat) : Int) = -a.num := Int.toNat_of_nonneg (by omega)
    rw [hnat, Int.mul_one, Int.one_mul, Int.mul_neg, Int.mul_neg, Int.mul_comm]

theorem one_ne_zero : (1 : RatQ) ≠ 0 :=
  ne_of_sub_isZero_false rfl

theorem two_ne_zero : ((1 : RatQ) + 1) ≠ 0 :=
  ne_of_sub_isZero_false rfl

theorem pos_add {x y : RatQ} (hx : IsPos x) (hy : IsPos y) : IsPos (x + y) := by
  refine Quot.inductionOn x (fun a ha => Quot.inductionOn y (fun b hb => ?_) hy) hx
  change 0 < a.num * (b.den : Int) + b.num * (a.den : Int)
  have p1 : 0 < a.num * (b.den : Int) := Int.mul_pos ha (RawRat.den_int_pos b)
  have p2 : 0 < b.num * (a.den : Int) := Int.mul_pos hb (RawRat.den_int_pos a)
  omega

theorem pos_mul {x y : RatQ} (hx : IsPos x) (hy : IsPos y) : IsPos (x * y) := by
  refine Quot.inductionOn x (fun a ha => Quot.inductionOn y (fun b hb => ?_) hy) hx
  change 0 < a.num * b.num
  exact Int.mul_pos ha hb

theorem pos_ne_zero {x : RatQ} (hx : IsPos x) : x ≠ 0 := by
  intro hz
  rw [hz] at hx
  change 0 < (0 : Int) at hx
  omega

theorem sq_pos_of_ne_zero {x : RatQ} (hx : x ≠ 0) : IsPos (x * x) := by
  refine Quot.inductionOn x (fun a ha => ?_) hx
  change 0 < a.num * a.num
  have hnum : a.num ≠ 0 := by
    intro hz
    apply ha
    apply Quot.sound
    change a.Equiv (RawRat.ofInt 0)
    unfold RawRat.Equiv RawRat.ofInt
    dsimp
    simp [hz]
  by_cases hp : 0 < a.num
  · exact Int.mul_pos hp hp
  · have hn : a.num < 0 := by omega
    have hnp : 0 < -a.num := by omega
    have heq : (-a.num) * (-a.num) = a.num * a.num := by
      rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    rw [← heq]
    exact Int.mul_pos hnp hnp

/-- Nonnegativity `0 ≤ x` on `RatQ`. -/
def IsNonneg (x : RatQ) : Prop := x = 0 ∨ IsPos x

theorem sq_nonneg (x : RatQ) : IsNonneg (x * x) := by
  refine Quot.inductionOn x fun a => ?_
  by_cases hz : a.num = 0
  · left
    apply Quot.sound
    change (a.mul a).Equiv (RawRat.ofInt 0)
    unfold RawRat.Equiv RawRat.mul RawRat.ofInt
    dsimp
    simp [hz]
  · right
    apply sq_pos_of_ne_zero
    intro heq
    have h0 := (mk_eq_iff.mp heq)
    unfold RawRat.Equiv RawRat.ofInt at h0
    dsimp at h0
    omega

theorem nonneg_add {x y : RatQ} (hx : IsNonneg x) (hy : IsNonneg y) : IsNonneg (x + y) := by
  cases hx with
  | inl hx0 =>
    rw [hx0, CommRing2.zero_add]
    exact hy
  | inr hxp =>
    right
    cases hy with
    | inl hy0 => rw [hy0, CommRing2.add_zero]; exact hxp
    | inr hyp => exact pos_add hxp hyp

theorem nonneg_mul {x y : RatQ} (hx : IsNonneg x) (hy : IsNonneg y) : IsNonneg (x * y) := by
  cases hx with
  | inl hx0 => left; rw [hx0, CommRing2.zero_mul]
  | inr hxp =>
    cases hy with
    | inl hy0 => left; rw [hy0, CommRing2.mul_zero]
    | inr hyp => right; exact pos_mul hxp hyp

theorem add_pos_of_pos_of_nonneg {x y : RatQ} (hx : IsPos x) (hy : IsNonneg y) : IsPos (x + y) := by
  cases hy with
  | inl hy0 => rw [hy0, CommRing2.add_zero]; exact hx
  | inr hyp => exact pos_add hx hyp

theorem add_pos_of_nonneg_of_pos {x y : RatQ} (hx : IsNonneg x) (hy : IsPos y) : IsPos (x + y) := by
  rw [CommRing2.add_comm]
  exact add_pos_of_pos_of_nonneg hy hx

end RatQ
end CliffordDecomp
