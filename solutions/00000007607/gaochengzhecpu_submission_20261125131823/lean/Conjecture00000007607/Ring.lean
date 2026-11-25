import Conjecture00000007607.RingBase

namespace Conjecture00000007607

/-!
# Ordered Commutative Rings & Concrete Instances (`ℤ`, `ℚ`, `ℚ[√2]`)

Builds on `RingBase` and its `comm_ring` tactic to establish:
1. `StrictOrderedCommRing R` and universal sum-of-squares / integral-domain theorems.
2. Concrete verified instances: `Int`, exact rationals `QRat` (`ℚ`), and `QSqrt2` (`ℚ[√2]`).
-/

class StrictOrderedCommRing (R : Type) extends CommRing R, LE R, LT R where
  zero_lt_one : (0 : R) < 1
  le_refl : ∀ a : R, a ≤ a
  le_trans : ∀ a b c : R, a ≤ b → b ≤ c → a ≤ c
  le_antisymm : ∀ a b : R, a ≤ b → b ≤ a → a = b
  le_total : ∀ a b : R, a ≤ b ∨ b ≤ a
  lt_iff_le_not_le : ∀ a b : R, a < b ↔ a ≤ b ∧ ¬ b ≤ a
  add_le_add_left : ∀ a b : R, a ≤ b → ∀ c : R, c + a ≤ c + b
  mul_pos : ∀ a b : R, 0 < a → 0 < b → 0 < a * b

namespace StrictOrderedCommRing

section Ordered
variable {R : Type} [StrictOrderedCommRing R]

theorem lt_irrefl (a : R) : ¬ (a < a) := by
  intro h
  have ⟨_, hnot⟩ := (lt_iff_le_not_le a a).mp h
  exact hnot (le_refl a)

theorem ne_of_lt {a b : R} (h : a < b) : a ≠ b := by
  intro heq
  rw [heq] at h
  exact lt_irrefl b h

theorem le_of_lt {a b : R} (h : a < b) : a ≤ b :=
  ((lt_iff_le_not_le a b).mp h).1

theorem lt_of_le_of_ne {a b : R} (hle : a ≤ b) (hne : a ≠ b) : a < b := by
  rw [lt_iff_le_not_le]
  refine ⟨hle, fun hba => hne (le_antisymm a b hle hba)⟩

theorem lt_of_lt_of_le {a b c : R} (hab : a < b) (hbc : b ≤ c) : a < c := by
  have ⟨h1, hnot1⟩ := (lt_iff_le_not_le a b).mp hab
  rw [lt_iff_le_not_le]
  refine ⟨le_trans a b c h1 hbc, fun hca => hnot1 (le_trans b c a hbc hca)⟩

theorem lt_of_le_of_lt {a b c : R} (hab : a ≤ b) (hbc : b < c) : a < c := by
  have ⟨h2, hnot2⟩ := (lt_iff_le_not_le b c).mp hbc
  rw [lt_iff_le_not_le]
  refine ⟨le_trans a b c hab h2, fun hca => hnot2 (le_trans c a b hca hab)⟩

theorem lt_trans {a b c : R} (hab : a < b) (hbc : b < c) : a < c :=
  lt_of_lt_of_le hab (le_of_lt hbc)

theorem lt_trichotomy (a b : R) : a < b ∨ a = b ∨ b < a := by
  cases le_total a b with
  | inl hab =>
    by_cases hba : b ≤ a
    · exact Or.inr (Or.inl (le_antisymm a b hab hba))
    · exact Or.inl ((lt_iff_le_not_le a b).mpr ⟨hab, hba⟩)
  | inr hba =>
    by_cases hab : a ≤ b
    · exact Or.inr (Or.inl (le_antisymm a b hab hba))
    · exact Or.inr (Or.inr ((lt_iff_le_not_le b a).mpr ⟨hba, hab⟩))

theorem add_le_add_right {a b : R} (h : a ≤ b) (c : R) : a + c ≤ b + c := by
  rw [CommRing.add_comm a c, CommRing.add_comm b c]
  exact add_le_add_left a b h c

theorem add_nonneg {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  have h1 : (0 : R) + 0 ≤ a + 0 := add_le_add_right ha 0
  rw [CommRing.add_zero', CommRing.add_zero'] at h1
  have h2 : a + 0 ≤ a + b := add_le_add_left 0 b hb a
  rw [CommRing.add_zero'] at h2
  exact le_trans 0 a (a + b) h1 h2

theorem add_pos_of_pos_of_nonneg {a b : R} (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b := by
  have h2 : a + 0 ≤ a + b := add_le_add_left 0 b hb a
  rw [CommRing.add_zero'] at h2
  exact lt_of_lt_of_le ha h2

theorem add_pos_of_nonneg_of_pos {a b : R} (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b := by
  rw [CommRing.add_comm]
  exact add_pos_of_pos_of_nonneg hb ha

theorem add_pos {a b : R} (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
  add_pos_of_pos_of_nonneg ha (le_of_lt hb)

theorem neg_pos_of_neg {a : R} (h : a < 0) : 0 < -a := by
  have hle : a ≤ 0 := le_of_lt h
  have h1 : -a + a ≤ -a + 0 := add_le_add_left a 0 hle (-a)
  rw [CommRing.add_left_neg', CommRing.add_zero'] at h1
  apply lt_of_le_of_ne h1
  intro heq
  have ha : a = 0 := by
    have h2 : - -a = -(0 : R) := congrArg Neg.neg heq.symm
    rw [CommRing.neg_neg, CommRing.neg_zero] at h2
    exact h2
  exact ne_of_lt h ha

theorem sub_pos_iff {a b : R} : 0 < b - a ↔ a < b := by
  constructor
  · intro h
    have hle : 0 ≤ b - a := le_of_lt h
    have h1 : a + 0 ≤ a + (b - a) := add_le_add_left 0 (b - a) hle a
    have heq : a + (b - a) = b := by comm_ring
    rw [CommRing.add_zero', heq] at h1
    apply lt_of_le_of_ne h1
    intro hab
    rw [hab, CommRing.sub_self] at h
    exact lt_irrefl 0 h
  · intro h
    have hle : a ≤ b := le_of_lt h
    have h1 : -a + a ≤ -a + b := add_le_add_left a b hle (-a)
    have heq : -a + b = b - a := by comm_ring
    rw [CommRing.add_left_neg', heq] at h1
    apply lt_of_le_of_ne h1
    intro h0
    have hab : b = a := CommRing.sub_eq_zero_iff.mp h0.symm
    exact ne_of_lt h hab.symm

theorem sq_pos_of_ne_zero {a : R} (h : a ≠ 0) : 0 < a * a := by
  rcases lt_trichotomy a 0 with hlt | heq | hgt
  · have hpos : 0 < -a := neg_pos_of_neg hlt
    have hm : 0 < (-a) * (-a) := mul_pos (-a) (-a) hpos hpos
    have hid : (-a) * (-a) = a * a := by comm_ring
    rw [hid] at hm
    exact hm
  · exact absurd heq h
  · exact mul_pos a a hgt hgt

theorem sq_nonneg (a : R) : 0 ≤ a * a := by
  by_cases h : a = 0
  · rw [h, CommRing.zero_mul]
    exact le_refl 0
  · exact le_of_lt (sq_pos_of_ne_zero h)

theorem sq_eq_zero_iff {a : R} : a * a = 0 ↔ a = 0 := by
  constructor
  · intro h
    by_cases ha : a = 0
    · exact ha
    · exfalso
      have hp := sq_pos_of_ne_zero ha
      rw [h] at hp
      exact lt_irrefl 0 hp
  · intro h
    rw [h, CommRing.zero_mul]

theorem mul_ne_zero {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro hab
  rcases lt_trichotomy a 0 with ha1 | ha0 | ha2
  · rcases lt_trichotomy b 0 with hb1 | hb0 | hb2
    · have hp := mul_pos (-a) (-b) (neg_pos_of_neg ha1) (neg_pos_of_neg hb1)
      have hid : (-a) * (-b) = a * b := by comm_ring
      rw [hid, hab] at hp; exact lt_irrefl 0 hp
    · exact hb hb0
    · have hp := mul_pos (-a) b (neg_pos_of_neg ha1) hb2
      have hid : (-a) * b = -(a * b) := by comm_ring
      rw [hid, hab, CommRing.neg_zero] at hp; exact lt_irrefl 0 hp
  · exact ha ha0
  · rcases lt_trichotomy b 0 with hb1 | hb0 | hb2
    · have hp := mul_pos a (-b) ha2 (neg_pos_of_neg hb1)
      have hid : a * (-b) = -(a * b) := by comm_ring
      rw [hid, hab, CommRing.neg_zero] at hp; exact lt_irrefl 0 hp
    · exact hb hb0
    · have hp := mul_pos a b ha2 hb2
      rw [hab] at hp; exact lt_irrefl 0 hp

theorem mul_eq_zero_iff {a b : R} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    by_cases ha : a = 0
    · exact Or.inl ha
    · by_cases hb : b = 0
      · exact Or.inr hb
      · exact absurd h (mul_ne_zero ha hb)
  · intro h
    rcases h with rfl | rfl
    · exact CommRing.zero_mul b
    · exact CommRing.mul_zero a

theorem eq_or_eq_neg_of_sq_eq {a b : R} (h : a * a = b * b) : a = b ∨ a = -b := by
  have hprod : (a - b) * (a + b) = 0 := by
    calc
      (a - b) * (a + b) = a * a - b * b := by comm_ring
      _ = b * b - b * b := by rw [h]
      _ = 0 := CommRing.sub_self (b * b)
  rcases mul_eq_zero_iff.mp hprod with h1 | h2
  · exact Or.inl (CommRing.sub_eq_zero_iff.mp h1)
  · right
    have hsub : a - (-b) = a + b := by comm_ring
    exact CommRing.sub_eq_zero_iff.mp (hsub.trans h2)

theorem add_eq_zero_of_nonneg {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 0) :
    a = 0 ∧ b = 0 := by
  have ha0 : a = 0 := by
    by_cases hne : a = 0
    · exact hne
    · exfalso
      have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hne)
      have hpos : 0 < a + b := add_pos_of_pos_of_nonneg hapos hb
      rw [h] at hpos
      exact lt_irrefl 0 hpos
  refine ⟨ha0, ?_⟩
  rw [ha0, CommRing.zero_add'] at h
  exact h

theorem sum2_sq_nonneg (x y : R) : 0 ≤ x * x + y * y :=
  add_nonneg (sq_nonneg x) (sq_nonneg y)

theorem sum3_sq_nonneg (x y z : R) : 0 ≤ x * x + y * y + z * z :=
  add_nonneg (sum2_sq_nonneg x y) (sq_nonneg z)

theorem sum2_sq_eq_zero_iff {x y : R} : x * x + y * y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    obtain ⟨hx, hy⟩ := add_eq_zero_of_nonneg (sq_nonneg x) (sq_nonneg y) h
    exact ⟨sq_eq_zero_iff.mp hx, sq_eq_zero_iff.mp hy⟩
  · rintro ⟨rfl, rfl⟩; comm_ring

theorem sum3_sq_eq_zero_iff {x y z : R} :
    x * x + y * y + z * z = 0 ↔ x = 0 ∧ y = 0 ∧ z = 0 := by
  constructor
  · intro h
    obtain ⟨hxy, hz⟩ := add_eq_zero_of_nonneg (sum2_sq_nonneg x y) (sq_nonneg z) h
    obtain ⟨hx, hy⟩ := sum2_sq_eq_zero_iff.mp hxy
    exact ⟨hx, hy, sq_eq_zero_iff.mp hz⟩
  · rintro ⟨rfl, rfl, rfl⟩; comm_ring

theorem two_pos : (0 : R) < 1 + 1 := add_pos zero_lt_one zero_lt_one

theorem two_ne_zero : ((1 : R) + 1) ≠ 0 := Ne.symm (ne_of_lt two_pos)

end Ordered

end StrictOrderedCommRing

/-! ## Concrete Instance 1: `Int` (`ℤ`) -/

instance : CommRing Int where
  zero := 0
  one := 1
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  add_left_neg := Int.add_left_neg
  sub_eq_add_neg := fun _ _ => Int.sub_eq_add_neg
  mul_assoc := Int.mul_assoc
  mul_comm := Int.mul_comm
  one_mul := Int.one_mul
  mul_one := Int.mul_one
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul

instance : StrictOrderedCommRing Int where
  zero_lt_one := by decide
  le_refl := Int.le_refl
  le_trans := fun _ _ _ => Int.le_trans
  le_antisymm := fun _ _ => Int.le_antisymm
  le_total := Int.le_total
  lt_iff_le_not_le := fun a b => by omega
  add_le_add_left := fun _ _ h c => Int.add_le_add_left h c
  mul_pos := fun _ _ => Int.mul_pos

/-! ## Concrete Instance 2: Exact Rationals `QRat` (`ℚ`) -/

structure PreRat where
  num : Int
  den : Int
  den_pos : 0 < den

namespace PreRat

def Equiv (a b : PreRat) : Prop := a.num * b.den = b.num * a.den

def add (a b : PreRat) : PreRat where
  num := a.num * b.den + b.num * a.den
  den := a.den * b.den
  den_pos := Int.mul_pos a.den_pos b.den_pos

def neg (a : PreRat) : PreRat where
  num := -a.num
  den := a.den
  den_pos := a.den_pos

def mul (a b : PreRat) : PreRat where
  num := a.num * b.num
  den := a.den * b.den
  den_pos := Int.mul_pos a.den_pos b.den_pos

end PreRat

abbrev QRat : Type := Quot PreRat.Equiv

namespace QRat

def mk (n : Int) (d : Int) (hd : 0 < d := by decide) : QRat :=
  Quot.mk PreRat.Equiv ⟨n, d, hd⟩

def ofInt (n : Int) : QRat := mk n 1 (by decide)

theorem ind1 {P : QRat → Prop} (h : ∀ x : PreRat, P (Quot.mk PreRat.Equiv x)) (a : QRat) :
    P a := Quot.ind h a

theorem ind2 {P : QRat → QRat → Prop}
    (h : ∀ x y : PreRat, P (Quot.mk PreRat.Equiv x) (Quot.mk PreRat.Equiv y))
    (a b : QRat) : P a b :=
  @Quot.ind PreRat PreRat.Equiv (fun u => P u b)
    (fun x => @Quot.ind PreRat PreRat.Equiv (fun v => P (Quot.mk PreRat.Equiv x) v)
      (fun y => h x y) b) a

theorem ind3 {P : QRat → QRat → QRat → Prop}
    (h : ∀ x y z : PreRat,
      P (Quot.mk PreRat.Equiv x) (Quot.mk PreRat.Equiv y) (Quot.mk PreRat.Equiv z))
    (a b c : QRat) : P a b c :=
  @Quot.ind PreRat PreRat.Equiv (fun u => P u b c)
    (fun x => ind2 (P := fun v w => P (Quot.mk PreRat.Equiv x) v w) (fun y z => h x y z) b c) a

def lift2_helper {α : Type} (f : PreRat → PreRat → α)
    (hleft : ∀ a1 a2 b, PreRat.Equiv a1 a2 → f a1 b = f a2 b)
    (hright : ∀ a b1 b2, PreRat.Equiv b1 b2 → f a b1 = f a b2) :
    QRat → QRat → α :=
  Quot.lift
    (fun a => Quot.lift (fun b => f a b) (fun b1 b2 hb => hright a b1 b2 hb))
    (fun a1 a2 ha => funext fun q =>
      @Quot.ind PreRat PreRat.Equiv
        (fun z => Quot.lift (fun b => f a1 b) (fun b1 b2 hb => hright a1 b1 b2 hb) z =
                  Quot.lift (fun b => f a2 b) (fun b1 b2 hb => hright a2 b1 b2 hb) z)
        (fun b => hleft a1 a2 b ha) q)

def add : QRat → QRat → QRat :=
  lift2_helper (fun a b => Quot.mk PreRat.Equiv (PreRat.add a b))
    (fun a1 a2 b (ha : a1.num * a2.den = a2.num * a1.den) => Quot.sound (by
      show (a1.num * b.den + b.num * a1.den) * (a2.den * b.den) =
           (a2.num * b.den + b.num * a2.den) * (a1.den * b.den)
      calc
        (a1.num * b.den + b.num * a1.den) * (a2.den * b.den)
          = (a1.num * a2.den) * (b.den * b.den) + b.num * b.den * a1.den * a2.den := by comm_ring
        _ = (a2.num * a1.den) * (b.den * b.den) + b.num * b.den * a1.den * a2.den := by rw [ha]
        _ = (a2.num * b.den + b.num * a2.den) * (a1.den * b.den) := by comm_ring))
    (fun a b1 b2 (hb : b1.num * b2.den = b2.num * b1.den) => Quot.sound (by
      show (a.num * b1.den + b1.num * a.den) * (a.den * b2.den) =
           (a.num * b2.den + b2.num * a.den) * (a.den * b1.den)
      calc
        (a.num * b1.den + b1.num * a.den) * (a.den * b2.den)
          = a.num * a.den * b1.den * b2.den + (b1.num * b2.den) * (a.den * a.den) := by comm_ring
        _ = a.num * a.den * b1.den * b2.den + (b2.num * b1.den) * (a.den * a.den) := by rw [hb]
        _ = (a.num * b2.den + b2.num * a.den) * (a.den * b1.den) := by comm_ring))

def neg : QRat → QRat :=
  Quot.lift (fun a => Quot.mk PreRat.Equiv (PreRat.neg a))
    (fun a1 a2 (ha : a1.num * a2.den = a2.num * a1.den) => Quot.sound (by
      show (-a1.num) * a2.den = (-a2.num) * a1.den
      calc
        (-a1.num) * a2.den = -(a1.num * a2.den) := by comm_ring
        _ = -(a2.num * a1.den) := by rw [ha]
        _ = (-a2.num) * a1.den := by comm_ring))

def sub (x y : QRat) : QRat := add x (neg y)

def mul : QRat → QRat → QRat :=
  lift2_helper (fun a b => Quot.mk PreRat.Equiv (PreRat.mul a b))
    (fun a1 a2 b (ha : a1.num * a2.den = a2.num * a1.den) => Quot.sound (by
      show (a1.num * b.num) * (a2.den * b.den) = (a2.num * b.num) * (a1.den * b.den)
      calc
        (a1.num * b.num) * (a2.den * b.den)
          = (a1.num * a2.den) * (b.num * b.den) := by comm_ring
        _ = (a2.num * a1.den) * (b.num * b.den) := by rw [ha]
        _ = (a2.num * b.num) * (a1.den * b.den) := by comm_ring))
    (fun a b1 b2 (hb : b1.num * b2.den = b2.num * b1.den) => Quot.sound (by
      show (a.num * b1.num) * (a.den * b2.den) = (a.num * b2.num) * (a.den * b1.den)
      calc
        (a.num * b1.num) * (a.den * b2.den)
          = (a.num * a.den) * (b1.num * b2.den) := by comm_ring
        _ = (a.num * a.den) * (b2.num * b1.den) := by rw [hb]
        _ = (a.num * b2.num) * (a.den * b1.den) := by comm_ring))

instance : Add QRat := ⟨add⟩
instance : Neg QRat := ⟨neg⟩
instance : Sub QRat := ⟨sub⟩
instance : Mul QRat := ⟨mul⟩

instance : CommRing QRat where
  zero := ofInt 0
  one := ofInt 1
  add_assoc := ind3 fun x y z => Quot.sound (by
    show ((x.num * y.den + y.num * x.den) * z.den + z.num * (x.den * y.den)) *
         (x.den * (y.den * z.den)) =
         (x.num * (y.den * z.den) + (y.num * z.den + z.num * y.den) * x.den) *
         ((x.den * y.den) * z.den)
    comm_ring)
  add_comm := ind2 fun x y => Quot.sound (by
    show (x.num * y.den + y.num * x.den) * (y.den * x.den) =
         (y.num * x.den + x.num * y.den) * (x.den * y.den)
    comm_ring)
  zero_add := ind1 fun x => Quot.sound (by
    show ((0 : Int) * x.den + x.num * 1) * x.den = x.num * (1 * x.den)
    comm_ring)
  add_zero := ind1 fun x => Quot.sound (by
    show (x.num * 1 + (0 : Int) * x.den) * x.den = x.num * (x.den * 1)
    comm_ring)
  add_left_neg := ind1 fun x => Quot.sound (by
    show ((-x.num) * x.den + x.num * x.den) * 1 = (0 : Int) * (x.den * x.den)
    comm_ring)
  sub_eq_add_neg _ _ := rfl
  mul_assoc := ind3 fun x y z => Quot.sound (by
    show ((x.num * y.num) * z.num) * (x.den * (y.den * z.den)) =
         (x.num * (y.num * z.num)) * ((x.den * y.den) * z.den)
    comm_ring)
  mul_comm := ind2 fun x y => Quot.sound (by
    show (x.num * y.num) * (y.den * x.den) = (y.num * x.num) * (x.den * y.den)
    comm_ring)
  one_mul := ind1 fun x => Quot.sound (by
    show ((1 : Int) * x.num) * x.den = x.num * (1 * x.den)
    comm_ring)
  mul_one := ind1 fun x => Quot.sound (by
    show (x.num * (1 : Int)) * x.den = x.num * (x.den * 1)
    comm_ring)
  left_distrib := ind3 fun x y z => Quot.sound (by
    show (x.num * (y.num * z.den + z.num * y.den)) * ((x.den * y.den) * (x.den * z.den)) =
         ((x.num * y.num) * (x.den * z.den) + (x.num * z.num) * (x.den * y.den)) *
         (x.den * (y.den * z.den))
    comm_ring)
  right_distrib := ind3 fun x y z => Quot.sound (by
    show ((x.num * y.den + y.num * x.den) * z.num) * ((x.den * z.den) * (y.den * z.den)) =
         ((x.num * z.num) * (y.den * z.den) + (y.num * z.num) * (x.den * z.den)) *
         ((x.den * y.den) * z.den)
    comm_ring)

theorem zero_def_mk : (0 : QRat) = mk 0 1 (by decide) := rfl
theorem one_def_mk : (1 : QRat) = mk 1 1 (by decide) := rfl
theorem add_mk (n1 d1 hd1 n2 d2 hd2) :
    mk n1 d1 hd1 + mk n2 d2 hd2 = mk (n1 * d2 + n2 * d1) (d1 * d2) (Int.mul_pos hd1 hd2) := rfl
theorem neg_mk (n d hd) : -mk n d hd = mk (-n) d hd := rfl
theorem sub_mk (n1 d1 hd1 n2 d2 hd2) :
    mk n1 d1 hd1 - mk n2 d2 hd2 = mk (n1 * d2 + (-n2) * d1) (d1 * d2) (Int.mul_pos hd1 hd2) := rfl
theorem mul_mk (n1 d1 hd1 n2 d2 hd2) :
    mk n1 d1 hd1 * mk n2 d2 hd2 = mk (n1 * n2) (d1 * d2) (Int.mul_pos hd1 hd2) := rfl

theorem mk_eq {n1 d1 : Int} {hd1 : 0 < d1} {n2 d2 : Int} {hd2 : 0 < d2}
    (h : n1 * d2 = n2 * d1) : mk n1 d1 hd1 = mk n2 d2 hd2 :=
  Quot.sound h

macro "qrat_eq" : tactic =>
  `(tactic| (simp only [QRat.zero_def_mk, QRat.one_def_mk, QRat.add_mk,
                        QRat.neg_mk, QRat.sub_mk, QRat.mul_mk];
             exact QRat.mk_eq (by decide)))

/-- Well-defined boolean zero test on `QRat` for kernel-computable non-equality proofs. -/
def isZero : QRat → Bool :=
  Quot.lift (fun a => a.num == 0) (fun a1 a2 (ha : a1.num * a2.den = a2.num * a1.den) => by
    have hd1 : a1.den ≠ 0 := by have := a1.den_pos; omega
    have hd2 : a2.den ≠ 0 := by have := a2.den_pos; omega
    by_cases h1 : a1.num = 0
    · have h2 : a2.num = 0 := by
        rw [h1, CommRing.zero_mul] at ha
        rcases StrictOrderedCommRing.mul_eq_zero_iff.mp ha.symm with hz | hd
        · exact hz
        · exact absurd hd hd1
      simp [h1, h2]
    · have h2 : a2.num ≠ 0 := by
        intro hz
        rw [hz, CommRing.zero_mul] at ha
        rcases StrictOrderedCommRing.mul_eq_zero_iff.mp ha with hz1 | hd
        · exact h1 hz1
        · exact hd2 hd
      have hb1 : (a1.num == 0) = false := beq_eq_false_iff_ne.mpr h1
      have hb2 : (a2.num == 0) = false := beq_eq_false_iff_ne.mpr h2
      dsimp only []
      rw [hb1, hb2])

theorem ne_of_isZero_sub_false {x y : QRat} (h : isZero (x - y) = false) : x ≠ y := by
  intro heq
  rw [heq, CommRing.sub_self] at h
  contradiction

private theorem le_left_coh (a1 a2 b : PreRat) (ha : PreRat.Equiv a1 a2) :
    (a1.num * b.den ≤ b.num * a1.den) = (a2.num * b.den ≤ b.num * a2.den) := by
  apply propext
  unfold PreRat.Equiv at ha
  have hd1 := a1.den_pos
  have hd2 := a2.den_pos
  constructor
  · intro h1
    have hmul : 0 ≤ (b.num * a1.den - a1.num * b.den) * a2.den :=
      Int.mul_nonneg (by omega) (Int.le_of_lt hd2)
    have hid : (b.num * a1.den - a1.num * b.den) * a2.den =
               (b.num * a2.den - a2.num * b.den) * a1.den := by
      calc
        (b.num * a1.den - a1.num * b.den) * a2.den
          = b.num * a1.den * a2.den - (a1.num * a2.den) * b.den := by comm_ring
        _ = b.num * a1.den * a2.den - (a2.num * a1.den) * b.den := by rw [ha]
        _ = (b.num * a2.den - a2.num * b.den) * a1.den := by comm_ring
    rw [hid] at hmul
    by_cases hle : a2.num * b.den ≤ b.num * a2.den
    · exact hle
    · exfalso
      have hp : 0 < (a2.num * b.den - b.num * a2.den) * a1.den := Int.mul_pos (by omega) hd1
      have hsum : (a2.num * b.den - b.num * a2.den) * a1.den +
                  (b.num * a2.den - a2.num * b.den) * a1.den = 0 := by comm_ring
      omega
  · intro h2
    have hmul : 0 ≤ (b.num * a2.den - a2.num * b.den) * a1.den :=
      Int.mul_nonneg (by omega) (Int.le_of_lt hd1)
    have hid : (b.num * a2.den - a2.num * b.den) * a1.den =
               (b.num * a1.den - a1.num * b.den) * a2.den := by
      calc
        (b.num * a2.den - a2.num * b.den) * a1.den
          = b.num * a2.den * a1.den - (a2.num * a1.den) * b.den := by comm_ring
        _ = b.num * a2.den * a1.den - (a1.num * a2.den) * b.den := by rw [ha]
        _ = (b.num * a1.den - a1.num * b.den) * a2.den := by comm_ring
    rw [hid] at hmul
    by_cases hle : a1.num * b.den ≤ b.num * a1.den
    · exact hle
    · exfalso
      have hp : 0 < (a1.num * b.den - b.num * a1.den) * a2.den := Int.mul_pos (by omega) hd2
      have hsum : (a1.num * b.den - b.num * a1.den) * a2.den +
                  (b.num * a1.den - a1.num * b.den) * a2.den = 0 := by comm_ring
      omega

private theorem le_right_coh (a b1 b2 : PreRat) (hb : PreRat.Equiv b1 b2) :
    (a.num * b1.den ≤ b1.num * a.den) = (a.num * b2.den ≤ b2.num * a.den) := by
  apply propext
  unfold PreRat.Equiv at hb
  have hd1 := b1.den_pos
  have hd2 := b2.den_pos
  constructor
  · intro h1
    have hmul : 0 ≤ (b1.num * a.den - a.num * b1.den) * b2.den :=
      Int.mul_nonneg (by omega) (Int.le_of_lt hd2)
    have hid : (b1.num * a.den - a.num * b1.den) * b2.den =
               (b2.num * a.den - a.num * b2.den) * b1.den := by
      calc
        (b1.num * a.den - a.num * b1.den) * b2.den
          = (b1.num * b2.den) * a.den - a.num * b1.den * b2.den := by comm_ring
        _ = (b2.num * b1.den) * a.den - a.num * b1.den * b2.den := by rw [hb]
        _ = (b2.num * a.den - a.num * b2.den) * b1.den := by comm_ring
    rw [hid] at hmul
    by_cases hle : a.num * b2.den ≤ b2.num * a.den
    · exact hle
    · exfalso
      have hp : 0 < (a.num * b2.den - b2.num * a.den) * b1.den := Int.mul_pos (by omega) hd1
      have hsum : (a.num * b2.den - b2.num * a.den) * b1.den +
                  (b2.num * a.den - a.num * b2.den) * b1.den = 0 := by comm_ring
      omega
  · intro h2
    have hmul : 0 ≤ (b2.num * a.den - a.num * b2.den) * b1.den :=
      Int.mul_nonneg (by omega) (Int.le_of_lt hd1)
    have hid : (b2.num * a.den - a.num * b2.den) * b1.den =
               (b1.num * a.den - a.num * b1.den) * b2.den := by
      calc
        (b2.num * a.den - a.num * b2.den) * b1.den
          = (b2.num * b1.den) * a.den - a.num * b2.den * b1.den := by comm_ring
        _ = (b1.num * b2.den) * a.den - a.num * b2.den * b1.den := by rw [hb]
        _ = (b1.num * a.den - a.num * b1.den) * b2.den := by comm_ring
    rw [hid] at hmul
    by_cases hle : a.num * b1.den ≤ b1.num * a.den
    · exact hle
    · exfalso
      have hp : 0 < (a.num * b1.den - b1.num * a.den) * b2.den := Int.mul_pos (by omega) hd2
      have hsum : (a.num * b1.den - b1.num * a.den) * b2.den +
                  (b1.num * a.den - a.num * b1.den) * b2.den = 0 := by comm_ring
      omega

def le : QRat → QRat → Prop :=
  lift2_helper (fun a b => a.num * b.den ≤ b.num * a.den) le_left_coh le_right_coh

def lt (x y : QRat) : Prop := le x y ∧ ¬ le y x

instance : LE QRat := ⟨le⟩
instance : LT QRat := ⟨lt⟩

instance : StrictOrderedCommRing QRat where
  zero_lt_one := ⟨by show (0 : Int) * 1 ≤ 1 * 1; decide, by show ¬ ((1 : Int) * 1 ≤ 0 * 1); decide⟩
  le_refl := ind1 fun x => Int.le_refl (x.num * x.den)
  le_trans := ind3 fun x y z => by
    intro (hab : x.num * y.den ≤ y.num * x.den) (hbc : y.num * z.den ≤ z.num * y.den)
    show x.num * z.den ≤ z.num * x.den
    have hy := y.den_pos
    have h1 : 0 ≤ (y.num * x.den - x.num * y.den) * z.den :=
      Int.mul_nonneg (by omega) (Int.le_of_lt z.den_pos)
    have h2 : 0 ≤ (z.num * y.den - y.num * z.den) * x.den :=
      Int.mul_nonneg (by omega) (Int.le_of_lt x.den_pos)
    have hsum : (y.num * x.den - x.num * y.den) * z.den +
                (z.num * y.den - y.num * z.den) * x.den =
                (z.num * x.den - x.num * z.den) * y.den := by comm_ring
    have hprod : 0 ≤ (z.num * x.den - x.num * z.den) * y.den := by omega
    by_cases hxz : x.num * z.den ≤ z.num * x.den
    · exact hxz
    · exfalso
      have hp : 0 < (x.num * z.den - z.num * x.den) * y.den := Int.mul_pos (by omega) hy
      have hz0 : (x.num * z.den - z.num * x.den) * y.den +
                 (z.num * x.den - x.num * z.den) * y.den = 0 := by comm_ring
      omega
  le_antisymm := ind2 fun x y => by
    intro (hab : x.num * y.den ≤ y.num * x.den) (hba : y.num * x.den ≤ x.num * y.den)
    exact Quot.sound (by show x.num * y.den = y.num * x.den; omega)
  le_total := ind2 fun x y => Int.le_total (x.num * y.den) (y.num * x.den)
  lt_iff_le_not_le _ _ := Iff.rfl
  add_le_add_left := ind2 fun x y => by
    intro (hab : x.num * y.den ≤ y.num * x.den) c
    refine ind1 (P := fun u => u + Quot.mk PreRat.Equiv x ≤ u + Quot.mk PreRat.Equiv y)
      (fun z => ?_) c
    show (z.num * x.den + x.num * z.den) * (z.den * y.den) ≤
         (z.num * y.den + y.num * z.den) * (z.den * x.den)
    have hdiff : 0 ≤ (y.num * x.den - x.num * y.den) * (z.den * z.den) :=
      Int.mul_nonneg (by omega) (Int.mul_nonneg (Int.le_of_lt z.den_pos) (Int.le_of_lt z.den_pos))
    have hid : (z.num * y.den + y.num * z.den) * (z.den * x.den) -
               (z.num * x.den + x.num * z.den) * (z.den * y.den) =
               (y.num * x.den - x.num * y.den) * (z.den * z.den) := by comm_ring
    omega
  mul_pos := ind2 fun x y => by
    rintro ⟨hxa, hxn⟩ ⟨hyb, hyn⟩
    have hxpos : 0 < x.num := by
      change (0 : Int) * x.den ≤ x.num * 1 at hxa
      change ¬ (x.num * (1 : Int) ≤ 0 * x.den) at hxn
      omega
    have hypos : 0 < y.num := by
      change (0 : Int) * y.den ≤ y.num * 1 at hyb
      change ¬ (y.num * (1 : Int) ≤ 0 * y.den) at hyn
      omega
    have hxy : 0 < x.num * y.num := Int.mul_pos hxpos hypos
    constructor
    · show (0 : Int) * (x.den * y.den) ≤ (x.num * y.num) * 1
      have h0 : (0 : Int) * (x.den * y.den) = 0 := by comm_ring
      omega
    · show ¬ ((x.num * y.num) * (1 : Int) ≤ 0 * (x.den * y.den))
      have h0 : (0 : Int) * (x.den * y.den) = 0 := by comm_ring
      omega

end QRat

/-! ## Concrete Instance 3: Quadratic Field `QSqrt2` (`ℚ[√2]`) -/

/-- Exact elements `re + im · √2` over `QRat` (`ℚ[√2]`), containing `1/√2 = (1/2)√2`. -/
structure QSqrt2 where
  re : QRat
  im : QRat

namespace QSqrt2

@[ext]
theorem ext {x y : QSqrt2} (hre : x.re = y.re) (him : x.im = y.im) : x = y := by
  cases x; cases y; simp_all

def ofRat (q : QRat) : QSqrt2 := ⟨q, 0⟩

instance : OfNat QSqrt2 0 := ⟨⟨0, 0⟩⟩
instance : OfNat QSqrt2 1 := ⟨⟨1, 0⟩⟩

instance : Add QSqrt2 := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg QSqrt2 := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance : Sub QSqrt2 := ⟨fun x y => ⟨x.re - y.re, x.im - y.im⟩⟩
instance : Mul QSqrt2 := ⟨fun x y =>
  ⟨x.re * y.re + (1 + 1) * x.im * y.im, x.re * y.im + x.im * y.re⟩⟩

@[simp] theorem zero_re : (0 : QSqrt2).re = 0 := rfl
@[simp] theorem zero_im : (0 : QSqrt2).im = 0 := rfl
@[simp] theorem one_re : (1 : QSqrt2).re = 1 := rfl
@[simp] theorem one_im : (1 : QSqrt2).im = 0 := rfl
@[simp] theorem add_re (x y : QSqrt2) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : QSqrt2) : (x + y).im = x.im + y.im := rfl
@[simp] theorem neg_re (x : QSqrt2) : (-x).re = -x.re := rfl
@[simp] theorem neg_im (x : QSqrt2) : (-x).im = -x.im := rfl
@[simp] theorem sub_re (x y : QSqrt2) : (x - y).re = x.re - y.re := rfl
@[simp] theorem sub_im (x y : QSqrt2) : (x - y).im = x.im - y.im := rfl
@[simp] theorem mul_re (x y : QSqrt2) : (x * y).re = x.re * y.re + (1 + 1) * x.im * y.im := rfl
@[simp] theorem mul_im (x y : QSqrt2) : (x * y).im = x.re * y.im + x.im * y.re := rfl

instance : CommRing QSqrt2 where
  zero := 0
  one := 1
  add_assoc a b c := by ext <;> simp <;> comm_ring
  add_comm a b := by ext <;> simp <;> comm_ring
  zero_add a := by ext <;> simp <;> comm_ring
  add_zero a := by ext <;> simp <;> comm_ring
  add_left_neg a := by ext <;> simp <;> comm_ring
  sub_eq_add_neg a b := by ext <;> simp <;> comm_ring
  mul_assoc a b c := by ext <;> simp <;> comm_ring
  mul_comm a b := by ext <;> simp <;> comm_ring
  one_mul a := by ext <;> simp <;> comm_ring
  mul_one a := by ext <;> simp <;> comm_ring
  left_distrib a b c := by ext <;> simp <;> comm_ring
  right_distrib a b c := by ext <;> simp <;> comm_ring

/-- Exact `1 / √2 = (1/2) · √2` in `ℚ[√2]`. -/
def invSqrt2 : QSqrt2 := ⟨0, QRat.mk 1 2⟩

theorem invSqrt2_sq : invSqrt2 * invSqrt2 = ⟨QRat.mk 1 2, 0⟩ := by
  ext <;> dsimp [invSqrt2, HMul.hMul, Mul.mul] <;> qrat_eq

theorem two_mul_invSqrt2_sq : ((1 : QSqrt2) + 1) * (invSqrt2 * invSqrt2) = 1 := by
  rw [invSqrt2_sq]
  ext <;> dsimp [HAdd.hAdd, Add.add, HMul.hMul, Mul.mul] <;> qrat_eq

end QSqrt2

end Conjecture00000007607
