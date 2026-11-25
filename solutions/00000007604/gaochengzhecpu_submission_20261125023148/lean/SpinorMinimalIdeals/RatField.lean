/-
  SpinorMinimalIdeals/RatField.lean
  Exact field of rational numbers `RatQ` constructed in Core Lean 4.19.0,
  together with:
    1. Complete field axioms (`0 ≠ 1`, `2 ≠ 0`, `a * a⁻¹ = 1`),
    2. Four-square anisotropy (`a² + b² + c² + d² = 0 → a = b = c = d = 0`),
    3. Irrationality / non-square theorem for odd powers of two `2^(2m+1)`
       over both `Nat` and `RatQ` (ruling out `dim S = 2^(n/2)` for all odd `n`),
    4. Verified polynomial normalizer lifting `PExpr` directly to `RatQ`.
-/

import SpinorMinimalIdeals.PolyNorm

namespace SpinorMinimalIdeals

open PolyNorm

/-! ### Elementary Integer Order & Parity Lemmas -/

theorem int_sq_nonneg (a : Int) : 0 ≤ a * a := by
  cases Int.le_total 0 a with
  | inl h => exact Int.mul_nonneg h h
  | inr h =>
    have hneg : 0 ≤ -a := by omega
    have hm : (-a) * (-a) = a * a :=
      PExpr.eq_of_norm_eq [a] (.mul (.neg (.var 0)) (.neg (.var 0))) (.mul (.var 0) (.var 0)) (by decide)
    rw [← hm]
    exact Int.mul_nonneg hneg hneg

theorem int_mul_pos_of_pos {a b : Int} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  have h1 : 0 ≤ (a - 1) * (b - 1) := by
    apply Int.mul_nonneg <;> omega
  have h2 : a * b = (a - 1) * (b - 1) + a + b - 1 :=
    PExpr.eq_of_norm_eq [a, b]
      (.mul (.var 0) (.var 1))
      (.sub (.add (.add (.mul (.sub (.var 0) (.const 1)) (.sub (.var 1) (.const 1))) (.var 0)) (.var 1))
            (.const 1)) (by decide)
  omega

theorem int_cancel_right_pos {a b c : Int} (hc : 0 < c) (h : a * c = b * c) : a = b := by
  have hsub : (a - b) * c = 0 := by
    have hid : (a - b) * c = a * c - b * c :=
      PExpr.eq_of_norm_eq [a, b, c]
        (.mul (.sub (.var 0) (.var 1)) (.var 2))
        (.sub (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2))) (by decide)
    omega
  cases Int.mul_eq_zero.mp hsub with
  | inl hab => omega
  | inr hc0 => omega

theorem int_four_sq_eq_zero {a b c d : Int}
    (h : a * a + b * b + c * c + d * d = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have ha := int_sq_nonneg a
  have hb := int_sq_nonneg b
  have hc := int_sq_nonneg c
  have hd := int_sq_nonneg d
  have ha0 : a * a = 0 := by omega
  have hb0 : b * b = 0 := by omega
  have hc0 : c * c = 0 := by omega
  have hd0 : d * d = 0 := by omega
  exact ⟨(Int.mul_eq_zero.mp ha0).elim id id,
         (Int.mul_eq_zero.mp hb0).elim id id,
         (Int.mul_eq_zero.mp hc0).elim id id,
         (Int.mul_eq_zero.mp hd0).elim id id⟩

theorem int_natAbs_sq (z : Int) : ((z.natAbs * z.natAbs : Nat) : Int) = z * z := by
  cases z with
  | ofNat n =>
    simp only [Int.natAbs]
    exact Int.natCast_mul n n
  | negSucc n =>
    simp only [Int.natAbs]
    rw [Int.natCast_mul]
    have hneg : Int.negSucc n = - ((n + 1 : Nat) : Int) := rfl
    rw [hneg]
    exact PExpr.eq_of_norm_eq [((n + 1 : Nat) : Int)]
      (.mul (.var 0) (.var 0)) (.mul (.neg (.var 0)) (.neg (.var 0))) (by decide)

/-! ### Odd-Dimension Arithmetic Obstruction: `2^(2m+1)` Is Never a Square -/

theorem nat_sq_even_imp_even (d : Nat) (h : (d * d) % 2 = 0) : d % 2 = 0 := by
  have hrem : d % 2 = 0 ∨ d % 2 = 1 := by omega
  cases hrem with
  | inl h0 => exact h0
  | inr h1 =>
    let q : Int := (d / 2 : Int)
    have hd : (d : Int) = 2 * q + 1 := by omega
    have hid : (2 * q + 1) * (2 * q + 1) = 4 * (q * q + q) + 1 :=
      PExpr.eq_of_norm_eq [q]
        (.mul (.add (.mul (.const 2) (.var 0)) (.const 1))
              (.add (.mul (.const 2) (.var 0)) (.const 1)))
        (.add (.mul (.const 4) (.add (.mul (.var 0) (.var 0)) (.var 0))) (.const 1)) (by decide)
    have hcast : ((d * d : Nat) : Int) = 4 * (q * q + q) + 1 := by
      rw [Int.natCast_mul, hd, hid]
    omega

theorem no_nat_sq_eq_two_mul_sq : ∀ (b a : Nat), 0 < b → a * a ≠ 2 * (b * b) := by
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a hb heq
    have ha_even : a % 2 = 0 := nat_sq_even_imp_even a (by omega)
    let a' := a / 2
    have h4 : 4 * (a' * a') = 2 * (b * b) := by
      have ha_int : (a : Int) * (a : Int) = 4 * ((a' : Int) * (a' : Int)) := by
        have h2 : (a : Int) = 2 * (a' : Int) := by omega
        rw [h2]
        exact PExpr.eq_of_norm_eq [(a' : Int)]
          (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0)))
          (.mul (.const 4) (.mul (.var 0) (.var 0))) (by decide)
      have hc1 : ((a * a : Nat) : Int) = (a : Int) * (a : Int) := Int.natCast_mul a a
      have hc2 : ((4 * (a' * a') : Nat) : Int) = 4 * ((a' : Int) * (a' : Int)) := by
        simp [Int.natCast_mul]
      omega
    have hb_sq : b * b = 2 * (a' * a') := by omega
    have hb_sq_pos : 0 < b * b := Nat.mul_pos hb hb
    have ha'_pos : 0 < a' := by
      cases Nat.eq_zero_or_pos a' with
      | inl hz => rw [hz] at hb_sq; omega
      | inr hp => exact hp
    have ha'_lt_b : a' < b := by
      cases Nat.lt_or_ge a' b with
      | inl hlt => exact hlt
      | inr hge =>
        have hmul : b * b ≤ a' * a' := Nat.mul_le_mul hge hge
        omega
    exact ih a' ha'_lt_b b ha'_pos hb_sq

/-- For every `m : Nat`, `2^(2m+1)` is never a rational square `(a/b)^2` (`b > 0`). -/
theorem odd_pow_two_not_rat_num_den (m : Nat) :
    ∀ (a b : Nat), 0 < b → a * a ≠ 2 ^ (2 * m + 1) * (b * b) := by
  induction m with
  | zero =>
    intro a b hb
    simpa using no_nat_sq_eq_two_mul_sq b a hb
  | succ m ih =>
    intro a b hb heq
    have hpow : 2 ^ (2 * (m + 1) + 1) = 4 * 2 ^ (2 * m + 1) := by
      show 2 ^ (2 * m + 3) = 4 * 2 ^ (2 * m + 1)
      rw [Nat.pow_add 2 (2 * m + 1) 2]
      omega
    rw [hpow, Nat.mul_assoc 4 (2 ^ (2 * m + 1)) (b * b)] at heq
    have ha_even : a % 2 = 0 := nat_sq_even_imp_even a (by omega)
    let a' := a / 2
    have h4 : 4 * (a' * a') = 4 * (2 ^ (2 * m + 1) * (b * b)) := by
      have ha_int : (a : Int) * (a : Int) = 4 * ((a' : Int) * (a' : Int)) := by
        have h2 : (a : Int) = 2 * (a' : Int) := by omega
        rw [h2]
        exact PExpr.eq_of_norm_eq [(a' : Int)]
          (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0)))
          (.mul (.const 4) (.mul (.var 0) (.var 0))) (by decide)
      have hc1 : ((a * a : Nat) : Int) = (a : Int) * (a : Int) := Int.natCast_mul a a
      have hc2 : ((4 * (a' * a') : Nat) : Int) = 4 * ((a' : Int) * (a' : Int)) := by
        simp [Int.natCast_mul]
      omega
    have hcancel : a' * a' = 2 ^ (2 * m + 1) * (b * b) := by omega
    exact ih a' b hb hcancel

/-- In every odd dimension `n = 2m + 1`, no natural number `d` satisfies `d^2 = 2^n`. -/
theorem odd_pow_two_not_nat_sq (m d : Nat) : d * d ≠ 2 ^ (2 * m + 1) := by
  intro h
  have h1 : d * d = 2 ^ (2 * m + 1) * (1 * 1) := by omega
  exact odd_pow_two_not_rat_num_den m d 1 (by decide) h1

/-! ### Exact Rational Numbers `RatQ` via Quotient -/

structure RawRat where
  num : Int
  den : Int
  den_pos : 0 < den

namespace RawRat

def Equiv (x y : RawRat) : Prop :=
  x.num * y.den = y.num * x.den

theorem equiv_refl (x : RawRat) : Equiv x x := rfl

theorem equiv_symm {x y : RawRat} (h : Equiv x y) : Equiv y x := h.symm

theorem equiv_trans {x y z : RawRat} (h1 : Equiv x y) (h2 : Equiv y z) : Equiv x z := by
  unfold Equiv at *
  apply int_cancel_right_pos y.den_pos
  have step1 : x.num * z.den * y.den = x.num * y.den * z.den :=
    PExpr.eq_of_norm_eq [x.num, z.den, y.den]
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
  have step2 : y.num * x.den * z.den = y.num * z.den * x.den :=
    PExpr.eq_of_norm_eq [y.num, x.den, z.den]
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
  have step3 : z.num * y.den * x.den = z.num * x.den * y.den :=
    PExpr.eq_of_norm_eq [z.num, y.den, x.den]
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
  rw [step1, h1, step2, h2, step3]

instance setoid : Setoid RawRat where
  r := Equiv
  iseqv := ⟨equiv_refl, equiv_symm, equiv_trans⟩

def add (x y : RawRat) : RawRat :=
  ⟨x.num * y.den + y.num * x.den, x.den * y.den, int_mul_pos_of_pos x.den_pos y.den_pos⟩

def neg (x : RawRat) : RawRat :=
  ⟨-x.num, x.den, x.den_pos⟩

def mul (x y : RawRat) : RawRat :=
  ⟨x.num * y.num, x.den * y.den, int_mul_pos_of_pos x.den_pos y.den_pos⟩

def inv (x : RawRat) : RawRat :=
  if hpos : 0 < x.num then
    ⟨x.den, x.num, hpos⟩
  else if hneg : x.num < 0 then
    ⟨-x.den, -x.num, by omega⟩
  else
    ⟨0, 1, by decide⟩

theorem add_congr {x1 x2 y1 y2 : RawRat} (hx : x1 ≈ x2) (hy : y1 ≈ y2) :
    add x1 y1 ≈ add x2 y2 := by
  change (x1.num * y1.den + y1.num * x1.den) * (x2.den * y2.den) =
         (x2.num * y2.den + y2.num * x2.den) * (x1.den * y1.den)
  have hx' : x1.num * x2.den = x2.num * x1.den := hx
  have hy' : y1.num * y2.den = y2.num * y1.den := hy
  have lhs_eq : (x1.num * y1.den + y1.num * x1.den) * (x2.den * y2.den) =
      (x1.num * x2.den) * (y1.den * y2.den) + (y1.num * y2.den) * (x1.den * x2.den) :=
    PExpr.eq_of_norm_eq [x1.num, y1.den, y1.num, x1.den, x2.den, y2.den]
      (.mul (.add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))) (.mul (.var 4) (.var 5)))
      (.add (.mul (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 5)))
            (.mul (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 4)))) (by decide)
  have rhs_eq : (x2.num * y2.den + y2.num * x2.den) * (x1.den * y1.den) =
      (x2.num * x1.den) * (y1.den * y2.den) + (y2.num * y1.den) * (x1.den * x2.den) :=
    PExpr.eq_of_norm_eq [x2.num, y2.den, y2.num, x2.den, x1.den, y1.den]
      (.mul (.add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))) (.mul (.var 4) (.var 5)))
      (.add (.mul (.mul (.var 0) (.var 4)) (.mul (.var 5) (.var 1)))
            (.mul (.mul (.var 2) (.var 5)) (.mul (.var 4) (.var 3)))) (by decide)
  rw [lhs_eq, hx', hy', rhs_eq]

theorem neg_congr {x1 x2 : RawRat} (hx : x1 ≈ x2) : neg x1 ≈ neg x2 := by
  change (-x1.num) * x2.den = (-x2.num) * x1.den
  have hx' : x1.num * x2.den = x2.num * x1.den := hx
  rw [Int.neg_mul, Int.neg_mul, hx']

theorem mul_congr {x1 x2 y1 y2 : RawRat} (hx : x1 ≈ x2) (hy : y1 ≈ y2) :
    mul x1 y1 ≈ mul x2 y2 := by
  change (x1.num * y1.num) * (x2.den * y2.den) = (x2.num * y2.num) * (x1.den * y1.den)
  have hx' : x1.num * x2.den = x2.num * x1.den := hx
  have hy' : y1.num * y2.den = y2.num * y1.den := hy
  have lhs_eq : (x1.num * y1.num) * (x2.den * y2.den) = (x1.num * x2.den) * (y1.num * y2.den) :=
    PExpr.eq_of_norm_eq [x1.num, y1.num, x2.den, y2.den]
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide)
  have rhs_eq : (x2.num * y2.num) * (x1.den * y1.den) = (x2.num * x1.den) * (y2.num * y1.den) :=
    PExpr.eq_of_norm_eq [x2.num, y2.num, x1.den, y1.den]
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide)
  rw [lhs_eq, hx', hy', rhs_eq]

theorem pos_iff_of_equiv {x y : RawRat} (h : x ≈ y) : 0 < x.num ↔ 0 < y.num := by
  have h' : x.num * y.den = y.num * x.den := h
  constructor
  · intro hxpos
    have hprod : 0 < y.num * x.den := by
      rw [← h']
      exact int_mul_pos_of_pos hxpos y.den_pos
    cases Int.lt_trichotomy 0 y.num with
    | inl hypos => exact hypos
    | inr hrest =>
      have hy_nonpos : 0 ≤ -y.num := by omega
      have hxd_nonneg : 0 ≤ x.den := by have := x.den_pos; omega
      have hneg_prod : 0 ≤ (-y.num) * x.den := Int.mul_nonneg hy_nonpos hxd_nonneg
      rw [Int.neg_mul] at hneg_prod
      omega
  · intro hypos
    have hprod : 0 < x.num * y.den := by
      rw [h']
      exact int_mul_pos_of_pos hypos x.den_pos
    cases Int.lt_trichotomy 0 x.num with
    | inl hxpos => exact hxpos
    | inr hrest =>
      have hx_nonpos : 0 ≤ -x.num := by omega
      have hyd_nonneg : 0 ≤ y.den := by have := y.den_pos; omega
      have hneg_prod : 0 ≤ (-x.num) * y.den := Int.mul_nonneg hx_nonpos hyd_nonneg
      rw [Int.neg_mul] at hneg_prod
      omega

theorem neg_iff_of_equiv {x y : RawRat} (h : x ≈ y) : x.num < 0 ↔ y.num < 0 := by
  have hneg : neg x ≈ neg y := neg_congr h
  have hpos := pos_iff_of_equiv hneg
  simp only [neg] at hpos
  omega

theorem inv_congr {x y : RawRat} (h : x ≈ y) : inv x ≈ inv y := by
  have h' : x.num * y.den = y.num * x.den := h
  have hpos_iff := pos_iff_of_equiv h
  have hneg_iff := neg_iff_of_equiv h
  unfold inv
  by_cases hxpos : 0 < x.num
  · have hypos : 0 < y.num := hpos_iff.mp hxpos
    simp only [dif_pos hxpos, dif_pos hypos]
    change x.den * y.num = y.den * x.num
    have c1 : x.den * y.num = y.num * x.den := Int.mul_comm _ _
    have c2 : y.den * x.num = x.num * y.den := Int.mul_comm _ _
    rw [c1, c2, h']
  · have hypos : ¬ (0 < y.num) := fun hy => hxpos (hpos_iff.mpr hy)
    simp only [dif_neg hxpos, dif_neg hypos]
    by_cases hxneg : x.num < 0
    · have hyneg : y.num < 0 := hneg_iff.mp hxneg
      simp only [dif_pos hxneg, dif_pos hyneg]
      change (-x.den) * (-y.num) = (-y.den) * (-x.num)
      have c1 : (-x.den) * (-y.num) = y.num * x.den :=
        PExpr.eq_of_norm_eq [x.den, y.num]
          (.mul (.neg (.var 0)) (.neg (.var 1))) (.mul (.var 1) (.var 0)) (by decide)
      have c2 : (-y.den) * (-x.num) = x.num * y.den :=
        PExpr.eq_of_norm_eq [y.den, x.num]
          (.mul (.neg (.var 0)) (.neg (.var 1))) (.mul (.var 1) (.var 0)) (by decide)
      rw [c1, c2, h']
    · have hyneg : ¬ (y.num < 0) := fun hy => hxneg (hneg_iff.mpr hy)
      simp only [dif_neg hxneg, dif_neg hyneg]
      rfl

end RawRat

/-- The exact field of rational numbers `ℚ`. -/
abbrev RatQ := Quotient RawRat.setoid

/-- Lightweight inverse typeclass for Core Lean 4.19.0. -/
class HasInv (α : Type) where
  inv : α → α

postfix:max "⁻¹" => HasInv.inv

namespace RatQ

def ofInt (n : Int) : RatQ := Quotient.mk _ ⟨n, 1, by decide⟩
def ofNat (n : Nat) : RatQ := ofInt (n : Int)
def mkRat (n d : Int) (hd : 0 < d) : RatQ := Quotient.mk _ ⟨n, d, hd⟩

instance (n : Nat) : OfNat RatQ n := ⟨ofNat n⟩

def add : RatQ → RatQ → RatQ :=
  Quotient.lift₂ (fun x y => Quotient.mk _ (RawRat.add x y))
    (fun _ _ _ _ hx hy => Quotient.sound (RawRat.add_congr hx hy))

def neg : RatQ → RatQ :=
  Quotient.lift (fun x => Quotient.mk _ (RawRat.neg x))
    (fun _ _ hx => Quotient.sound (RawRat.neg_congr hx))

def sub (a b : RatQ) : RatQ := add a (neg b)

def mul : RatQ → RatQ → RatQ :=
  Quotient.lift₂ (fun x y => Quotient.mk _ (RawRat.mul x y))
    (fun _ _ _ _ hx hy => Quotient.sound (RawRat.mul_congr hx hy))

def inv : RatQ → RatQ :=
  Quotient.lift (fun x => Quotient.mk _ (RawRat.inv x))
    (fun _ _ hx => Quotient.sound (RawRat.inv_congr hx))

def div (a b : RatQ) : RatQ := mul a (inv b)

instance : Add RatQ := ⟨add⟩
instance : Neg RatQ := ⟨neg⟩
instance : Sub RatQ := ⟨sub⟩
instance : Mul RatQ := ⟨mul⟩
instance : HasInv RatQ := ⟨inv⟩
instance : Div RatQ := ⟨div⟩

def half : RatQ := mkRat 1 2 (by decide)

instance : DecidableEq RatQ :=
  fun a b => Quotient.recOnSubsingleton₂ a b fun x y =>
    if h : x.num * y.den = y.num * x.den then
      isTrue (Quotient.sound h)
    else
      isFalse (fun heq => h (Quotient.exact heq))

/-! ### Field Laws for `RatQ` -/

theorem add_assoc (a b c : RatQ) : a + b + c = a + (b + c) := by
  induction a using Quotient.ind; next x =>
  induction b using Quotient.ind; next y =>
  induction c using Quotient.ind; next z =>
  apply Quotient.sound
  change ((x.num * y.den + y.num * x.den) * z.den + z.num * (x.den * y.den)) * (x.den * (y.den * z.den)) =
         (x.num * (y.den * z.den) + (y.num * z.den + z.num * y.den) * x.den) * (x.den * y.den * z.den)
  exact PExpr.eq_of_norm_eq [x.num, x.den, y.num, y.den, z.num, z.den]
    (.mul (.add (.mul (.add (.mul (.var 0) (.var 3)) (.mul (.var 2) (.var 1))) (.var 5))
                (.mul (.var 4) (.mul (.var 1) (.var 3))))
          (.mul (.var 1) (.mul (.var 3) (.var 5))))
    (.mul (.add (.mul (.var 0) (.mul (.var 3) (.var 5)))
                (.mul (.add (.mul (.var 2) (.var 5)) (.mul (.var 4) (.var 3))) (.var 1)))
          (.mul (.mul (.var 1) (.var 3)) (.var 5))) (by decide)

theorem add_comm (a b : RatQ) : a + b = b + a := by
  induction a using Quotient.ind; next x =>
  induction b using Quotient.ind; next y =>
  apply Quotient.sound
  change (x.num * y.den + y.num * x.den) * (y.den * x.den) =
         (y.num * x.den + x.num * y.den) * (x.den * y.den)
  exact PExpr.eq_of_norm_eq [x.num, x.den, y.num, y.den]
    (.mul (.add (.mul (.var 0) (.var 3)) (.mul (.var 2) (.var 1))) (.mul (.var 3) (.var 1)))
    (.mul (.add (.mul (.var 2) (.var 1)) (.mul (.var 0) (.var 3))) (.mul (.var 1) (.var 3))) (by decide)

theorem zero_add (a : RatQ) : 0 + a = a := by
  induction a using Quotient.ind; next x =>
  apply Quotient.sound
  change (0 * x.den + x.num * 1) * x.den = x.num * (1 * x.den)
  exact PExpr.eq_of_norm_eq [x.num, x.den]
    (.mul (.add (.mul (.const 0) (.var 1)) (.mul (.var 0) (.const 1))) (.var 1))
    (.mul (.var 0) (.mul (.const 1) (.var 1))) (by decide)

theorem add_zero (a : RatQ) : a + 0 = a := by
  rw [add_comm, zero_add]

theorem neg_add_cancel (a : RatQ) : -a + a = 0 := by
  induction a using Quotient.ind; next x =>
  apply Quotient.sound
  change ((-x.num) * x.den + x.num * x.den) * 1 = 0 * (x.den * x.den)
  exact PExpr.eq_of_norm_eq [x.num, x.den]
    (.mul (.add (.mul (.neg (.var 0)) (.var 1)) (.mul (.var 0) (.var 1))) (.const 1))
    (.mul (.const 0) (.mul (.var 1) (.var 1))) (by decide)

theorem add_neg_cancel (a : RatQ) : a + (-a) = 0 := by
  rw [add_comm, neg_add_cancel]

theorem sub_eq_add_neg (a b : RatQ) : a - b = a + (-b) := rfl

theorem mul_assoc (a b c : RatQ) : a * b * c = a * (b * c) := by
  induction a using Quotient.ind; next x =>
  induction b using Quotient.ind; next y =>
  induction c using Quotient.ind; next z =>
  apply Quotient.sound
  change (x.num * y.num * z.num) * (x.den * (y.den * z.den)) =
         (x.num * (y.num * z.num)) * (x.den * y.den * z.den)
  exact PExpr.eq_of_norm_eq [x.num, x.den, y.num, y.den, z.num, z.den]
    (.mul (.mul (.mul (.var 0) (.var 2)) (.var 4)) (.mul (.var 1) (.mul (.var 3) (.var 5))))
    (.mul (.mul (.var 0) (.mul (.var 2) (.var 4))) (.mul (.mul (.var 1) (.var 3)) (.var 5))) (by decide)

theorem mul_comm (a b : RatQ) : a * b = b * a := by
  induction a using Quotient.ind; next x =>
  induction b using Quotient.ind; next y =>
  apply Quotient.sound
  change (x.num * y.num) * (y.den * x.den) = (y.num * x.num) * (x.den * y.den)
  exact PExpr.eq_of_norm_eq [x.num, x.den, y.num, y.den]
    (.mul (.mul (.var 0) (.var 2)) (.mul (.var 3) (.var 1)))
    (.mul (.mul (.var 2) (.var 0)) (.mul (.var 1) (.var 3))) (by decide)

theorem one_mul (a : RatQ) : 1 * a = a := by
  induction a using Quotient.ind; next x =>
  apply Quotient.sound
  change (1 * x.num) * x.den = x.num * (1 * x.den)
  exact PExpr.eq_of_norm_eq [x.num, x.den]
    (.mul (.mul (.const 1) (.var 0)) (.var 1))
    (.mul (.var 0) (.mul (.const 1) (.var 1))) (by decide)

theorem mul_one (a : RatQ) : a * 1 = a := by
  rw [mul_comm, one_mul]

theorem zero_mul (a : RatQ) : 0 * a = 0 := by
  induction a using Quotient.ind; next x =>
  apply Quotient.sound
  change (0 * x.num) * 1 = 0 * (1 * x.den)
  exact PExpr.eq_of_norm_eq [x.num, x.den]
    (.mul (.mul (.const 0) (.var 0)) (.const 1))
    (.mul (.const 0) (.mul (.const 1) (.var 1))) (by decide)

theorem mul_zero (a : RatQ) : a * 0 = 0 := by
  rw [mul_comm, zero_mul]

theorem left_distrib (a b c : RatQ) : a * (b + c) = a * b + a * c := by
  induction a using Quotient.ind; next x =>
  induction b using Quotient.ind; next y =>
  induction c using Quotient.ind; next z =>
  apply Quotient.sound
  change (x.num * (y.num * z.den + z.num * y.den)) * ((x.den * y.den) * (x.den * z.den)) =
         ((x.num * y.num) * (x.den * z.den) + (x.num * z.num) * (x.den * y.den)) * (x.den * (y.den * z.den))
  exact PExpr.eq_of_norm_eq [x.num, x.den, y.num, y.den, z.num, z.den]
    (.mul (.mul (.var 0) (.add (.mul (.var 2) (.var 5)) (.mul (.var 4) (.var 3))))
          (.mul (.mul (.var 1) (.var 3)) (.mul (.var 1) (.var 5))))
    (.mul (.add (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 5)))
                (.mul (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 3))))
          (.mul (.var 1) (.mul (.var 3) (.var 5)))) (by decide)

theorem right_distrib (a b c : RatQ) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, left_distrib, mul_comm c a, mul_comm c b]

theorem one_ne_zero : (1 : RatQ) ≠ (0 : RatQ) := by decide
theorem two_ne_zero : (1 + 1 : RatQ) ≠ (0 : RatQ) := by decide
theorem half_add_half : half + half = (1 : RatQ) := by decide
theorem two_mul_half : (2 : RatQ) * half = (1 : RatQ) := by decide
theorem half_mul_two : half * (2 : RatQ) = (1 : RatQ) := by decide
theorem half_ne_zero : half ≠ (0 : RatQ) := by decide

theorem mul_inv_cancel {a : RatQ} (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  induction a using Quotient.ind; next x =>
  have hx0 : x.num ≠ 0 := by
    intro hz
    apply ha
    apply Quotient.sound
    change x.num * 1 = 0 * x.den
    omega
  apply Quotient.sound
  unfold RawRat.inv
  by_cases hpos : 0 < x.num
  · simp only [dif_pos hpos]
    change (x.num * x.den) * 1 = 1 * (x.den * x.num)
    exact PExpr.eq_of_norm_eq [x.num, x.den]
      (.mul (.mul (.var 0) (.var 1)) (.const 1))
      (.mul (.const 1) (.mul (.var 1) (.var 0))) (by decide)
  · have hneg : x.num < 0 := by omega
    simp only [dif_neg hpos, dif_pos hneg]
    change (x.num * (-x.den)) * 1 = 1 * (x.den * (-x.num))
    exact PExpr.eq_of_norm_eq [x.num, x.den]
      (.mul (.mul (.var 0) (.neg (.var 1))) (.const 1))
      (.mul (.const 1) (.mul (.var 1) (.neg (.var 0)))) (by decide)

theorem inv_mul_cancel {a : RatQ} (ha : a ≠ 0) : a⁻¹ * a = 1 := by
  rw [mul_comm, mul_inv_cancel ha]

theorem mul_eq_zero {a b : RatQ} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · exact .inl ha
  · right
    have h1 : a⁻¹ * (a * b) = a⁻¹ * 0 := by rw [h]
    rw [← mul_assoc, inv_mul_cancel ha, one_mul, mul_zero] at h1
    exact h1

theorem sub_eq_zero_iff {a b : RatQ} : a - b = 0 ↔ a = b := by
  constructor
  · intro h
    have h2 : (a - b) + b = 0 + b := by rw [h]
    rw [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero, zero_add] at h2
    exact h2
  · intro h
    subst h
    exact add_neg_cancel a

theorem ofInt_zero : ofInt 0 = (0 : RatQ) := rfl
theorem ofInt_one : ofInt 1 = (1 : RatQ) := rfl
theorem ofInt_neg (k : Int) : ofInt (-k) = - ofInt k := rfl

theorem ofInt_add (a b : Int) : ofInt (a + b) = ofInt a + ofInt b := by
  apply Quotient.sound
  change (a + b) * (1 * 1) = (a * 1 + b * 1) * 1
  omega

theorem ofInt_mul (a b : Int) : ofInt (a * b) = ofInt a * ofInt b := by
  apply Quotient.sound
  change (a * b) * (1 * 1) = (a * b) * 1
  omega

/-- Sum of four squares over `ℚ` vanishes iff all four components vanish. -/
theorem four_squares_eq_zero (a b c d : RatQ)
    (h : a * a + b * b + c * c + d * d = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  induction a using Quotient.ind; next ra =>
  induction b using Quotient.ind; next rb =>
  induction c using Quotient.ind; next rc =>
  induction d using Quotient.ind; next rd =>
  have hex : (((RawRat.add (RawRat.add (RawRat.add (RawRat.mul ra ra) (RawRat.mul rb rb))
      (RawRat.mul rc rc)) (RawRat.mul rd rd)).num) * 1 =
      0 * ((RawRat.add (RawRat.add (RawRat.add (RawRat.mul ra ra) (RawRat.mul rb rb))
      (RawRat.mul rc rc)) (RawRat.mul rd rd)).den)) := Quotient.exact h
  let A := ra.num * rb.den * rc.den * rd.den
  let B := rb.num * ra.den * rc.den * rd.den
  let C := rc.num * ra.den * rb.den * rd.den
  let D := rd.num * ra.den * rb.den * rc.den
  have hnum_id : ((RawRat.add (RawRat.add (RawRat.add (RawRat.mul ra ra) (RawRat.mul rb rb))
      (RawRat.mul rc rc)) (RawRat.mul rd rd)).num) =
      A * A + B * B + C * C + D * D := by
    simp only [RawRat.add, RawRat.mul, A, B, C, D]
    exact PExpr.eq_of_norm_eq [ra.num, ra.den, rb.num, rb.den, rc.num, rc.den, rd.num, rd.den]
      (.add
        (.mul
          (.add
            (.mul
              (.add (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))
                    (.mul (.mul (.var 2) (.var 2)) (.mul (.var 1) (.var 1))))
              (.mul (.var 5) (.var 5)))
            (.mul (.mul (.var 4) (.var 4))
                  (.mul (.mul (.var 1) (.var 1)) (.mul (.var 3) (.var 3)))))
          (.mul (.var 7) (.var 7)))
        (.mul (.mul (.var 6) (.var 6))
              (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 3) (.var 3)))
                    (.mul (.var 5) (.var 5)))))
      (.add
        (.add
          (.add
            (.mul (.mul (.mul (.mul (.var 0) (.var 3)) (.var 5)) (.var 7))
                  (.mul (.mul (.mul (.var 0) (.var 3)) (.var 5)) (.var 7)))
            (.mul (.mul (.mul (.mul (.var 2) (.var 1)) (.var 5)) (.var 7))
                  (.mul (.mul (.mul (.var 2) (.var 1)) (.var 5)) (.var 7))))
          (.mul (.mul (.mul (.mul (.var 4) (.var 1)) (.var 3)) (.var 7))
                (.mul (.mul (.mul (.var 4) (.var 1)) (.var 3)) (.var 7))))
        (.mul (.mul (.mul (.mul (.var 6) (.var 1)) (.var 3)) (.var 5))
              (.mul (.mul (.mul (.var 6) (.var 1)) (.var 3)) (.var 5)))) (by decide)
  have hsum0 : A * A + B * B + C * C + D * D = 0 := by
    rw [← hnum_id]
    omega
  have ⟨hA, hB, hC, hD⟩ := int_four_sq_eq_zero hsum0
  have ha0 : ra.num = 0 := by
    have h1 := int_cancel_right_pos rd.den_pos (show ra.num * rb.den * rc.den * rd.den = 0 * rd.den by omega)
    have h2 := int_cancel_right_pos rc.den_pos (show ra.num * rb.den * rc.den = 0 * rc.den by omega)
    exact int_cancel_right_pos rb.den_pos (show ra.num * rb.den = 0 * rb.den by omega)
  have hb0 : rb.num = 0 := by
    have h1 := int_cancel_right_pos rd.den_pos (show rb.num * ra.den * rc.den * rd.den = 0 * rd.den by omega)
    have h2 := int_cancel_right_pos rc.den_pos (show rb.num * ra.den * rc.den = 0 * rc.den by omega)
    exact int_cancel_right_pos ra.den_pos (show rb.num * ra.den = 0 * ra.den by omega)
  have hc0 : rc.num = 0 := by
    have h1 := int_cancel_right_pos rd.den_pos (show rc.num * ra.den * rb.den * rd.den = 0 * rd.den by omega)
    have h2 := int_cancel_right_pos rb.den_pos (show rc.num * ra.den * rb.den = 0 * rb.den by omega)
    exact int_cancel_right_pos ra.den_pos (show rc.num * ra.den = 0 * ra.den by omega)
  have hd0 : rd.num = 0 := by
    have h1 := int_cancel_right_pos rc.den_pos (show rd.num * ra.den * rb.den * rc.den = 0 * rc.den by omega)
    have h2 := int_cancel_right_pos rb.den_pos (show rd.num * ra.den * rb.den = 0 * rb.den by omega)
    exact int_cancel_right_pos ra.den_pos (show rd.num * ra.den = 0 * ra.den by omega)
  refine ⟨Quotient.sound ?_, Quotient.sound ?_, Quotient.sound ?_, Quotient.sound ?_⟩ <;>
    (change _ * 1 = 0 * _; omega)

theorem sq_add_one_ne_zero (a : RatQ) : a * a + 1 ≠ 0 := by
  intro h
  have h4 : a * a + 1 * 1 + 0 * 0 + 0 * 0 = 0 := by
    rw [one_mul, zero_mul, add_zero, add_zero]
    exact h
  have ⟨_, h1, _, _⟩ := four_squares_eq_zero a 1 0 0 h4
  exact one_ne_zero h1

/-- No rational number squares to `2^(2m+1)` for any `m : Nat`. -/
theorem odd_pow_two_not_rat_sq (m : Nat) (q : RatQ) :
    q * q ≠ ofNat (2 ^ (2 * m + 1)) := by
  induction q using Quotient.ind; next rq =>
  intro h
  have hex : (rq.num * rq.num) * 1 = ((2 ^ (2 * m + 1) : Nat) : Int) * (rq.den * rq.den) :=
    Quotient.exact h
  let a := rq.num.natAbs
  let b := rq.den.toNat
  have hb : (b : Int) = rq.den := Int.toNat_of_nonneg (by have := rq.den_pos; omega)
  have hb_pos : 0 < b := by
    have hdp := rq.den_pos
    omega
  have ha_sq : ((a * a : Nat) : Int) = rq.num * rq.num := int_natAbs_sq rq.num
  have hnat_int : ((a * a : Nat) : Int) = ((2 ^ (2 * m + 1) * (b * b) : Nat) : Int) := by
    rw [ha_sq, Int.natCast_mul, Int.natCast_mul, hb]
    omega
  have hnat : a * a = 2 ^ (2 * m + 1) * (b * b) := Int.ofNat.inj hnat_int
  exact odd_pow_two_not_rat_num_den m a b hb_pos hnat

/-! ### Verified Polynomial Normalizer Directly Over `RatQ` -/

private theorem mul_four_swap (u v w z : RatQ) : w * ((u * v) * z) = (u * v) * (w * z) := by
  induction u using Quotient.ind; next ru =>
  induction v using Quotient.ind; next rv =>
  induction w using Quotient.ind; next rw_ =>
  induction z using Quotient.ind; next rz =>
  apply Quotient.sound
  change (rw_.num * (ru.num * rv.num * rz.num)) * ((ru.den * rv.den) * (rw_.den * rz.den)) =
         ((ru.num * rv.num) * (rw_.num * rz.num)) * (rw_.den * (ru.den * rv.den * rz.den))
  exact PExpr.eq_of_norm_eq [ru.num, ru.den, rv.num, rv.den, rw_.num, rw_.den, rz.num, rz.den]
    (.mul (.mul (.var 4) (.mul (.mul (.var 0) (.var 2)) (.var 6)))
          (.mul (.mul (.var 1) (.var 3)) (.mul (.var 5) (.var 7))))
    (.mul (.mul (.mul (.var 0) (.var 2)) (.mul (.var 4) (.var 6)))
          (.mul (.var 5) (.mul (.mul (.var 1) (.var 3)) (.var 7)))) (by decide)

def evalVarQ : List RatQ → Nat → RatQ
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => evalVarQ xs i

def evalMonomQ (env : List RatQ) : List Nat → RatQ
  | [] => 1
  | v :: vs => evalVarQ env v * evalMonomQ env vs

theorem evalMonomQ_insertVar (env : List RatQ) (x : Nat) :
    ∀ (ys : List Nat), evalMonomQ env (insertVar x ys) = evalVarQ env x * evalMonomQ env ys
  | [] => by simp [insertVar, evalMonomQ]
  | y :: ys => by
      simp only [insertVar]
      split
      · simp only [evalMonomQ]
      · simp only [evalMonomQ, evalMonomQ_insertVar env x ys]
        rw [← mul_assoc (evalVarQ env y), mul_comm (evalVarQ env y) (evalVarQ env x), mul_assoc]

theorem evalMonomQ_merge (env : List RatQ) :
    ∀ (m1 m2 : List Nat), evalMonomQ env (mergeMonom m1 m2) = evalMonomQ env m1 * evalMonomQ env m2
  | [], ys => by simp [mergeMonom, evalMonomQ, one_mul]
  | x :: xs, ys => by
      simp only [mergeMonom, evalMonomQ_insertVar, evalMonomQ_merge env xs ys, evalMonomQ, mul_assoc]

def evalPolyQ (env : List RatQ) : Poly → RatQ
  | [] => 0
  | (c, m) :: rest => ofInt c * evalMonomQ env m + evalPolyQ env rest

theorem evalPolyQ_consTerm (env : List RatQ) (c : Int) (m : List Nat) (rest : Poly) :
    evalPolyQ env (consTerm c m rest) = ofInt c * evalMonomQ env m + evalPolyQ env rest := by
  unfold consTerm
  split
  · next h =>
    have hc : c = 0 := (isZeroInt_eq_true_iff c).mp h
    subst hc
    rw [ofInt_zero, zero_mul, zero_add]
  · rfl

theorem evalPolyQ_neg (env : List RatQ) :
    ∀ (p : Poly), evalPolyQ env (negPoly p) = - evalPolyQ env p
  | [] => by
      simp only [negPoly, evalPolyQ]
      decide
  | (c, m) :: rest => by
      simp only [negPoly, evalPolyQ, evalPolyQ_neg env rest, ofInt_neg]
      apply sub_eq_zero_iff.mp
      rw [sub_eq_add_neg]
      have hnegneg : ∀ u : RatQ, -(-u) = u := by
        intro u
        apply sub_eq_zero_iff.mp
        rw [sub_eq_add_neg, neg_add_cancel]
      rw [hnegneg]
      have hcm : (-ofInt c) * evalMonomQ env m + ofInt c * evalMonomQ env m = 0 := by
        rw [← right_distrib, neg_add_cancel, zero_mul]
      rw [add_assoc (-ofInt c * evalMonomQ env m),
          ← add_assoc (-evalPolyQ env rest),
          add_comm (-evalPolyQ env rest) (ofInt c * evalMonomQ env m),
          add_assoc (ofInt c * evalMonomQ env m), neg_add_cancel, add_zero, hcm]

theorem evalPolyQ_insertTerm (env : List RatQ) (c : Int) (m : List Nat) :
    ∀ (p : Poly), evalPolyQ env (insertTerm c m p) = ofInt c * evalMonomQ env m + evalPolyQ env p
  | [] => by rw [insertTerm, evalPolyQ_consTerm]
  | (c2, m2) :: rest => by
      unfold insertTerm
      split
      · rw [evalPolyQ_consTerm]
      · simp only [evalPolyQ, evalPolyQ_insertTerm env c m rest]
        rw [← add_assoc (ofInt c2 * evalMonomQ env m2),
            add_comm (ofInt c2 * evalMonomQ env m2) (ofInt c * evalMonomQ env m),
            add_assoc]
      · next heq =>
        have hm : m = m2 := (cmpMonom_eq_iff m m2).mp heq
        subst hm
        rw [evalPolyQ_consTerm]
        simp only [evalPolyQ, ofInt_add, right_distrib, add_assoc]

theorem evalPolyQ_mulTerm (env : List RatQ) (c : Int) (m : List Nat) :
    ∀ (q : Poly), evalPolyQ env (mulTermPoly c m q) = (ofInt c * evalMonomQ env m) * evalPolyQ env q
  | [] => by simp [mulTermPoly, evalPolyQ, mul_zero]
  | (c2, m2) :: rest => by
      simp only [mulTermPoly, evalPolyQ_insertTerm, evalMonomQ_merge,
                 evalPolyQ_mulTerm env c m rest, evalPolyQ, ofInt_mul]
      rw [left_distrib]
      have h : (ofInt c * ofInt c2) * (evalMonomQ env m * evalMonomQ env m2) =
          (ofInt c * evalMonomQ env m) * (ofInt c2 * evalMonomQ env m2) := by
        rw [mul_assoc (ofInt c), ← mul_assoc (ofInt c2),
            mul_comm (ofInt c2) (evalMonomQ env m),
            mul_assoc (evalMonomQ env m), ← mul_assoc (ofInt c)]
      rw [h]

theorem evalPolyQ_addFast (env : List RatQ) :
    ∀ (p q : Poly), evalPolyQ env (addPolyFast p q) = evalPolyQ env p + evalPolyQ env q
  | [], q => by simp [addPolyFast, evalPolyQ, zero_add]
  | (c, m) :: rest, q => by
      simp only [addPolyFast, evalPolyQ_insertTerm, evalPolyQ_addFast env rest q, evalPolyQ, add_assoc]

theorem evalPolyQ_mulFast (env : List RatQ) :
    ∀ (p q : Poly), evalPolyQ env (mulPolyFast p q) = evalPolyQ env p * evalPolyQ env q
  | [], q => by simp [mulPolyFast, evalPolyQ, zero_mul]
  | (c, m) :: rest, q => by
      simp only [mulPolyFast, evalPolyQ_addFast, evalPolyQ_mulTerm,
                 evalPolyQ_mulFast env rest q, evalPolyQ, right_distrib]

def evalExprQ (env : List RatQ) : PExpr → RatQ
  | .const k => ofInt k
  | .var i   => evalVarQ env i
  | .neg a   => - evalExprQ env a
  | .add a b => evalExprQ env a + evalExprQ env b
  | .sub a b => evalExprQ env a - evalExprQ env b
  | .mul a b => evalExprQ env a * evalExprQ env b

theorem evalExprQ_norm (env : List RatQ) : ∀ (e : PExpr), evalPolyQ env e.norm = evalExprQ env e
  | .const k => by
      simp only [PExpr.norm, evalPolyQ_consTerm, evalMonomQ, evalPolyQ, evalExprQ,
                 mul_one, add_zero]
  | .var i => by
      simp only [PExpr.norm, evalPolyQ, evalMonomQ, evalExprQ,
                 ofInt_one, one_mul, mul_one, add_zero]
  | .neg a => by
      simp only [PExpr.norm, evalPolyQ_neg, evalExprQ_norm env a, evalExprQ]
  | .add a b => by
      simp only [PExpr.norm, evalPolyQ_addFast, evalExprQ_norm env a, evalExprQ_norm env b, evalExprQ]
  | .sub a b => by
      simp only [PExpr.norm, evalPolyQ_addFast, evalPolyQ_neg,
                 evalExprQ_norm env a, evalExprQ_norm env b, evalExprQ, sub_eq_add_neg]
  | .mul a b => by
      simp only [PExpr.norm, evalPolyQ_mulFast, evalExprQ_norm env a, evalExprQ_norm env b, evalExprQ]

/-- Master reflection lemma over `RatQ`: if `e1.norm = e2.norm` (by `rfl`), then `evalExprQ` agrees! -/
theorem eqQ_of_norm_eq (env : List RatQ) (e1 e2 : PExpr) (h : e1.norm = e2.norm) :
    evalExprQ env e1 = evalExprQ env e2 := by
  rw [← evalExprQ_norm env e1, ← evalExprQ_norm env e2, h]

end RatQ
end SpinorMinimalIdeals
