/-
Copyright (c) 2026 The Last Math Competition Authors. All rights reserved.
 Concrete ordered-field witness `QField` (`ℚ`, 4-square anisotropic) and
 Master Disproof Theorem for Conjecture 00000007621 (Zero-divisor metric rank-deficit law).
-/
import ZeroDivisorMetricRankDeficit.FiniteFieldCounts

namespace ZeroDivisorMetricRankDeficit

open AssocInvolAlg

/-!
## 1. Concrete 4-Square Anisotropic Field Witness (`QField = ℚ` via Quotient of Formal Fractions)

Over any finite field `𝔽_q`, Lagrange's four-square theorem forces `Cl_{0,2}(𝔽_q) ≅ M₂(𝔽_q)`.
To certify non-vacuously in Core Lean 4 that `IsFourSqAnisotropic K` holds (making `Cl_{0,2}(K) ≅ ℍ_K`
a genuine division algebra with `Z = {0}`), we construct `ℚ` as a `Quotient` of formal fractions
`(num, den)` with `0 < den`.
-/

/-- Formal fraction representative `num / den` with strictly positive integer denominator. -/
structure FracRep where
  num : Int
  den : Int
  den_pos : 0 < den

namespace FracRep

theorem den_ne_zero (x : FracRep) : x.den ≠ 0 := by
  have h := x.den_pos
  omega

def Rel (x y : FracRep) : Prop := x.num * y.den = y.num * x.den

theorem rel_refl (x : FracRep) : Rel x x := rfl

theorem rel_symm {x y : FracRep} (h : Rel x y) : Rel y x := h.symm

theorem int_mul_eq_zero {a b : Int} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    by_cases hb : b = 0
    · exact hb
    · exfalso
      have hCases : (0 < a ∨ a < 0) ∧ (0 < b ∨ b < 0) := by omega
      rcases hCases with ⟨haP | haN, hbP | hbN⟩
      · have hp := Int.mul_pos haP hbP; omega
      · have hp := Int.mul_pos haP (show 0 < -b by omega)
        rw [Int.mul_neg] at hp; omega
      · have hp := Int.mul_pos (show 0 < -a by omega) hbP
        rw [Int.neg_mul] at hp; omega
      · have hp := Int.mul_pos (show 0 < -a by omega) (show 0 < -b by omega)
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg] at hp; omega

theorem int_mul_right_cancel {a b c : Int} (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  have hDiff : (a - b) * c = 0 := by
    rw [Int.sub_mul, h, Int.sub_self]
  rcases int_mul_eq_zero hDiff with hab | hcZ
  · omega
  · exact False.elim (hc hcZ)

theorem rel_trans {x y z : FracRep} (hxy : Rel x y) (hyz : Rel y z) : Rel x z := by
  dsimp only [Rel] at *
  apply int_mul_right_cancel (den_ne_zero y)
  calc
    (x.num * z.den) * y.den
      = (x.num * y.den) * z.den := by
          rw [Int.mul_assoc x.num z.den y.den, Int.mul_comm z.den y.den,
              ← Int.mul_assoc x.num y.den z.den]
    _ = (y.num * x.den) * z.den := by rw [hxy]
    _ = (y.num * z.den) * x.den := by
          rw [Int.mul_assoc y.num x.den z.den, Int.mul_comm x.den z.den,
              ← Int.mul_assoc y.num z.den x.den]
    _ = (z.num * y.den) * x.den := by rw [hyz]
    _ = (z.num * x.den) * y.den := by
          rw [Int.mul_assoc z.num y.den x.den, Int.mul_comm y.den x.den,
              ← Int.mul_assoc z.num x.den y.den]

def zero : FracRep := ⟨0, 1, by decide⟩
def one : FracRep := ⟨1, 1, by decide⟩

def add (x y : FracRep) : FracRep :=
  ⟨x.num * y.den + y.num * x.den, x.den * y.den, Int.mul_pos x.den_pos y.den_pos⟩

def neg (x : FracRep) : FracRep :=
  ⟨-x.num, x.den, x.den_pos⟩

def mul (x y : FracRep) : FracRep :=
  ⟨x.num * y.num, x.den * y.den, Int.mul_pos x.den_pos y.den_pos⟩

def inv (x : FracRep) : FracRep :=
  if hPos : 0 < x.num then ⟨x.den, x.num, hPos⟩
  else if hNeg : x.num < 0 then ⟨-x.den, -x.num, by omega⟩
  else zero

theorem inv_pos {x : FracRep} (hPos : 0 < x.num) :
    (inv x).num = x.den ∧ (inv x).den = x.num := by
  dsimp only [inv]
  rw [dif_pos hPos]
  exact ⟨rfl, rfl⟩

theorem inv_neg {x : FracRep} (hNeg : x.num < 0) :
    (inv x).num = -x.den ∧ (inv x).den = -x.num := by
  dsimp only [inv]
  have hNotPos : ¬ (0 < x.num) := by omega
  rw [dif_neg hNotPos, dif_pos hNeg]
  exact ⟨rfl, rfl⟩

theorem inv_zero {x : FracRep} (hZero : x.num = 0) : inv x = zero := by
  dsimp only [inv]
  have hNotPos : ¬ (0 < x.num) := by omega
  have hNotNeg : ¬ (x.num < 0) := by omega
  rw [dif_neg hNotPos, dif_neg hNotNeg]

theorem mul_inv_rel_one {x : FracRep} (hx : x.num ≠ 0) :
    Rel (mul x (inv x)) one := by
  dsimp only [Rel, mul, one]
  rw [Int.mul_one, Int.one_mul]
  by_cases hPos : 0 < x.num
  · rcases inv_pos hPos with ⟨hNum, hDen⟩
    rw [hNum, hDen, Int.mul_comm]
  · have hNeg : x.num < 0 := by omega
    rcases inv_neg hNeg with ⟨hNum, hDen⟩
    rw [hNum, hDen, Int.mul_neg, Int.mul_neg, Int.mul_comm]

end FracRep

/-- Setoid of formal fractions representing `ℚ`. -/
instance fracSetoid : Setoid FracRep where
  r := FracRep.Rel
  iseqv := ⟨FracRep.rel_refl, FracRep.rel_symm, FracRep.rel_trans⟩

/-- Concrete rational field `QField = ℚ`. -/
abbrev QField : Type := Quotient fracSetoid

namespace QField

def add : QField → QField → QField :=
  Quotient.lift₂ (fun x y => Quotient.mk fracSetoid (FracRep.add x y)) (by
    intro x1 y1 x2 y2 hx hy
    apply Quotient.sound
    change FracRep.Rel x1 x2 at hx
    change FracRep.Rel y1 y2 at hy
    change FracRep.Rel (FracRep.add x1 y1) (FracRep.add x2 y2)
    dsimp only [FracRep.Rel, FracRep.add] at hx hy ⊢
    calc
      (x1.num * y1.den + y1.num * x1.den) * (x2.den * y2.den)
        = (x1.num * x2.den) * (y1.den * y2.den) + (y1.num * y2.den) * (x1.den * x2.den) := by
            rw [Int.add_mul]
            have p1 : (x1.num * y1.den) * (x2.den * y2.den) =
                      (x1.num * x2.den) * (y1.den * y2.den) := by
              rw [Int.mul_assoc x1.num y1.den (x2.den * y2.den),
                  ← Int.mul_assoc y1.den x2.den y2.den,
                  Int.mul_comm y1.den x2.den,
                  Int.mul_assoc x2.den y1.den y2.den,
                  ← Int.mul_assoc x1.num x2.den (y1.den * y2.den)]
            have p2 : (y1.num * x1.den) * (x2.den * y2.den) =
                      (y1.num * y2.den) * (x1.den * x2.den) := by
              rw [Int.mul_assoc y1.num x1.den (x2.den * y2.den),
                  Int.mul_comm x2.den y2.den,
                  ← Int.mul_assoc x1.den y2.den x2.den,
                  Int.mul_comm x1.den y2.den,
                  Int.mul_assoc y2.den x1.den x2.den,
                  ← Int.mul_assoc y1.num y2.den (x1.den * x2.den)]
            rw [p1, p2]
      _ = (x2.num * x1.den) * (y1.den * y2.den) + (y2.num * y1.den) * (x1.den * x2.den) := by
            rw [hx, hy]
      _ = (x2.num * y2.den + y2.num * x2.den) * (x1.den * y1.den) := by
            rw [Int.add_mul]
            have p1 : (x2.num * y2.den) * (x1.den * y1.den) =
                      (x2.num * x1.den) * (y1.den * y2.den) := by
              rw [Int.mul_assoc x2.num y2.den (x1.den * y1.den),
                  ← Int.mul_assoc y2.den x1.den y1.den,
                  Int.mul_comm y2.den x1.den,
                  Int.mul_assoc x1.den y2.den y1.den,
                  Int.mul_comm y2.den y1.den,
                  ← Int.mul_assoc x2.num x1.den (y1.den * y2.den)]
            have p2 : (y2.num * x2.den) * (x1.den * y1.den) =
                      (y2.num * y1.den) * (x1.den * x2.den) := by
              rw [Int.mul_assoc y2.num x2.den (x1.den * y1.den),
                  Int.mul_comm x1.den y1.den,
                  ← Int.mul_assoc x2.den y1.den x1.den,
                  Int.mul_comm x2.den y1.den,
                  Int.mul_assoc y1.den x2.den x1.den,
                  Int.mul_comm x2.den x1.den,
                  ← Int.mul_assoc y2.num y1.den (x1.den * x2.den)]
            rw [p1, p2])

def neg : QField → QField :=
  Quotient.lift (fun x => Quotient.mk fracSetoid (FracRep.neg x)) (by
    intro x y hxy
    apply Quotient.sound
    change FracRep.Rel x y at hxy
    change FracRep.Rel (FracRep.neg x) (FracRep.neg y)
    dsimp only [FracRep.Rel, FracRep.neg] at hxy ⊢
    rw [Int.neg_mul, Int.neg_mul, hxy])

def mulQ : QField → QField → QField :=
  Quotient.lift₂ (fun x y => Quotient.mk fracSetoid (FracRep.mul x y)) (by
    intro x1 y1 x2 y2 hx hy
    apply Quotient.sound
    change FracRep.Rel x1 x2 at hx
    change FracRep.Rel y1 y2 at hy
    change FracRep.Rel (FracRep.mul x1 y1) (FracRep.mul x2 y2)
    dsimp only [FracRep.Rel, FracRep.mul] at hx hy ⊢
    calc
      (x1.num * y1.num) * (x2.den * y2.den)
        = (x1.num * x2.den) * (y1.num * y2.den) := by
            rw [Int.mul_assoc x1.num y1.num (x2.den * y2.den),
                ← Int.mul_assoc y1.num x2.den y2.den,
                Int.mul_comm y1.num x2.den,
                Int.mul_assoc x2.den y1.num y2.den,
                ← Int.mul_assoc x1.num x2.den (y1.num * y2.den)]
      _ = (x2.num * x1.den) * (y2.num * y1.den) := by rw [hx, hy]
      _ = (x2.num * y2.num) * (x1.den * y1.den) := by
            rw [Int.mul_assoc x2.num x1.den (y2.num * y1.den),
                ← Int.mul_assoc x1.den y2.num y1.den,
                Int.mul_comm x1.den y2.num,
                Int.mul_assoc y2.num x1.den y1.den,
                ← Int.mul_assoc x2.num y2.num (x1.den * y1.den)])

def inv : QField → QField :=
  Quotient.lift (fun x => Quotient.mk fracSetoid (FracRep.inv x)) (by
    intro x y hxy
    apply Quotient.sound
    change FracRep.Rel x y at hxy
    change FracRep.Rel (FracRep.inv x) (FracRep.inv y)
    dsimp only [FracRep.Rel] at hxy ⊢
    by_cases hx0 : x.num = 0
    · have hy0 : y.num = 0 := by
        rw [hx0, Int.zero_mul] at hxy
        rcases FracRep.int_mul_eq_zero hxy.symm with hyZ | hxDen
        · exact hyZ
        · exact False.elim (FracRep.den_ne_zero x hxDen)
      rw [FracRep.inv_zero hx0, FracRep.inv_zero hy0]
    · have hy0 : y.num ≠ 0 := by
        intro hyZ
        rw [hyZ, Int.zero_mul] at hxy
        rcases FracRep.int_mul_eq_zero hxy with hxZ | hyDen
        · exact hx0 hxZ
        · exact FracRep.den_ne_zero y hyDen
      apply FracRep.int_mul_right_cancel hx0
      apply FracRep.int_mul_right_cancel hy0
      have hInvX : (FracRep.inv x).num * x.num = x.den * (FracRep.inv x).den := by
        by_cases hxp : 0 < x.num
        · rcases FracRep.inv_pos hxp with ⟨hn, hd⟩; rw [hn, hd]
        · have hxn : x.num < 0 := by omega
          rcases FracRep.inv_neg hxn with ⟨hn, hd⟩
          rw [hn, hd, Int.neg_mul, Int.mul_neg]
      have hInvY : (FracRep.inv y).num * y.num = y.den * (FracRep.inv y).den := by
        by_cases hyp : 0 < y.num
        · rcases FracRep.inv_pos hyp with ⟨hn, hd⟩; rw [hn, hd]
        · have hyn : y.num < 0 := by omega
          rcases FracRep.inv_neg hyn with ⟨hn, hd⟩
          rw [hn, hd, Int.neg_mul, Int.mul_neg]
      calc
        (((FracRep.inv x).num * (FracRep.inv y).den) * x.num) * y.num
          = ((FracRep.inv x).num * x.num) * ((FracRep.inv y).den * y.num) := by
              rw [Int.mul_assoc (FracRep.inv x).num (FracRep.inv y).den x.num,
                  Int.mul_comm (FracRep.inv y).den x.num,
                  ← Int.mul_assoc (FracRep.inv x).num x.num (FracRep.inv y).den,
                  Int.mul_assoc ((FracRep.inv x).num * x.num) (FracRep.inv y).den y.num]
        _ = (x.den * (FracRep.inv x).den) * ((FracRep.inv y).den * y.num) := by rw [hInvX]
        _ = (y.num * x.den) * ((FracRep.inv x).den * (FracRep.inv y).den) := by
              rw [Int.mul_comm (FracRep.inv y).den y.num,
                  Int.mul_assoc x.den (FracRep.inv x).den (y.num * (FracRep.inv y).den),
                  ← Int.mul_assoc (FracRep.inv x).den y.num (FracRep.inv y).den,
                  Int.mul_comm (FracRep.inv x).den y.num,
                  Int.mul_assoc y.num (FracRep.inv x).den (FracRep.inv y).den,
                  ← Int.mul_assoc x.den y.num ((FracRep.inv x).den * (FracRep.inv y).den),
                  Int.mul_comm x.den y.num]
        _ = (x.num * y.den) * ((FracRep.inv x).den * (FracRep.inv y).den) := by rw [← hxy]
        _ = ((y.den * (FracRep.inv y).den) * (FracRep.inv x).den) * x.num := by
              rw [Int.mul_comm x.num y.den,
                  Int.mul_assoc y.den x.num ((FracRep.inv x).den * (FracRep.inv y).den),
                  Int.mul_comm x.num ((FracRep.inv x).den * (FracRep.inv y).den),
                  ← Int.mul_assoc y.den ((FracRep.inv x).den * (FracRep.inv y).den) x.num]
              apply congrArg (fun t => t * x.num)
              rw [← Int.mul_assoc y.den (FracRep.inv x).den (FracRep.inv y).den,
                  Int.mul_assoc y.den (FracRep.inv x).den (FracRep.inv y).den,
                  Int.mul_comm (FracRep.inv x).den (FracRep.inv y).den,
                  ← Int.mul_assoc y.den (FracRep.inv y).den (FracRep.inv x).den]
        _ = (((FracRep.inv y).num * y.num) * (FracRep.inv x).den) * x.num := by rw [← hInvY]
        _ = (((FracRep.inv y).num * (FracRep.inv x).den) * x.num) * y.num := by
              rw [Int.mul_assoc (FracRep.inv y).num y.num (FracRep.inv x).den,
                  Int.mul_comm y.num (FracRep.inv x).den,
                  ← Int.mul_assoc (FracRep.inv y).num (FracRep.inv x).den y.num,
                  Int.mul_assoc ((FracRep.inv y).num * (FracRep.inv x).den) y.num x.num,
                  Int.mul_comm y.num x.num,
                  ← Int.mul_assoc ((FracRep.inv y).num * (FracRep.inv x).den) x.num y.num])

instance : FieldOps QField where
  zero := Quotient.mk fracSetoid FracRep.zero
  one := Quotient.mk fracSetoid FracRep.one
  add := add
  sub a b := add a (neg b)
  neg := neg
  mul := mulQ
  inv := inv
  zero_ne_one := by
    intro h
    have hRel : FracRep.Rel FracRep.zero FracRep.one := Quotient.exact h
    dsimp only [FracRep.Rel, FracRep.zero, FracRep.one] at hRel
    omega
  add_assoc a b c := by
    refine Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound ?_)
    change FracRep.Rel (FracRep.add (FracRep.add x y) z) (FracRep.add x (FracRep.add y z))
    dsimp only [FracRep.Rel, FracRep.add]
    have hL : ((x.num * y.den + y.num * x.den) * z.den + z.num * (x.den * y.den)) =
              x.num * (y.den * z.den) + (y.num * z.den + z.num * y.den) * x.den := by
      rw [Int.add_mul, Int.add_mul, Int.mul_assoc x.num y.den z.den]
      have t1 : (y.num * x.den) * z.den = (y.num * z.den) * x.den := by
        rw [Int.mul_assoc, Int.mul_comm x.den z.den, ← Int.mul_assoc]
      have t2 : z.num * (x.den * y.den) = (z.num * y.den) * x.den := by
        rw [Int.mul_comm x.den y.den, ← Int.mul_assoc]
      rw [t1, t2, Int.add_assoc]
    rw [hL, Int.mul_assoc x.den y.den z.den]
  add_comm a b := by
    refine Quotient.inductionOn₂ a b (fun x y => Quotient.sound ?_)
    change FracRep.Rel (FracRep.add x y) (FracRep.add y x)
    dsimp only [FracRep.Rel, FracRep.add]
    rw [Int.add_comm (x.num * y.den) (y.num * x.den), Int.mul_comm y.den x.den]
  zero_add a := by
    refine Quotient.inductionOn a (fun x => Quotient.sound ?_)
    change FracRep.Rel (FracRep.add FracRep.zero x) x
    dsimp only [FracRep.Rel, FracRep.add, FracRep.zero]
    rw [Int.zero_mul, Int.zero_add, Int.mul_one, Int.one_mul]
  add_zero a := by
    refine Quotient.inductionOn a (fun x => Quotient.sound ?_)
    change FracRep.Rel (FracRep.add x FracRep.zero) x
    dsimp only [FracRep.Rel, FracRep.add, FracRep.zero]
    rw [Int.zero_mul, Int.add_zero, Int.mul_one, Int.mul_one]
  neg_add_cancel a := by
    refine Quotient.inductionOn a (fun x => Quotient.sound ?_)
    change FracRep.Rel (FracRep.add (FracRep.neg x) x) FracRep.zero
    dsimp only [FracRep.Rel, FracRep.add, FracRep.neg, FracRep.zero]
    rw [Int.neg_mul, Int.mul_one, Int.zero_mul]
    omega
  sub_eq_add_neg _ _ := rfl
  mul_assoc a b c := by
    refine Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound ?_)
    change FracRep.Rel (FracRep.mul (FracRep.mul x y) z) (FracRep.mul x (FracRep.mul y z))
    dsimp only [FracRep.Rel, FracRep.mul]
    rw [Int.mul_assoc x.num y.num z.num, Int.mul_assoc x.den y.den z.den]
  mul_comm a b := by
    refine Quotient.inductionOn₂ a b (fun x y => Quotient.sound ?_)
    change FracRep.Rel (FracRep.mul x y) (FracRep.mul y x)
    dsimp only [FracRep.Rel, FracRep.mul]
    rw [Int.mul_comm x.num y.num, Int.mul_comm y.den x.den]
  one_mul a := by
    refine Quotient.inductionOn a (fun x => Quotient.sound ?_)
    change FracRep.Rel (FracRep.mul FracRep.one x) x
    dsimp only [FracRep.Rel, FracRep.mul, FracRep.one]
    rw [Int.one_mul, Int.one_mul]
  mul_one a := by
    refine Quotient.inductionOn a (fun x => Quotient.sound ?_)
    change FracRep.Rel (FracRep.mul x FracRep.one) x
    dsimp only [FracRep.Rel, FracRep.mul, FracRep.one]
    rw [Int.mul_one, Int.mul_one]
  left_distrib a b c := by
    refine Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound ?_)
    change FracRep.Rel (FracRep.mul x (FracRep.add y z))
                       (FracRep.add (FracRep.mul x y) (FracRep.mul x z))
    dsimp only [FracRep.Rel, FracRep.mul, FracRep.add]
    calc
      (x.num * (y.num * z.den + z.num * y.den)) * ((x.den * y.den) * (x.den * z.den))
        = (x.num * (y.num * z.den + z.num * y.den) * x.den) * (x.den * (y.den * z.den)) := by
            have hd : (x.den * y.den) * (x.den * z.den) = x.den * (x.den * (y.den * z.den)) := by
              rw [← Int.mul_assoc (x.den * y.den) x.den z.den,
                  Int.mul_assoc x.den y.den x.den,
                  Int.mul_comm y.den x.den,
                  Int.mul_assoc x.den (x.den * y.den) z.den,
                  Int.mul_assoc x.den y.den z.den]
            rw [hd, ← Int.mul_assoc _ x.den (x.den * (y.den * z.den))]
      _ = ((x.num * y.num) * (x.den * z.den) + (x.num * z.num) * (x.den * y.den)) *
            (x.den * (y.den * z.den)) := by
            apply congrArg (fun t => t * (x.den * (y.den * z.den)))
            rw [Int.mul_add, Int.add_mul]
            have p1 : (x.num * (y.num * z.den)) * x.den = (x.num * y.num) * (x.den * z.den) := by
              rw [← Int.mul_assoc x.num y.num z.den, Int.mul_assoc (x.num * y.num) z.den x.den,
                  Int.mul_comm z.den x.den]
            have p2 : (x.num * (z.num * y.den)) * x.den = (x.num * z.num) * (x.den * y.den) := by
              rw [← Int.mul_assoc x.num z.num y.den, Int.mul_assoc (x.num * z.num) y.den x.den,
                  Int.mul_comm y.den x.den]
            rw [p1, p2]
  right_distrib a b c := by
    refine Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound ?_)
    change FracRep.Rel (FracRep.mul (FracRep.add x y) z)
                       (FracRep.add (FracRep.mul x z) (FracRep.mul y z))
    dsimp only [FracRep.Rel, FracRep.mul, FracRep.add]
    calc
      ((x.num * y.den + y.num * x.den) * z.num) * ((x.den * z.den) * (y.den * z.den))
        = ((x.num * y.den + y.num * x.den) * z.num * z.den) * ((x.den * y.den) * z.den) := by
            have hd : (x.den * z.den) * (y.den * z.den) = z.den * ((x.den * y.den) * z.den) := by
              rw [← Int.mul_assoc (x.den * z.den) y.den z.den,
                  Int.mul_assoc x.den z.den y.den,
                  Int.mul_comm z.den y.den,
                  ← Int.mul_assoc x.den y.den z.den,
                  Int.mul_comm ((x.den * y.den) * z.den) z.den]
            rw [hd, ← Int.mul_assoc _ z.den ((x.den * y.den) * z.den)]
      _ = ((x.num * z.num) * (y.den * z.den) + (y.num * z.num) * (x.den * z.den)) *
            ((x.den * y.den) * z.den) := by
            apply congrArg (fun t => t * ((x.den * y.den) * z.den))
            rw [Int.add_mul, Int.add_mul]
            have p1 : ((x.num * y.den) * z.num) * z.den = (x.num * z.num) * (y.den * z.den) := by
              rw [Int.mul_assoc x.num y.den z.num, Int.mul_comm y.den z.num,
                  ← Int.mul_assoc x.num z.num y.den, Int.mul_assoc (x.num * z.num) y.den z.den]
            have p2 : ((y.num * x.den) * z.num) * z.den = (y.num * z.num) * (x.den * z.den) := by
              rw [Int.mul_assoc y.num x.den z.num, Int.mul_comm x.den z.num,
                  ← Int.mul_assoc y.num z.num x.den, Int.mul_assoc (y.num * z.num) x.den z.den]
            rw [p1, p2]
  mul_inv_cancel a ha := by
    refine Quotient.inductionOn a (fun x => ?_) ha
    intro hxNe
    have hxNum : x.num ≠ 0 := by
      intro h0
      apply hxNe
      apply Quotient.sound
      change FracRep.Rel x FracRep.zero
      dsimp only [FracRep.Rel, FracRep.zero]
      rw [h0, Int.zero_mul, Int.zero_mul]
    exact Quotient.sound (FracRep.mul_inv_rel_one hxNum)

theorem int_sq_nonneg (n : Int) : 0 ≤ n * n := by
  by_cases h0 : n = 0
  · subst h0; omega
  · by_cases hp : 0 < n
    · have := Int.mul_pos hp hp; omega
    · have hn : 0 < -n := by omega
      have hpos := Int.mul_pos hn hn
      rw [Int.neg_mul, Int.mul_neg, Int.neg_neg] at hpos
      omega

theorem int_sq_pos_of_ne_zero {n : Int} (hn : n ≠ 0) : 0 < n * n := by
  by_cases hp : 0 < n
  · exact Int.mul_pos hp hp
  · have hneg : 0 < -n := by omega
    have hpos := Int.mul_pos hneg hneg
    rw [Int.neg_mul, Int.mul_neg, Int.neg_neg] at hpos
    exact hpos

theorem eq_zero_iff (x : FracRep) :
    (Quotient.mk fracSetoid x : QField) = 0 ↔ x.num = 0 := by
  constructor
  · intro h
    have hRel : FracRep.Rel x FracRep.zero := Quotient.exact h
    dsimp only [FracRep.Rel, FracRep.zero] at hRel
    omega
  · intro h0
    apply Quotient.sound
    change FracRep.Rel x FracRep.zero
    dsimp only [FracRep.Rel, FracRep.zero]
    rw [h0, Int.zero_mul, Int.zero_mul]

/-- `QField` (`ℚ`) is 4-square anisotropic: `a² + b² + c² + d² = 0 → a = b = c = d = 0`. -/
theorem four_sq_anisotropic : IsFourSqAnisotropic QField := by
  intro a b c d
  refine Quotient.inductionOn₂ a b (fun x y => ?_)
  refine Quotient.inductionOn₂ c d (fun z w => ?_)
  intro hSum
  rw [eq_zero_iff, eq_zero_iff, eq_zero_iff, eq_zero_iff]
  have hNum0 : ((FracRep.add (FracRep.add (FracRep.mul x x) (FracRep.mul y y))
                             (FracRep.add (FracRep.mul z z) (FracRep.mul w w)))).num = 0 :=
    (eq_zero_iff _).mp hSum
  dsimp only [FracRep.add, FracRep.mul] at hNum0
  have hxD := Int.mul_pos x.den_pos x.den_pos
  have hyD := Int.mul_pos y.den_pos y.den_pos
  have hzD := Int.mul_pos z.den_pos z.den_pos
  have hwD := Int.mul_pos w.den_pos w.den_pos
  have hxyD := Int.mul_pos hxD hyD
  have hzwD := Int.mul_pos hzD hwD
  have ht1 : 0 ≤ (x.num * x.num * (y.den * y.den)) * ((z.den * z.den) * (w.den * w.den)) :=
    Int.mul_nonneg (Int.mul_nonneg (int_sq_nonneg x.num) (by omega)) (by omega)
  have ht2 : 0 ≤ (y.num * y.num * (x.den * x.den)) * ((z.den * z.den) * (w.den * w.den)) :=
    Int.mul_nonneg (Int.mul_nonneg (int_sq_nonneg y.num) (by omega)) (by omega)
  have ht3 : 0 ≤ (z.num * z.num * (w.den * w.den)) * ((x.den * x.den) * (y.den * y.den)) :=
    Int.mul_nonneg (Int.mul_nonneg (int_sq_nonneg z.num) (by omega)) (by omega)
  have ht4 : 0 ≤ (w.num * w.num * (z.den * z.den)) * ((x.den * x.den) * (y.den * y.den)) :=
    Int.mul_nonneg (Int.mul_nonneg (int_sq_nonneg w.num) (by omega)) (by omega)
  rw [Int.add_mul, Int.add_mul] at hNum0
  have hx0 : x.num = 0 := by
    by_cases h0 : x.num = 0
    · exact h0
    · exfalso
      have hStrict := Int.mul_pos (Int.mul_pos (int_sq_pos_of_ne_zero h0) hyD) hzwD
      omega
  have hy0 : y.num = 0 := by
    by_cases h0 : y.num = 0
    · exact h0
    · exfalso
      have hStrict := Int.mul_pos (Int.mul_pos (int_sq_pos_of_ne_zero h0) hxD) hzwD
      omega
  have hz0 : z.num = 0 := by
    by_cases h0 : z.num = 0
    · exact h0
    · exfalso
      have hStrict := Int.mul_pos (Int.mul_pos (int_sq_pos_of_ne_zero h0) hwD) hxyD
      omega
  have hw0 : w.num = 0 := by
    by_cases h0 : w.num = 0
    · exact h0
    · exfalso
      have hStrict := Int.mul_pos (Int.mul_pos (int_sq_pos_of_ne_zero h0) hzD) hxyD
      omega
  exact ⟨hx0, hy0, hz0, hw0⟩

theorem two_sq_anisotropic : IsTwoSqAnisotropic QField := by
  intro a b h
  have h4 : (a * a + b * b) + ((0 : QField) * 0 + (0 : QField) * 0) = 0 := by
    rw [FieldOps.zero_mul, FieldOps.add_zero, h, FieldOps.add_zero]
  rcases four_sq_anisotropic a b 0 0 h4 with ⟨ha, hb, _, _⟩
  exact ⟨ha, hb⟩

end QField

/-!
## 2. Exact Real Clifford Zero-Divisor Dimension Law & Master Disproof Theorem
-/

/-- Bott-periodic real codimension `c(p - q mod 8) ∈ {1, 2, 4}` of `Z(Cl_{p,q,r}(ℝ))`. -/
def bottCodim (p q : Nat) : Nat :=
  let k := ((Int.ofNat p - Int.ofNat q) % 8 + 8).toNat % 8
  if k == 0 || k == 1 || k == 2 then 1
  else if k == 3 || k == 7 then 2
  else 4

/-- Exact real algebraic dimension `dim_ℝ Z(Cl_{p,q,r}(ℝ)) = 2^(p+q+r) - bottCodim p q`. -/
def realCliffordZeroDivisorDim (p q r : Nat) : Nat :=
  2 ^ (p + q + r) - bottCodim p q

/-- Metric rank deficit (`dim V - rank(B_Q)`) equals the metric nullity count `r`. -/
def metricRankDeficit (p q r : Nat) : Nat :=
  (p + q + r) - (p + q)

theorem metricRankDeficit_eq_nullity (p q r : Nat) : metricRankDeficit p q r = r := by
  dsimp only [metricRankDeficit]
  omega

/--
**Obstruction 1 — No Dimension Law Determined by `(n, r)` Exists (`r = 0` Counterexamples):**
-/
theorem no_dimension_law_from_metric_rank_deficit :
    ¬ ∃ law : Nat → Nat → Nat,
        ∀ p q r : Nat,
          realCliffordZeroDivisorDim p q r = law (p + q + r) (metricRankDeficit p q r) := by
  rintro ⟨law, hLaw⟩
  have h01 := hLaw 0 1 0
  have h10 := hLaw 1 0 0
  dsimp only [realCliffordZeroDivisorDim, bottCodim, metricRankDeficit] at h01 h10
  have hEq : (0 : Nat) = 1 := h01.trans h10.symm
  cases hEq

theorem n2_and_n3_r0_multiplicity :
    realCliffordZeroDivisorDim 0 2 0 = 0 ∧
    realCliffordZeroDivisorDim 1 1 0 = 3 ∧
    realCliffordZeroDivisorDim 2 0 0 = 3 ∧
    realCliffordZeroDivisorDim 0 3 0 = 4 ∧
    realCliffordZeroDivisorDim 1 2 0 = 6 ∧
    realCliffordZeroDivisorDim 2 1 0 = 7 ∧
    realCliffordZeroDivisorDim 3 0 0 = 6 ∧
    realCliffordZeroDivisorDim 0 1 1 = 2 ∧
    realCliffordZeroDivisorDim 0 0 2 = 3 := by
  decide

theorem bottCodim_le_four (p q : Nat) : bottCodim p q ≤ 4 := by
  dsimp only [bottCodim]
  split
  · decide
  · split <;> decide

theorem four_le_two_pow_add_two (k : Nat) : 4 ≤ 2 ^ (k + 2) := by
  have hk : 1 ≤ 2 ^ k := FiniteFieldOps.one_le_two_pow k
  have hpow : 2 ^ (k + 2) = 2 ^ k * 4 := Nat.pow_add 2 k 2
  omega

theorem two_pow_le_two_pow_add (a : Nat) : ∀ b : Nat, 2 ^ a ≤ 2 ^ (a + b)
  | 0 => Nat.le_refl (2 ^ a)
  | m + 1 => by
    have ih := two_pow_le_two_pow_add a m
    have hstep : 2 ^ (a + (m + 1)) = 2 ^ (a + m) * 2 := by
      have he : a + (m + 1) = (a + m) + 1 := by omega
      rw [he, Nat.pow_succ]
    omega

theorem bottCodim_le_two_pow (p q : Nat) : bottCodim p q ≤ 2 ^ (p + q) := by
  match p, q with
  | 0, 0 => decide
  | 1, 0 => decide
  | 0, 1 => decide
  | p2 + 2, q =>
    have h4 := bottCodim_le_four (p2 + 2) q
    have hp := four_le_two_pow_add_two (p2 + q)
    have he : p2 + 2 + q = (p2 + q) + 2 := by omega
    rw [he]
    omega
  | 1, q1 + 1 =>
    have h4 := bottCodim_le_four 1 (q1 + 1)
    have hp := four_le_two_pow_add_two q1
    have he : 1 + (q1 + 1) = q1 + 2 := by omega
    rw [he]
    omega
  | 0, q2 + 2 =>
    have h4 := bottCodim_le_four 0 (q2 + 2)
    have hp := four_le_two_pow_add_two q2
    have he : 0 + (q2 + 2) = q2 + 2 := by omega
    rw [he]
    omega

/--
**Obstruction 2 — Complete Insensitivity of Codimension to Metric Nullity `r`:**
-/
theorem codim_independent_of_nullity (p q r : Nat) :
    2 ^ (p + q + r) - realCliffordZeroDivisorDim p q r = bottCodim p q := by
  dsimp only [realCliffordZeroDivisorDim]
  have h1 : bottCodim p q ≤ 2 ^ (p + q) := bottCodim_le_two_pow p q
  have h2 : 2 ^ (p + q) ≤ 2 ^ (p + q + r) := two_pow_le_two_pow_add (p + q) r
  omega

/--
**Master End-to-End Disproof Theorem for Conjecture 00000007621:**
Combines concrete algebraic counterexamples over `ℚ` (`QField`) and `𝔽₃` (`F3`) refuting every
algebraic and geometric reading of the zero-divisor metric rank-deficit conjecture.
-/
theorem conjecture_00000007621_disproved :
    -- (1) Non-existence of any dimension law determined by `(n, r)`
    (¬ ∃ law : Nat → Nat → Nat,
        ∀ p q r : Nat,
          realCliffordZeroDivisorDim p q r = law (p + q + r) (metricRankDeficit p q r)) ∧
    -- (2) Concrete characteristic-0 division vs. zero-divisor contrast at `(n, r) = (1, 0)` and `(2, 0)`
    (∀ z : QField × QField,
        IsZeroDivisor (cl01Alg QField).zero (cl01Alg QField).mul z ↔ z = (0, 0)) ∧
    ((1 : QField), (1 : QField)) ≠ (0, 0) ∧
    IsZeroDivisor (cl10Alg QField).zero (cl10Alg QField).mul ((1 : QField), (1 : QField)) ∧
    (∀ q : (QField × QField) × (QField × QField),
        IsZeroDivisor (cl02Alg QField).zero (cl02Alg QField).mul q ↔ q = ((0, 0), (0, 0))) ∧
    grade1Vec (1 : QField) 1 ≠ ((0, 0), (0, 0)) ∧
    IsZeroDivisor (cl11Alg QField).zero (cl11Alg QField).mul (grade1Vec (1 : QField) 1) ∧
    -- (3) Exact finite-field point-count & annihilator contrasts over `𝔽₃`
    (∃ L : List (F3 × F3),
        IsExactEnum (IsZeroDivisor (cl01Alg F3).zero (cl01Alg F3).mul) L ∧ L.length = 1) ∧
    (∃ L : List (F3 × F3),
        IsExactEnum (IsZeroDivisor (cl10Alg F3).zero (cl10Alg F3).mul) L ∧ L.length = 5) ∧
    (∃ L : List (Mat2 F3),
        IsExactEnum (IsZeroDivisor (Mat2.alg F3).zero (Mat2.alg F3).mul) L ∧ L.length = 33) ∧
    (∃ L : List (ExtAlg F3 2),
        IsExactEnum (IsZeroDivisor (extAlg F3 2).zero (extAlg F3 2).mul) L ∧ L.length = 27) ∧
    (∃ L : List (Mat2 F3),
        IsExactEnum (InRightAnn (Mat2.alg F3).zero (Mat2.alg F3).mul Mat2.e11) L ∧ L.length = 9) ∧
    (∃ L1 L2 : List (ExtAlg F3 3),
        IsExactEnum (InRightAnn (extAlg F3 3).zero (extAlg F3 3).mul (lastGen F3 2)) L1 ∧
        IsExactEnum (InRightAnn (extAlg F3 3).zero (extAlg F3 3).mul (topMonomial F3 3)) L2 ∧
        L1.length = 81 ∧ L2.length = 2187 ∧ L1.length ≠ L2.length) := by
  refine ⟨no_dimension_law_from_metric_rank_deficit,
          cl01_isZeroDivisor_iff QField.two_sq_anisotropic,
          ?_,
          cl10_line_zeroDivisor (1 : QField),
          cl02_isZeroDivisor_iff QField.four_sq_anisotropic,
          ?_,
          (cl11_grade1_isZeroDivisor_iff (1 : QField) 1).mpr (Or.inl rfl),
          FiniteFieldOps.cl01_zeroDivisor_card F3 F3.two_sq_anisotropic,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_⟩
  · intro h
    exact FieldOps.zero_ne_one (congrArg Prod.fst h).symm
  · intro h
    exact FieldOps.zero_ne_one (congrArg Prod.snd (congrArg Prod.fst h)).symm
  · rcases FiniteFieldOps.cl10_zeroDivisor_card F3 F3.two_ne_zero with ⟨L, hEnum, hLen⟩
    exact ⟨L, hEnum, hLen⟩
  · rcases FiniteFieldOps.mat2_zeroDivisor_card F3 with ⟨L, hEnum, hLen, _⟩
    exact ⟨L, hEnum, hLen⟩
  · exact FiniteFieldOps.extAlg_zeroDivisor_card F3 2
  · exact FiniteFieldOps.mat2_annR_e11_card F3
  · rcases FiniteFieldOps.extAlg_annR_lastGen_card F3 2 with ⟨L1, hE1, hL1⟩
    rcases FiniteFieldOps.extAlg_annR_topMonomial_card F3 3 with ⟨L2, hE2, hL2⟩
    refine ⟨L1, L2, hE1, hE2, hL1, hL2, ?_⟩
    rw [hL1, hL2]
    decide

end ZeroDivisorMetricRankDeficit
