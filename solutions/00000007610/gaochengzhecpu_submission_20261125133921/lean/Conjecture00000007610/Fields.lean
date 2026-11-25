/-
  Conjecture 00000007610 — Exact Rational Field Q and Quadratic Field Extensions K(√d)
  Pure Lean 4.19.0 core (zero external dependencies).
-/

import Conjecture00000007610.Algebra

namespace Conjecture00000007610

universe u

/-! ### Part 1: Exact Rational Field `RatQ` Constructed as Quotient of Pairs `(num, den > 0)` -/

structure PreRat where
  num : Int
  den : Int
  den_pos : 0 < den

def PreRat.Rel (a b : PreRat) : Prop :=
  a.num * b.den = b.num * a.den

theorem PreRat.rel_refl (a : PreRat) : PreRat.Rel a a := rfl

theorem PreRat.rel_symm {a b : PreRat} (h : PreRat.Rel a b) : PreRat.Rel b a := h.symm

private theorem int_mul_cancel_right {x y z : Int} (hz : 0 < z) (h : x * z = y * z) : x = y := by
  have hdiff : (x - y) * z = 0 := by
    rw [Int.sub_mul, h, Int.sub_self]
  cases Int.mul_eq_zero.mp hdiff with
  | inl hxy => omega
  | inr hz0 => omega

theorem PreRat.rel_trans {a b c : PreRat} (hab : PreRat.Rel a b) (hbc : PreRat.Rel b c) :
    PreRat.Rel a c := by
  unfold PreRat.Rel at *
  apply int_mul_cancel_right b.den_pos
  calc
    (a.num * c.den) * b.den = (a.num * b.den) * c.den := by
      rw [Int.mul_assoc, Int.mul_comm c.den b.den, ← Int.mul_assoc]
    _ = (b.num * a.den) * c.den := by rw [hab]
    _ = (b.num * c.den) * a.den := by
      rw [Int.mul_assoc, Int.mul_comm a.den c.den, ← Int.mul_assoc]
    _ = (c.num * b.den) * a.den := by rw [hbc]
    _ = (c.num * a.den) * b.den := by
      rw [Int.mul_assoc, Int.mul_comm b.den a.den, ← Int.mul_assoc]

def PreRat.add (a b : PreRat) : PreRat where
  num := a.num * b.den + b.num * a.den
  den := a.den * b.den
  den_pos := Int.mul_pos a.den_pos b.den_pos

def PreRat.neg (a : PreRat) : PreRat where
  num := -a.num
  den := a.den
  den_pos := a.den_pos

def PreRat.mul (a b : PreRat) : PreRat where
  num := a.num * b.num
  den := a.den * b.den
  den_pos := Int.mul_pos a.den_pos b.den_pos

def PreRat.inv (a : PreRat) : PreRat :=
  if hpos : 0 < a.num then
    ⟨a.den, a.num, hpos⟩
  else if hneg : a.num < 0 then
    ⟨-a.den, -a.num, by omega⟩
  else
    ⟨0, 1, by omega⟩

/-- Exact field of rational numbers Q. -/
def RatQ : Type := Quot PreRat.Rel

def RatQ.mk (p : PreRat) : RatQ := Quot.mk PreRat.Rel p

def RatQ.ofInt (n : Int) : RatQ := RatQ.mk ⟨n, 1, by omega⟩

theorem RatQ.sound {a b : PreRat} (h : PreRat.Rel a b) : RatQ.mk a = RatQ.mk b :=
  Quot.sound h

theorem RatQ.exact {a b : PreRat} (h : RatQ.mk a = RatQ.mk b) : PreRat.Rel a b := by
  let prop : RatQ → Prop := Quot.lift (fun x => PreRat.Rel a x) (by
    intro x y hxy
    apply propext
    constructor
    · intro hax
      exact PreRat.rel_trans hax hxy
    · intro hay
      exact PreRat.rel_trans hay (PreRat.rel_symm hxy))
  have ha : prop (RatQ.mk a) := PreRat.rel_refl a
  rw [h] at ha
  exact ha

private theorem add_well_def {a1 a2 b1 b2 : PreRat}
    (ha : PreRat.Rel a1 a2) (hb : PreRat.Rel b1 b2) :
    PreRat.Rel (PreRat.add a1 b1) (PreRat.add a2 b2) := by
  unfold PreRat.Rel PreRat.add at *
  dsimp
  calc
    (a1.num * b1.den + b1.num * a1.den) * (a2.den * b2.den)
      = (a1.num * a2.den) * (b1.den * b2.den) + (b1.num * b2.den) * (a1.den * a2.den) := by
        rw [Int.add_mul]
        congr 1 <;> ac_rfl
    _ = (a2.num * a1.den) * (b1.den * b2.den) + (b2.num * b1.den) * (a1.den * a2.den) := by
        rw [ha, hb]
    _ = (a2.num * b2.den + b2.num * a2.den) * (a1.den * b1.den) := by
        rw [Int.add_mul]
        congr 1 <;> ac_rfl

private theorem neg_well_def {a1 a2 : PreRat} (ha : PreRat.Rel a1 a2) :
    PreRat.Rel (PreRat.neg a1) (PreRat.neg a2) := by
  unfold PreRat.Rel PreRat.neg at *
  dsimp
  rw [Int.neg_mul, Int.neg_mul, ha]

private theorem mul_well_def {a1 a2 b1 b2 : PreRat}
    (ha : PreRat.Rel a1 a2) (hb : PreRat.Rel b1 b2) :
    PreRat.Rel (PreRat.mul a1 b1) (PreRat.mul a2 b2) := by
  unfold PreRat.Rel PreRat.mul at *
  dsimp
  calc
    (a1.num * b1.num) * (a2.den * b2.den)
      = (a1.num * a2.den) * (b1.num * b2.den) := by ac_rfl
    _ = (a2.num * a1.den) * (b2.num * b1.den) := by rw [ha, hb]
    _ = (a2.num * b2.num) * (a1.den * b1.den) := by ac_rfl

private theorem inv_well_def {a1 a2 : PreRat} (ha : PreRat.Rel a1 a2) :
    PreRat.Rel (PreRat.inv a1) (PreRat.inv a2) := by
  unfold PreRat.Rel at ha
  have hd1 := a1.den_pos
  have hd2 := a2.den_pos
  unfold PreRat.inv
  split
  · next hp1 =>
    have hprod_pos : 0 < a1.num * a2.den := Int.mul_pos hp1 hd2
    rw [ha] at hprod_pos
    have hp2 : 0 < a2.num := by
      by_cases h : 0 < a2.num
      · exact h
      · exfalso
        have hle : a2.num ≤ 0 := by omega
        have hnonpos : a2.num * a1.den ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg hle (by omega)
        omega
    rw [dif_pos hp2]
    unfold PreRat.Rel
    dsimp
    rw [Int.mul_comm a1.den a2.num, ← ha, Int.mul_comm a1.num a2.den]
  · next hnp1 =>
    split
    · next hn1 =>
      have hneg_pos : 0 < (-a1.num) * a2.den := Int.mul_pos (by omega) hd2
      have hprod_neg : a1.num * a2.den < 0 := by
        rw [Int.neg_mul] at hneg_pos
        omega
      rw [ha] at hprod_neg
      have hn2 : a2.num < 0 := by
        by_cases h : a2.num < 0
        · exact h
        · exfalso
          have hge : 0 ≤ a2.num := by omega
          have hnonneg : 0 ≤ a2.num * a1.den := Int.mul_nonneg hge (by omega)
          omega
      have hnp2 : ¬ (0 < a2.num) := by omega
      rw [dif_neg hnp2, dif_pos hn2]
      unfold PreRat.Rel
      dsimp
      rw [Int.neg_mul_neg, Int.neg_mul_neg, Int.mul_comm a1.den a2.num, ← ha,
          Int.mul_comm a1.num a2.den]
    · next hnn1 =>
      have hz1 : a1.num = 0 := by omega
      rw [hz1, Int.zero_mul] at ha
      have hz2 : a2.num = 0 := by
        cases Int.mul_eq_zero.mp ha.symm with
        | inl h => exact h
        | inr h => omega
      have hnp2 : ¬ (0 < a2.num) := by omega
      have hnn2 : ¬ (a2.num < 0) := by omega
      rw [dif_neg hnp2, dif_neg hnn2]
      rfl

def RatQ.add : RatQ → RatQ → RatQ :=
  Quot.lift (fun a => Quot.lift (fun b => RatQ.mk (PreRat.add a b))
    (fun _ _ hb => RatQ.sound (add_well_def (PreRat.rel_refl a) hb)))
    (fun _ _ ha => funext fun q => Quot.inductionOn q fun b =>
      RatQ.sound (add_well_def ha (PreRat.rel_refl b)))

def RatQ.neg : RatQ → RatQ :=
  Quot.lift (fun a => RatQ.mk (PreRat.neg a)) (fun _ _ ha => RatQ.sound (neg_well_def ha))

def RatQ.mul : RatQ → RatQ → RatQ :=
  Quot.lift (fun a => Quot.lift (fun b => RatQ.mk (PreRat.mul a b))
    (fun _ _ hb => RatQ.sound (mul_well_def (PreRat.rel_refl a) hb)))
    (fun _ _ ha => funext fun q => Quot.inductionOn q fun b =>
      RatQ.sound (mul_well_def ha (PreRat.rel_refl b)))

def RatQ.inv : RatQ → RatQ :=
  Quot.lift (fun a => RatQ.mk (PreRat.inv a)) (fun _ _ ha => RatQ.sound (inv_well_def ha))

instance : FieldStructure RatQ where
  zero := RatQ.ofInt 0
  one := RatQ.ofInt 1
  add := RatQ.add
  neg := RatQ.neg
  mul := RatQ.mul
  inv := RatQ.inv
  add_assoc x y z := Quot.inductionOn x fun a => Quot.inductionOn y fun b =>
    Quot.inductionOn z fun c => RatQ.sound (by
      unfold PreRat.Rel PreRat.add
      dsimp
      simp only [Int.add_mul, Int.mul_add, Int.add_assoc]
      congr 1
      · ac_rfl
      · congr 1 <;> ac_rfl)
  add_comm x y := Quot.inductionOn x fun a => Quot.inductionOn y fun b =>
    RatQ.sound (by
      unfold PreRat.Rel PreRat.add
      dsimp
      rw [Int.add_comm (a.num * b.den), Int.mul_comm a.den b.den])
  zero_add x := Quot.inductionOn x fun a => RatQ.sound (by
    unfold PreRat.Rel PreRat.add
    dsimp
    rw [Int.zero_mul, Int.zero_add, Int.mul_one, Int.one_mul])
  neg_add_cancel x := Quot.inductionOn x fun a => RatQ.sound (by
    unfold PreRat.Rel PreRat.add PreRat.neg
    dsimp
    rw [Int.neg_mul, Int.add_left_neg, Int.zero_mul, Int.zero_mul])
  mul_assoc x y z := Quot.inductionOn x fun a => Quot.inductionOn y fun b =>
    Quot.inductionOn z fun c => RatQ.sound (by
      unfold PreRat.Rel PreRat.mul
      dsimp
      rw [Int.mul_assoc a.num, Int.mul_assoc a.den])
  one_mul x := Quot.inductionOn x fun a => RatQ.sound (by
    unfold PreRat.Rel PreRat.mul
    dsimp
    rw [Int.one_mul, Int.one_mul])
  mul_one x := Quot.inductionOn x fun a => RatQ.sound (by
    unfold PreRat.Rel PreRat.mul
    dsimp
    rw [Int.mul_one, Int.mul_one])
  left_distrib x y z := Quot.inductionOn x fun a => Quot.inductionOn y fun b =>
    Quot.inductionOn z fun c => RatQ.sound (by
      unfold PreRat.Rel PreRat.mul PreRat.add
      dsimp
      rw [Int.mul_add, Int.add_mul, Int.add_mul]
      congr 1 <;> ac_rfl)
  right_distrib x y z := Quot.inductionOn x fun a => Quot.inductionOn y fun b =>
    Quot.inductionOn z fun c => RatQ.sound (by
      unfold PreRat.Rel PreRat.mul PreRat.add
      dsimp
      rw [Int.add_mul, Int.add_mul, Int.add_mul]
      congr 1 <;> ac_rfl)
  mul_comm x y := Quot.inductionOn x fun a => Quot.inductionOn y fun b =>
    RatQ.sound (by
      unfold PreRat.Rel PreRat.mul
      dsimp
      rw [Int.mul_comm a.num b.num, Int.mul_comm a.den b.den])
  zero_ne_one h := by
    have heq := RatQ.exact h
    unfold PreRat.Rel at heq
    dsimp at heq
    omega
  mul_inv_cancel x hx := Quot.inductionOn x (fun a ha => by
    apply RatQ.sound
    unfold PreRat.inv
    split
    · next hp =>
      unfold PreRat.Rel PreRat.mul
      dsimp
      rw [Int.mul_one, Int.one_mul, Int.mul_comm]
    · next hnp =>
      split
      · next hn =>
        unfold PreRat.Rel PreRat.mul
        dsimp
        rw [Int.mul_one, Int.one_mul, Int.mul_neg, Int.mul_neg, Int.mul_comm]
      · next hnn =>
        exfalso
        apply ha
        apply RatQ.sound
        unfold PreRat.Rel
        dsimp
        omega) hx
  inv_zero := RatQ.sound (by
    unfold PreRat.inv PreRat.Rel
    dsimp)

/-- No rational number satisfies q^2 + 1 = 0 (hence -1 is not a square in Q). -/
theorem ratQ_no_sqrt_neg_one (q : RatQ) : q * q + 1 ≠ 0 := by
  refine Quot.inductionOn q fun a h => ?_
  have heq := RatQ.exact h
  unfold PreRat.Rel PreRat.add PreRat.mul at heq
  dsimp at heq
  have hsq_nonneg : 0 ≤ a.num * a.num := by
    by_cases hp : 0 ≤ a.num
    · exact Int.mul_nonneg hp hp
    · have hn : a.num ≤ 0 := by omega
      exact Int.mul_nonneg_of_nonpos_of_nonpos hn hn
  have hden_pos : 0 < a.den * a.den := Int.mul_pos a.den_pos a.den_pos
  omega

/-- Corollary: -1 is a non-square in RatQ. -/
theorem ratQ_nonSquare_neg_one (q : RatQ) : q * q ≠ -(1 : RatQ) := by
  intro h
  apply ratQ_no_sqrt_neg_one q
  rw [h, AddCommGrp.neg_add_cancel]

/-- Natural number parity descent: a^2 ≠ 2 * b^2 for b > 0. -/
private theorem nat_sq_ne_two_mul_sq : ∀ b : Nat, 0 < b → ∀ a : Nat, a * a ≠ 2 * (b * b) := by
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro hb a heq
    have ha_even : a % 2 = 0 := by
      by_cases hpar : a % 2 = 0
      · exact hpar
      · exfalso
        have hodd : a = 2 * (a / 2) + 1 := by omega
        let k := a / 2
        have hsq : a * a = 2 * (2 * (k * k) + 2 * k) + 1 := by
          calc
            a * a = (2 * k + 1) * (2 * k + 1) := by rw [← hodd]
            _ = (2 * k + 1) * (2 * k) + (2 * k + 1) * 1 := by rw [Nat.mul_add]
            _ = (2 * k) * (2 * k) + 1 * (2 * k) + (2 * k + 1) := by rw [Nat.add_mul, Nat.mul_one]
            _ = 4 * (k * k) + 4 * k + 1 := by
              have h4 : (2 * k) * (2 * k) = 4 * (k * k) := by
                calc
                  (2 * k) * (2 * k) = 2 * (k * (2 * k)) := Nat.mul_assoc 2 k (2 * k)
                  _ = 2 * ((2 * k) * k) := by rw [Nat.mul_comm k (2 * k)]
                  _ = 2 * (2 * (k * k)) := by rw [Nat.mul_assoc 2 k k]
                  _ = 4 * (k * k) := by rw [← Nat.mul_assoc 2 2 (k * k)]
              rw [h4]
              omega
            _ = 2 * (2 * (k * k) + 2 * k) + 1 := by omega
        omega
    let k := a / 2
    have ha2 : a = 2 * k := by omega
    have h4k : 4 * (k * k) = 2 * (b * b) := by
      calc
        4 * (k * k) = (2 * 2) * (k * k) := rfl
        _ = 2 * (2 * (k * k)) := Nat.mul_assoc 2 2 (k * k)
        _ = 2 * ((2 * k) * k) := by rw [← Nat.mul_assoc 2 k k]
        _ = 2 * (k * (2 * k)) := by rw [Nat.mul_comm (2 * k) k]
        _ = (2 * k) * (2 * k) := (Nat.mul_assoc 2 k (2 * k)).symm
        _ = a * a := by rw [← ha2]
        _ = 2 * (b * b) := heq
    have hb2 : b * b = 2 * (k * k) := by omega
    have hk_pos : 0 < k := by
      by_cases hk0 : k = 0
      · rw [hk0] at hb2
        have hb0 : b * b = 0 := hb2
        cases Nat.mul_eq_zero.mp hb0 with
        | inl h => omega
        | inr h => omega
      · omega
    have hk_lt_b : k < b := by
      by_cases hlt : k < b
      · exact hlt
      · exfalso
        have hle : b ≤ k := by omega
        have hsq_le : b * b ≤ k * k := Nat.mul_le_mul hle hle
        have hk2_pos : 0 < k * k := Nat.mul_pos hk_pos hk_pos
        omega
    exact ih k hk_lt_b hk_pos b hb2

/-- Two is not a square in Q: ∀ q ∈ Q, q^2 ≠ 2. -/
theorem ratQ_nonSquare_two (q : RatQ) : q * q ≠ (1 : RatQ) + 1 := by
  refine Quot.inductionOn q fun a h => ?_
  have heq := RatQ.exact h
  unfold PreRat.Rel PreRat.mul PreRat.add at heq
  dsimp at heq
  have hint : a.num * a.num = 2 * (a.den * a.den) := by omega
  have hnat_eq : a.num.natAbs * a.num.natAbs = 2 * (a.den.natAbs * a.den.natAbs) := by
    have h0 := congrArg Int.natAbs hint
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul] at h0
    exact h0
  have hden_pos : 0 < a.den.natAbs := by
    have hd := a.den_pos
    omega
  exact nat_sq_ne_two_mul_sq a.den.natAbs hden_pos a.num.natAbs hnat_eq

/-! ### Part 2: Explicit Quadratic Field Extensions `QuadExt K d` (`K(√d)`) -/

/-- Predicate that d ∈ K is not a square in K. -/
def NonSquare {K : Type u} [FieldStructure K] (d : K) : Prop :=
  ∀ x : K, x * x ≠ d

/-- Underlying carrier K × K of K[X]/(X^2 - d). -/
structure QuadExt (K : Type u) [FieldStructure K] (d : K) where
  re : K
  im : K

theorem QuadExt.ext {K : Type u} [FieldStructure K] {d : K}
    {z1 z2 : QuadExt K d} (hre : z1.re = z2.re) (him : z1.im = z2.im) : z1 = z2 := by
  cases z1
  cases z2
  cases hre
  cases him
  rfl

instance quadExtRing (K : Type u) [FieldStructure K] (d : K) : UnitalRing (QuadExt K d) where
  zero := ⟨0, 0⟩
  one := ⟨1, 0⟩
  add z1 z2 := ⟨z1.re + z2.re, z1.im + z2.im⟩
  neg z := ⟨-z.re, -z.im⟩
  mul z1 z2 := ⟨z1.re * z2.re + d * (z1.im * z2.im), z1.re * z2.im + z1.im * z2.re⟩
  add_assoc z1 z2 z3 := QuadExt.ext
    (AddCommGrp.add_assoc z1.re z2.re z3.re)
    (AddCommGrp.add_assoc z1.im z2.im z3.im)
  add_comm z1 z2 := QuadExt.ext
    (AddCommGrp.add_comm z1.re z2.re)
    (AddCommGrp.add_comm z1.im z2.im)
  zero_add z := QuadExt.ext (AddCommGrp.zero_add z.re) (AddCommGrp.zero_add z.im)
  neg_add_cancel z := QuadExt.ext (AddCommGrp.neg_add_cancel z.re) (AddCommGrp.neg_add_cancel z.im)
  mul_assoc z1 z2 z3 := QuadExt.ext
    (by
      change (z1.re * z2.re + d * (z1.im * z2.im)) * z3.re +
          d * ((z1.re * z2.im + z1.im * z2.re) * z3.im) =
        z1.re * (z2.re * z3.re + d * (z2.im * z3.im)) +
          d * (z1.im * (z2.re * z3.im + z2.im * z3.re))
      rw [UnitalRing.right_distrib, UnitalRing.right_distrib, UnitalRing.left_distrib,
          UnitalRing.left_distrib, UnitalRing.left_distrib, UnitalRing.left_distrib]
      rw [UnitalRing.mul_assoc z1.re z2.re z3.re]
      rw [UnitalRing.mul_assoc d (z1.im * z2.im) z3.re, UnitalRing.mul_assoc z1.im z2.im z3.re]
      rw [UnitalRing.mul_assoc z1.re z2.im z3.im, UnitalRing.mul_assoc z1.im z2.re z3.im]
      rw [← UnitalRing.mul_assoc z1.re d (z2.im * z3.im), FieldStructure.mul_comm z1.re d,
          UnitalRing.mul_assoc d z1.re (z2.im * z3.im)]
      rw [AddCommGrp.add_assoc (z1.re * (z2.re * z3.re)),
          AddCommGrp.add_assoc (z1.re * (z2.re * z3.re))]
      congr 1
      rw [← AddCommGrp.add_assoc (d * (z1.im * (z2.im * z3.re))),
          AddCommGrp.add_comm (d * (z1.im * (z2.im * z3.re))) (d * (z1.re * (z2.im * z3.im))),
          AddCommGrp.add_assoc, AddCommGrp.add_comm (d * (z1.im * (z2.im * z3.re)))])
    (by
      change (z1.re * z2.re + d * (z1.im * z2.im)) * z3.im +
          (z1.re * z2.im + z1.im * z2.re) * z3.re =
        z1.re * (z2.re * z3.im + z2.im * z3.re) +
          z1.im * (z2.re * z3.re + d * (z2.im * z3.im))
      rw [UnitalRing.right_distrib, UnitalRing.right_distrib,
          UnitalRing.left_distrib, UnitalRing.left_distrib]
      rw [UnitalRing.mul_assoc z1.re z2.re z3.im, UnitalRing.mul_assoc z1.re z2.im z3.re,
          UnitalRing.mul_assoc z1.im z2.re z3.re]
      rw [UnitalRing.mul_assoc d (z1.im * z2.im) z3.im, UnitalRing.mul_assoc z1.im z2.im z3.im]
      rw [← UnitalRing.mul_assoc z1.im d (z2.im * z3.im), FieldStructure.mul_comm z1.im d,
          UnitalRing.mul_assoc d z1.im (z2.im * z3.im)]
      rw [AddCommGrp.add_assoc (z1.re * (z2.re * z3.im)),
          AddCommGrp.add_assoc (z1.re * (z2.re * z3.im))]
      congr 1
      rw [← AddCommGrp.add_assoc (d * (z1.im * (z2.im * z3.im))),
          AddCommGrp.add_comm (d * (z1.im * (z2.im * z3.im))) (z1.re * (z2.im * z3.re)),
          AddCommGrp.add_assoc, AddCommGrp.add_comm (d * (z1.im * (z2.im * z3.im)))])
  one_mul z := QuadExt.ext
    (by change 1 * z.re + d * (0 * z.im) = z.re; rw [UnitalRing.one_mul, zero_mul_ring, mul_zero_ring, add_zero_grp])
    (by change 1 * z.im + 0 * z.re = z.im; rw [UnitalRing.one_mul, zero_mul_ring, add_zero_grp])
  mul_one z := QuadExt.ext
    (by change z.re * 1 + d * (z.im * 0) = z.re; rw [UnitalRing.mul_one, mul_zero_ring, mul_zero_ring, add_zero_grp])
    (by change z.re * 0 + z.im * 1 = z.im; rw [mul_zero_ring, UnitalRing.mul_one, AddCommGrp.zero_add])
  left_distrib z1 z2 z3 := QuadExt.ext
    (by
      change z1.re * (z2.re + z3.re) + d * (z1.im * (z2.im + z3.im)) =
        (z1.re * z2.re + d * (z1.im * z2.im)) + (z1.re * z3.re + d * (z1.im * z3.im))
      rw [UnitalRing.left_distrib, UnitalRing.left_distrib, UnitalRing.left_distrib]
      rw [AddCommGrp.add_assoc (z1.re * z2.re), ← AddCommGrp.add_assoc (z1.re * z3.re),
          AddCommGrp.add_comm (z1.re * z3.re), AddCommGrp.add_assoc, ← AddCommGrp.add_assoc])
    (by
      change z1.re * (z2.im + z3.im) + z1.im * (z2.re + z3.re) =
        (z1.re * z2.im + z1.im * z2.re) + (z1.re * z3.im + z1.im * z3.re)
      rw [UnitalRing.left_distrib, UnitalRing.left_distrib]
      rw [AddCommGrp.add_assoc (z1.re * z2.im), ← AddCommGrp.add_assoc (z1.re * z3.im),
          AddCommGrp.add_comm (z1.re * z3.im), AddCommGrp.add_assoc, ← AddCommGrp.add_assoc])
  right_distrib z1 z2 z3 := QuadExt.ext
    (by
      change (z1.re + z2.re) * z3.re + d * ((z1.im + z2.im) * z3.im) =
        (z1.re * z3.re + d * (z1.im * z3.im)) + (z2.re * z3.re + d * (z2.im * z3.im))
      rw [UnitalRing.right_distrib, UnitalRing.right_distrib, UnitalRing.left_distrib]
      rw [AddCommGrp.add_assoc (z1.re * z3.re), ← AddCommGrp.add_assoc (z2.re * z3.re),
          AddCommGrp.add_comm (z2.re * z3.re), AddCommGrp.add_assoc, ← AddCommGrp.add_assoc])
    (by
      change (z1.re + z2.re) * z3.im + (z1.im + z2.im) * z3.re =
        (z1.re * z3.im + z1.im * z3.re) + (z2.re * z3.im + z2.im * z3.re)
      rw [UnitalRing.right_distrib, UnitalRing.right_distrib]
      rw [AddCommGrp.add_assoc (z1.re * z3.im), ← AddCommGrp.add_assoc (z2.re * z3.im),
          AddCommGrp.add_comm (z2.re * z3.im), AddCommGrp.add_assoc, ← AddCommGrp.add_assoc])

theorem QuadExt.mul_comm {K : Type u} [FieldStructure K] {d : K} (z1 z2 : QuadExt K d) :
    z1 * z2 = z2 * z1 :=
  QuadExt.ext
    (by
      change z1.re * z2.re + d * (z1.im * z2.im) = z2.re * z1.re + d * (z2.im * z1.im)
      rw [FieldStructure.mul_comm z1.re z2.re, FieldStructure.mul_comm z1.im z2.im])
    (by
      change z1.re * z2.im + z1.im * z2.re = z2.re * z1.im + z2.im * z1.re
      rw [FieldStructure.mul_comm z1.re z2.im, FieldStructure.mul_comm z1.im z2.re,
          AddCommGrp.add_comm])

instance quadExtKAlgebra (K : Type u) [FieldStructure K] (d : K) : KAlgebra K (QuadExt K d) where
  smul c z := ⟨c * z.re, c * z.im⟩
  one_smul z := QuadExt.ext (UnitalRing.one_mul z.re) (UnitalRing.one_mul z.im)
  mul_smul a b z := QuadExt.ext (UnitalRing.mul_assoc a b z.re) (UnitalRing.mul_assoc a b z.im)
  smul_zero a := QuadExt.ext (mul_zero_ring a) (mul_zero_ring a)
  smul_add a z1 z2 := QuadExt.ext
    (UnitalRing.left_distrib a z1.re z2.re) (UnitalRing.left_distrib a z1.im z2.im)
  add_smul a b z := QuadExt.ext
    (UnitalRing.right_distrib a b z.re) (UnitalRing.right_distrib a b z.im)
  zero_smul z := QuadExt.ext (zero_mul_ring z.re) (zero_mul_ring z.im)
  smul_mul_assoc a z1 z2 := QuadExt.ext
    (by
      change (a * z1.re) * z2.re + d * ((a * z1.im) * z2.im) =
        a * (z1.re * z2.re + d * (z1.im * z2.im))
      rw [UnitalRing.left_distrib, UnitalRing.mul_assoc a z1.re z2.re,
          UnitalRing.mul_assoc a z1.im z2.im, ← UnitalRing.mul_assoc d a,
          FieldStructure.mul_comm d a, UnitalRing.mul_assoc a d])
    (by
      change (a * z1.re) * z2.im + (a * z1.im) * z2.re = a * (z1.re * z2.im + z1.im * z2.re)
      rw [UnitalRing.left_distrib, UnitalRing.mul_assoc, UnitalRing.mul_assoc])
  mul_smul_comm a z1 z2 := QuadExt.ext
    (by
      change z1.re * (a * z2.re) + d * (z1.im * (a * z2.im)) =
        a * (z1.re * z2.re + d * (z1.im * z2.im))
      rw [UnitalRing.left_distrib, ← UnitalRing.mul_assoc z1.re a, FieldStructure.mul_comm z1.re a,
          UnitalRing.mul_assoc a z1.re, ← UnitalRing.mul_assoc z1.im a,
          FieldStructure.mul_comm z1.im a, UnitalRing.mul_assoc a z1.im,
          ← UnitalRing.mul_assoc d a, FieldStructure.mul_comm d a, UnitalRing.mul_assoc a d])
    (by
      change z1.re * (a * z2.im) + z1.im * (a * z2.re) = a * (z1.re * z2.im + z1.im * z2.re)
      rw [UnitalRing.left_distrib, ← UnitalRing.mul_assoc z1.re a, FieldStructure.mul_comm z1.re a,
          UnitalRing.mul_assoc a z1.re, ← UnitalRing.mul_assoc z1.im a,
          FieldStructure.mul_comm z1.im a, UnitalRing.mul_assoc a z1.im])

/-- Norm N(a + b√d) = a^2 - d * b^2 is nonzero whenever z ≠ 0 and d is non-square. -/
theorem QuadExt.norm_ne_zero {K : Type u} [FieldStructure K] {d : K}
    (hd : NonSquare d) {z : QuadExt K d} (hz : z ≠ 0) :
    z.re * z.re + -(d * (z.im * z.im)) ≠ 0 := by
  intro hnorm
  by_cases hb : z.im = 0
  · rw [hb, mul_zero_ring, mul_zero_ring, neg_zero_grp, add_zero_grp] at hnorm
    cases mul_eq_zero_field hnorm with
    | inl ha => exact hz (QuadExt.ext ha hb)
    | inr ha => exact hz (QuadExt.ext ha hb)
  · have h_eq : z.re * z.re = d * (z.im * z.im) := by
      have hneg : -(z.re * z.re) = -(d * (z.im * z.im)) := neg_eq_of_add_eq_zero hnorm
      calc
        z.re * z.re = -(-(z.re * z.re)) := (neg_neg_grp _).symm
        _ = -(-(d * (z.im * z.im))) := by rw [hneg]
        _ = d * (z.im * z.im) := neg_neg_grp _
    let q := z.re * FieldStructure.inv z.im
    have hq_sq : q * q = d := by
      unfold q
      calc
        (z.re * FieldStructure.inv z.im) * (z.re * FieldStructure.inv z.im)
          = z.re * (FieldStructure.inv z.im * (z.re * FieldStructure.inv z.im)) :=
            UnitalRing.mul_assoc _ _ _
        _ = z.re * ((FieldStructure.inv z.im * z.re) * FieldStructure.inv z.im) := by
            rw [← UnitalRing.mul_assoc (FieldStructure.inv z.im) z.re]
        _ = z.re * ((z.re * FieldStructure.inv z.im) * FieldStructure.inv z.im) := by
            rw [FieldStructure.mul_comm (FieldStructure.inv z.im) z.re]
        _ = z.re * (z.re * (FieldStructure.inv z.im * FieldStructure.inv z.im)) := by
            rw [UnitalRing.mul_assoc z.re (FieldStructure.inv z.im)]
        _ = (z.re * z.re) * (FieldStructure.inv z.im * FieldStructure.inv z.im) :=
            (UnitalRing.mul_assoc _ _ _).symm
        _ = (d * (z.im * z.im)) * (FieldStructure.inv z.im * FieldStructure.inv z.im) := by
            rw [h_eq]
        _ = d * ((z.im * z.im) * (FieldStructure.inv z.im * FieldStructure.inv z.im)) :=
            UnitalRing.mul_assoc _ _ _
        _ = d * 1 := by
            congr 1
            calc
              (z.im * z.im) * (FieldStructure.inv z.im * FieldStructure.inv z.im)
                = z.im * (z.im * (FieldStructure.inv z.im * FieldStructure.inv z.im)) :=
                  UnitalRing.mul_assoc _ _ _
              _ = z.im * ((z.im * FieldStructure.inv z.im) * FieldStructure.inv z.im) := by
                  rw [← UnitalRing.mul_assoc z.im (FieldStructure.inv z.im)]
              _ = z.im * (1 * FieldStructure.inv z.im) := by
                  rw [FieldStructure.mul_inv_cancel z.im hb]
              _ = z.im * FieldStructure.inv z.im := by rw [UnitalRing.one_mul]
              _ = 1 := FieldStructure.mul_inv_cancel z.im hb
        _ = d := UnitalRing.mul_one d
    exact hd q hq_sq

/-- Whenever d is a non-square in K, QuadExt K d is a genuine commutative field. -/
def quadExtFieldStructure (K : Type u) [FieldStructure K] (d : K) (hd : NonSquare d) :
    FieldStructure (QuadExt K d) where
  inv z :=
    let invN := FieldStructure.inv (z.re * z.re + -(d * (z.im * z.im)))
    ⟨z.re * invN, -(z.im * invN)⟩
  mul_comm := QuadExt.mul_comm
  zero_ne_one h := by
    have h01 : (0 : K) = 1 := congrArg QuadExt.re h
    exact FieldStructure.zero_ne_one h01
  mul_inv_cancel z hz := by
    let N := z.re * z.re + -(d * (z.im * z.im))
    have hN : N ≠ 0 := QuadExt.norm_ne_zero hd hz
    let invN := FieldStructure.inv N
    apply QuadExt.ext
    · change z.re * (z.re * invN) + d * (z.im * -(z.im * invN)) = 1
      rw [← UnitalRing.mul_assoc z.re z.re invN, mul_neg_ring z.im, mul_neg_ring d,
          ← UnitalRing.mul_assoc z.im z.im invN, ← UnitalRing.mul_assoc d (z.im * z.im) invN,
          ← neg_mul_ring (d * (z.im * z.im)) invN, ← UnitalRing.right_distrib]
      exact FieldStructure.mul_inv_cancel N hN
    · change z.re * -(z.im * invN) + z.im * (z.re * invN) = 0
      rw [mul_neg_ring z.re, ← UnitalRing.mul_assoc z.re z.im invN,
          ← UnitalRing.mul_assoc z.im z.re invN, FieldStructure.mul_comm z.im z.re,
          AddCommGrp.neg_add_cancel]
  inv_zero := by
    apply QuadExt.ext
    · change (0 : K) * FieldStructure.inv ((0 : K) * 0 + -(d * ((0 : K) * 0))) = 0
      rw [zero_mul_ring]
    · change -((0 : K) * FieldStructure.inv ((0 : K) * 0 + -(d * ((0 : K) * 0)))) = 0
      rw [zero_mul_ring, neg_zero_grp]

/-- Explicit Gaussian rational field Q(i) = QuadExt RatQ (-1). -/
abbrev Qi : Type := QuadExt RatQ (-(1 : RatQ))

instance : FieldStructure Qi :=
  quadExtFieldStructure RatQ (-(1 : RatQ)) ratQ_nonSquare_neg_one

/-- Explicit real quadratic field Q(√2) = QuadExt RatQ 2. -/
abbrev Qsqrt2 : Type := QuadExt RatQ ((1 : RatQ) + 1)

instance : FieldStructure Qsqrt2 :=
  quadExtFieldStructure RatQ ((1 : RatQ) + 1) ratQ_nonSquare_two

/-- Canonical injective field/ring embedding K ↪ QuadExt K d. -/
def QuadExt.embed (K : Type u) [FieldStructure K] (d : K) : RingHom K (QuadExt K d) where
  toFun c := ⟨c, 0⟩
  map_zero := rfl
  map_one := rfl
  map_add c1 c2 := QuadExt.ext rfl (AddCommGrp.zero_add 0).symm
  map_mul c1 c2 := QuadExt.ext
    (by
      change c1 * c2 = c1 * c2 + d * ((0 : K) * 0)
      rw [zero_mul_ring, mul_zero_ring, add_zero_grp])
    (by
      change (0 : K) = c1 * 0 + 0 * c2
      rw [mul_zero_ring, zero_mul_ring, AddCommGrp.zero_add])

theorem QuadExt.embed_injective {K : Type u} [FieldStructure K] {d : K} :
    ∀ c1 c2 : K, (QuadExt.embed K d).toFun c1 = (QuadExt.embed K d).toFun c2 → c1 = c2 := by
  intro c1 c2 h
  exact congrArg QuadExt.re h

/-- In Q(i), the element i = ⟨0, 1⟩ satisfies i^2 + 1 = 0. -/
theorem qi_has_sqrt_neg_one :
    let i_el : Qi := ⟨0, 1⟩
    i_el * i_el + 1 = 0 := by
  apply QuadExt.ext
  · change (0 : RatQ) * 0 + -(1 : RatQ) * ((1 : RatQ) * 1) + 1 = 0
    rw [zero_mul_ring, UnitalRing.mul_one, neg_mul_ring, UnitalRing.one_mul,
        AddCommGrp.zero_add, AddCommGrp.neg_add_cancel]
  · change (0 : RatQ) * 1 + (1 : RatQ) * 0 + 0 = 0
    rw [zero_mul_ring, mul_zero_ring, AddCommGrp.zero_add, AddCommGrp.zero_add]

/-- No element z ∈ Q(√2) satisfies z^2 + 1 = 0!
    Proof: Re(z^2 + 1) = a^2 + 2 b^2 + 1 > 0 in Q. -/
theorem qsqrt2_no_sqrt_neg_one (z : Qsqrt2) : z * z + 1 ≠ 0 := by
  intro h
  have hre : z.re * z.re + ((1 : RatQ) + 1) * (z.im * z.im) + 1 = 0 :=
    congrArg QuadExt.re h
  refine Quot.inductionOn z.re (fun a => Quot.inductionOn z.im (fun b hab => ?_)) hre
  have heq := RatQ.exact hab
  unfold PreRat.Rel PreRat.add PreRat.mul at heq
  dsimp at heq
  have ha_sq : 0 ≤ a.num * a.num := by
    by_cases hp : 0 ≤ a.num
    · exact Int.mul_nonneg hp hp
    · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  have hb_sq : 0 ≤ b.num * b.num := by
    by_cases hp : 0 ≤ b.num
    · exact Int.mul_nonneg hp hp
    · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  have had_pos : 0 < a.den * a.den := Int.mul_pos a.den_pos a.den_pos
  have hbd_pos : 0 < b.den * b.den := Int.mul_pos b.den_pos b.den_pos
  have hterm1 : 0 ≤ (a.num * a.num) * (1 * (b.den * b.den)) :=
    Int.mul_nonneg ha_sq (by omega)
  have hterm2 : 0 ≤ 2 * (b.num * b.num) * (a.den * a.den) :=
    Int.mul_nonneg (Int.mul_nonneg (by omega) hb_sq) (by omega)
  have hterm3 : 0 < (a.den * a.den) * (1 * (b.den * b.den)) :=
    Int.mul_pos had_pos (by omega)
  omega

/-- No unital ring homomorphism Qi → RatQ exists (hence ¬ RingIso RatQ Qi). -/
theorem no_ringHom_qi_to_ratQ : ¬ Nonempty (RingHom Qi RatQ) := by
  intro ⟨f⟩
  let i_el : Qi := ⟨0, 1⟩
  have hi : i_el * i_el + 1 = 0 := qi_has_sqrt_neg_one
  have hmap : f.toFun i_el * f.toFun i_el + 1 = 0 := by
    symm
    calc
      (0 : RatQ) = f.toFun 0 := f.map_zero.symm
      _ = f.toFun (i_el * i_el + 1) := by rw [← hi]
      _ = f.toFun (i_el * i_el) + f.toFun 1 := f.map_add _ _
      _ = f.toFun i_el * f.toFun i_el + 1 := by rw [f.map_mul, f.map_one]
  exact ratQ_no_sqrt_neg_one (f.toFun i_el) hmap

/-- No unital ring homomorphism Qi → Qsqrt2 exists (hence ¬ RingIso Qsqrt2 Qi). -/
theorem no_ringHom_qi_to_qsqrt2 : ¬ Nonempty (RingHom Qi Qsqrt2) := by
  intro ⟨f⟩
  let i_el : Qi := ⟨0, 1⟩
  have hi : i_el * i_el + 1 = 0 := qi_has_sqrt_neg_one
  have hmap : f.toFun i_el * f.toFun i_el + 1 = 0 := by
    symm
    calc
      (0 : Qsqrt2) = f.toFun 0 := f.map_zero.symm
      _ = f.toFun (i_el * i_el + 1) := by rw [← hi]
      _ = f.toFun (i_el * i_el) + f.toFun 1 := f.map_add _ _
      _ = f.toFun i_el * f.toFun i_el + 1 := by rw [f.map_mul, f.map_one]
  exact qsqrt2_no_sqrt_neg_one (f.toFun i_el) hmap

end Conjecture00000007610
