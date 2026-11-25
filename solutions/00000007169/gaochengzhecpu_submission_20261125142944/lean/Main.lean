/-
Conjecture 00000007169 — Complete Formal Analysis and Refutation in Core Lean 4.19.0
====================================================================================

Source statement (`SOURCE.md`):
  English: "Definition: Fiedler with the additive inequalities of eigenvalues.
            Conjecture: The ordering correction of additive inequalities holds,
            and the optimum of the correction is antisymmetrization.
            (antisymmetric Fiedler additive correction)"
  Chinese: "定义：Fiedler：特征值的加性不等式。猜想：Fiedler 的加性：加性不等式的排序修正
            且正的最优为反对称化。（Fiedler 反对称化加性排序最优修正）"
-/

universe u

namespace Conjecture00000007169

-- ============================================================================
-- §1. Linearly Ordered Commutative Rings, Fields, Int, and Exact Rationals Q
-- ============================================================================

class LinearOrderedCommRing (R : Type u) extends
    Add R, Sub R, Mul R, Neg R, LE R, LT R where
  toZero : OfNat R (nat_lit 0)
  toOne  : OfNat R (nat_lit 1)
  add_assoc : ∀ a b c : R, a + b + c = a + (b + c)
  add_comm  : ∀ a b : R, a + b = b + a
  zero_add  : ∀ a : R, 0 + a = a
  add_zero  : ∀ a : R, a + 0 = a
  neg_add_cancel : ∀ a : R, -a + a = 0
  sub_eq_add_neg : ∀ a b : R, a - b = a + -b
  mul_assoc : ∀ a b c : R, a * b * c = a * (b * c)
  mul_comm  : ∀ a b : R, a * b = b * a
  one_mul   : ∀ a : R, 1 * a = a
  mul_one   : ∀ a : R, a * 1 = a
  left_distrib  : ∀ a b c : R, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c
  le_refl   : ∀ a : R, a ≤ a
  le_trans  : ∀ a b c : R, a ≤ b → b ≤ c → a ≤ c
  le_antisymm : ∀ a b : R, a ≤ b → b ≤ a → a = b
  le_total  : ∀ a b : R, a ≤ b ∨ b ≤ a
  lt_iff_le_not_le : ∀ a b : R, a < b ↔ a ≤ b ∧ ¬ b ≤ a
  add_le_add_left : ∀ a b : R, a ≤ b → ∀ c : R, c + a ≤ c + b
  mul_nonneg : ∀ a b : R, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
  mul_pos    : ∀ a b : R, 0 < a → 0 < b → 0 < a * b
  zero_lt_one : (0 : R) < 1

attribute [instance] LinearOrderedCommRing.toZero LinearOrderedCommRing.toOne

class LinearOrderedField (F : Type u) extends LinearOrderedCommRing F where
  inv : F → F
  inv_zero : inv 0 = 0
  mul_inv_cancel : ∀ a : F, a ≠ 0 → a * inv a = 1

instance : LinearOrderedCommRing Int where
  toZero := inferInstance
  toOne  := inferInstance
  add_assoc := Int.add_assoc
  add_comm  := Int.add_comm
  zero_add  := Int.zero_add
  add_zero  := Int.add_zero
  neg_add_cancel := fun _ => by omega
  sub_eq_add_neg := @Int.sub_eq_add_neg
  mul_assoc := Int.mul_assoc
  mul_comm  := Int.mul_comm
  one_mul   := Int.one_mul
  mul_one   := Int.mul_one
  left_distrib  := Int.mul_add
  right_distrib := Int.add_mul
  le_refl   := Int.le_refl
  le_trans  := @Int.le_trans
  le_antisymm := @Int.le_antisymm
  le_total  := Int.le_total
  lt_iff_le_not_le := fun _ _ => by omega
  add_le_add_left := fun _ _ h _ => by omega
  mul_nonneg := fun _ _ ha hb => Int.mul_nonneg ha hb
  mul_pos    := fun _ _ ha hb => Int.mul_pos ha hb
  zero_lt_one := by decide

/-- Unreduced integer fractions `num / den` with `0 < den`, used to construct `QField`. -/
structure RawRat where
  num : Int
  den : Int
  den_pos : 0 < den

namespace RawRat

theorem mul_mul_mul_comm (a b c d : Int) : (a * b) * (c * d) = (a * c) * (b * d) := by
  rw [Int.mul_assoc, ← Int.mul_assoc b c d, Int.mul_comm b c, Int.mul_assoc c b d, ← Int.mul_assoc]

theorem cancel_right {a b c : Int} (hc : 0 < c) (h : a * c = b * c) : a = b :=
  Int.eq_of_mul_eq_mul_right (by omega) h

def rel (p q : RawRat) : Prop := p.num * q.den = q.num * p.den

theorem rel_refl (p : RawRat) : rel p p := rfl
theorem rel_symm {p q : RawRat} (h : rel p q) : rel q p := h.symm
theorem rel_trans {p q r : RawRat} (hpq : rel p q) (hqr : rel q r) : rel p r := by
  unfold rel at *
  apply cancel_right q.den_pos
  calc (p.num * r.den) * q.den
      = (p.num * q.den) * r.den := by rw [Int.mul_assoc, Int.mul_comm r.den q.den, ← Int.mul_assoc]
    _ = (q.num * p.den) * r.den := by rw [hpq]
    _ = (q.num * r.den) * p.den := by rw [Int.mul_assoc, Int.mul_comm p.den r.den, ← Int.mul_assoc]
    _ = (r.num * q.den) * p.den := by rw [hqr]
    _ = (r.num * p.den) * q.den := by rw [Int.mul_assoc, Int.mul_comm q.den p.den, ← Int.mul_assoc]

instance setoid : Setoid RawRat where
  r := rel
  iseqv := ⟨rel_refl, rel_symm, rel_trans⟩

def zero : RawRat := ⟨0, 1, by decide⟩
def one  : RawRat := ⟨1, 1, by decide⟩
def add (p q : RawRat) : RawRat :=
  ⟨p.num * q.den + q.num * p.den, p.den * q.den, Int.mul_pos p.den_pos q.den_pos⟩
def neg (p : RawRat) : RawRat := ⟨-p.num, p.den, p.den_pos⟩
def mul (p q : RawRat) : RawRat :=
  ⟨p.num * q.num, p.den * q.den, Int.mul_pos p.den_pos q.den_pos⟩
def inv (p : RawRat) : RawRat :=
  if hpos : 0 < p.num then ⟨p.den, p.num, hpos⟩
  else if _ : p.num < 0 then ⟨-p.den, -p.num, by omega⟩
  else zero
def le (p q : RawRat) : Prop := p.num * q.den ≤ q.num * p.den

theorem add_term_eq (a b c d e f : Int) (h : a * d = c * b) :
    (a * e) * (d * f) = (c * f) * (b * e) := by
  rw [mul_mul_mul_comm a e d f, h, Int.mul_comm e f, ← mul_mul_mul_comm c f b e]

theorem add_wd {p1 p2 q1 q2 : RawRat} (hp : rel p1 p2) (hq : rel q1 q2) :
    rel (add p1 q1) (add p2 q2) := by
  unfold rel add at *; dsimp
  rw [Int.add_mul, Int.add_mul]
  have h1 := add_term_eq p1.num p1.den p2.num p2.den q1.den q2.den hp
  have h2 := add_term_eq q1.num q1.den q2.num q2.den p1.den p2.den hq
  rw [Int.mul_comm q2.den p2.den, Int.mul_comm q1.den p1.den] at h2
  omega

theorem neg_wd {p1 p2 : RawRat} (hp : rel p1 p2) : rel (neg p1) (neg p2) := by
  unfold rel neg at *; dsimp; rw [Int.neg_mul, Int.neg_mul, hp]

theorem mul_wd {p1 p2 q1 q2 : RawRat} (hp : rel p1 p2) (hq : rel q1 q2) :
    rel (mul p1 q1) (mul p2 q2) := by
  unfold rel mul at *; dsimp; rw [mul_mul_mul_comm, hp, hq, mul_mul_mul_comm]

theorem inv_wd {p1 p2 : RawRat} (hp : rel p1 p2) : rel (inv p1) (inv p2) := by
  unfold rel at hp
  have hp1_pos := p1.den_pos
  have hp2_pos := p2.den_pos
  by_cases h1p : 0 < p1.num
  · have h2p : 0 < p2.num := by
      have lhs : 0 < p1.num * p2.den := Int.mul_pos h1p hp2_pos
      cases Int.le_total p2.num 0 with
      | inr _ =>
        by_cases hz : p2.num = 0
        · rw [hz, Int.zero_mul] at hp; omega
        · omega
      | inl hle =>
        have rhs : p2.num * p1.den ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg hle (by omega)
        omega
    unfold inv rel; simp [h1p, h2p]
    rw [Int.mul_comm p1.den p2.num, ← hp, Int.mul_comm]
  · by_cases h1n : p1.num < 0
    · have h2n : p2.num < 0 := by
        have lhs : p1.num * p2.den < 0 := Int.mul_neg_of_neg_of_pos h1n hp2_pos
        cases Int.le_total 0 p2.num with
        | inl hge =>
          have rhs : 0 ≤ p2.num * p1.den := Int.mul_nonneg hge (by omega)
          omega
        | inr _ =>
          by_cases hz : p2.num = 0
          · rw [hz, Int.zero_mul] at hp; omega
          · omega
      have h2np : ¬ 0 < p2.num := by omega
      unfold inv rel; simp [h1p, h1n, h2np, h2n]
      rw [Int.neg_mul_neg, Int.neg_mul_neg, Int.mul_comm p1.den p2.num, ← hp, Int.mul_comm]
    · have h1z : p1.num = 0 := by omega
      have h2z : p2.num = 0 := by
        rw [h1z, Int.zero_mul] at hp
        exact cancel_right hp1_pos (by omega)
      have h2np : ¬ 0 < p2.num := by omega
      have h2nn : ¬ p2.num < 0 := by omega
      unfold inv rel zero; simp [h1p, h1n, h2np, h2nn]

theorem le_of_mul_le_mul_right_pos {a b c : Int} (hc : 0 < c) (h : a * c ≤ b * c) : a ≤ b := by
  cases Int.le_total a b with
  | inl hab => exact hab
  | inr _ =>
    by_cases heq : a = b
    · omega
    · have hpos : 0 < (a - b) * c := Int.mul_pos (by omega) hc
      rw [Int.sub_mul] at hpos; omega

theorem le_wd {p1 p2 q1 q2 : RawRat} (hp : rel p1 p2) (hq : rel q1 q2) :
    le p1 q1 ↔ le p2 q2 := by
  unfold le rel at *
  have hd1 : 0 < p1.den * q1.den := Int.mul_pos p1.den_pos q1.den_pos
  have hd2 : 0 < p2.den * q2.den := Int.mul_pos p2.den_pos q2.den_pos
  have eq1 := add_term_eq p1.num p1.den p2.num p2.den q1.den q2.den hp
  have eq2 := add_term_eq q1.num q1.den q2.num q2.den p1.den p2.den hq
  rw [Int.mul_comm q2.den p2.den, Int.mul_comm q1.den p1.den] at eq2
  constructor
  · intro h
    apply le_of_mul_le_mul_right_pos hd1
    have hdiff : 0 ≤ (q1.num * p1.den - p1.num * q1.den) * (p2.den * q2.den) :=
      Int.mul_nonneg (by omega) (by omega)
    rw [Int.sub_mul] at hdiff; omega
  · intro h
    apply le_of_mul_le_mul_right_pos hd2
    have hdiff : 0 ≤ (q2.num * p2.den - p2.num * q2.den) * (p1.den * q1.den) :=
      Int.mul_nonneg (by omega) (by omega)
    rw [Int.sub_mul] at hdiff; omega

theorem left_distrib_helper (u rden pden qden : Int) :
    (u * rden) * ((pden * qden) * (pden * rden)) =
    (u * (pden * rden)) * (pden * (qden * rden)) := by
  calc (u * rden) * ((pden * qden) * (pden * rden))
      = (u * (pden * rden)) * (rden * (pden * qden)) := by
          rw [Int.mul_comm (pden * qden) (pden * rden), mul_mul_mul_comm]
    _ = (u * (pden * rden)) * (pden * (qden * rden)) := by
          rw [← Int.mul_assoc rden pden qden, Int.mul_comm rden pden, Int.mul_assoc pden rden qden,
              Int.mul_comm rden qden]

theorem left_distrib_rel (p q r : RawRat) : rel (mul p (add q r)) (add (mul p q) (mul p r)) := by
  unfold rel mul add; dsimp
  rw [Int.mul_add, Int.add_mul, Int.add_mul]
  rw [← Int.mul_assoc p.num q.num r.den, ← Int.mul_assoc p.num r.num q.den]
  have h1 := left_distrib_helper (p.num * q.num) r.den p.den q.den
  have h2 : ((p.num * r.num) * q.den) * ((p.den * q.den) * (p.den * r.den)) =
            ((p.num * r.num) * (p.den * q.den)) * (p.den * (q.den * r.den)) := by
    calc ((p.num * r.num) * q.den) * ((p.den * q.den) * (p.den * r.den))
        = ((p.num * r.num) * (p.den * q.den)) * (q.den * (p.den * r.den)) :=
            mul_mul_mul_comm _ _ _ _
      _ = ((p.num * r.num) * (p.den * q.den)) * (p.den * (q.den * r.den)) := by
            rw [← Int.mul_assoc q.den p.den r.den, Int.mul_comm q.den p.den, Int.mul_assoc p.den q.den r.den]
  omega

end RawRat

/-- Exact rational numbers `Q`, constructively witnessing `LinearOrderedField`. -/
abbrev QField := Quotient RawRat.setoid

namespace QField

def mk (n : Int) (d : Int) (hd : 0 < d) : QField := Quotient.mk _ ⟨n, d, hd⟩

instance : OfNat QField (nat_lit 0) where ofNat := Quotient.mk _ RawRat.zero
instance : OfNat QField (nat_lit 1) where ofNat := Quotient.mk _ RawRat.one
instance : Add QField where
  add := Quotient.lift₂ (fun a b => Quotient.mk _ (RawRat.add a b))
    (fun _ _ _ _ ha hb => Quotient.sound (RawRat.add_wd ha hb))
instance : Neg QField where
  neg := Quotient.lift (fun a => Quotient.mk _ (RawRat.neg a))
    (fun _ _ ha => Quotient.sound (RawRat.neg_wd ha))
instance : Sub QField where
  sub a b := a + -b
instance : Mul QField where
  mul := Quotient.lift₂ (fun a b => Quotient.mk _ (RawRat.mul a b))
    (fun _ _ _ _ ha hb => Quotient.sound (RawRat.mul_wd ha hb))
def inv : QField → QField :=
  Quotient.lift (fun a => Quotient.mk _ (RawRat.inv a))
    (fun _ _ ha => Quotient.sound (RawRat.inv_wd ha))
instance : LE QField where
  le := Quotient.lift₂ RawRat.le (fun _ _ _ _ ha hb => propext (RawRat.le_wd ha hb))
instance : LT QField where
  lt a b := a ≤ b ∧ ¬ b ≤ a

private theorem mul_comm_q (a b : QField) : a * b = b * a := by
  refine Quotient.inductionOn₂ a b fun p q => Quotient.sound ?_
  change RawRat.rel (RawRat.mul p q) (RawRat.mul q p)
  unfold RawRat.rel RawRat.mul; dsimp
  rw [Int.mul_comm p.num, Int.mul_comm p.den]

private theorem left_distrib_q (a b c : QField) : a * (b + c) = a * b + a * c :=
  Quotient.inductionOn₃ a b c fun p q r => Quotient.sound (RawRat.left_distrib_rel p q r)

instance : LinearOrderedField QField where
  toZero := inferInstance
  toOne  := inferInstance
  add_assoc a b c := by
    refine Quotient.inductionOn₃ a b c fun p q r => Quotient.sound ?_
    change RawRat.rel (RawRat.add (RawRat.add p q) r) (RawRat.add p (RawRat.add q r))
    unfold RawRat.rel RawRat.add; dsimp
    have num_eq : (p.num * q.den + q.num * p.den) * r.den + r.num * (p.den * q.den) =
                  p.num * (q.den * r.den) + (q.num * r.den + r.num * q.den) * p.den := by
      rw [Int.add_mul, Int.add_mul, Int.mul_assoc p.num q.den r.den]
      have h1 : (q.num * p.den) * r.den = (q.num * r.den) * p.den := by
        rw [Int.mul_assoc, Int.mul_comm p.den r.den, ← Int.mul_assoc]
      have h2 : r.num * (p.den * q.den) = (r.num * q.den) * p.den := by
        rw [Int.mul_comm p.den q.den, ← Int.mul_assoc]
      rw [h1, h2, Int.add_assoc]
    rw [num_eq, Int.mul_assoc p.den q.den r.den]
  add_comm a b := by
    refine Quotient.inductionOn₂ a b fun p q => Quotient.sound ?_
    change RawRat.rel (RawRat.add p q) (RawRat.add q p)
    unfold RawRat.rel RawRat.add; dsimp
    rw [Int.add_comm (p.num * q.den), Int.mul_comm p.den q.den]
  zero_add a := by
    refine Quotient.inductionOn a fun p => Quotient.sound ?_
    change RawRat.rel (RawRat.add RawRat.zero p) p
    unfold RawRat.rel RawRat.add RawRat.zero; dsimp
    simp [Int.zero_mul, Int.zero_add, Int.mul_one, Int.one_mul]
  add_zero a := by
    refine Quotient.inductionOn a fun p => Quotient.sound ?_
    change RawRat.rel (RawRat.add p RawRat.zero) p
    unfold RawRat.rel RawRat.add RawRat.zero; dsimp
    simp [Int.zero_mul, Int.add_zero, Int.mul_one]
  neg_add_cancel a := by
    refine Quotient.inductionOn a fun p => Quotient.sound ?_
    change RawRat.rel (RawRat.add (RawRat.neg p) p) RawRat.zero
    unfold RawRat.rel RawRat.add RawRat.neg RawRat.zero; dsimp
    rw [Int.neg_mul]; omega
  sub_eq_add_neg _ _ := rfl
  mul_assoc a b c := by
    refine Quotient.inductionOn₃ a b c fun p q r => Quotient.sound ?_
    change RawRat.rel (RawRat.mul (RawRat.mul p q) r) (RawRat.mul p (RawRat.mul q r))
    unfold RawRat.rel RawRat.mul; dsimp
    rw [Int.mul_assoc p.num, Int.mul_assoc p.den]
  mul_comm := mul_comm_q
  one_mul a := by
    refine Quotient.inductionOn a fun p => Quotient.sound ?_
    change RawRat.rel (RawRat.mul RawRat.one p) p
    unfold RawRat.rel RawRat.mul RawRat.one; dsimp
    simp [Int.one_mul]
  mul_one a := by
    refine Quotient.inductionOn a fun p => Quotient.sound ?_
    change RawRat.rel (RawRat.mul p RawRat.one) p
    unfold RawRat.rel RawRat.mul RawRat.one; dsimp
    simp [Int.mul_one]
  left_distrib := left_distrib_q
  right_distrib a b c := by
    rw [mul_comm_q (a + b) c, left_distrib_q, mul_comm_q c a, mul_comm_q c b]
  le_refl a := Quotient.inductionOn a fun _ => Int.le_refl _
  le_trans a b c := by
    refine Quotient.inductionOn₃ a b c fun p q r hpq hqr => ?_
    change RawRat.le p q at hpq
    change RawRat.le q r at hqr
    change RawRat.le p r
    unfold RawRat.le at *
    have hp_pos := p.den_pos
    have hq_pos := q.den_pos
    have hr_pos := r.den_pos
    apply RawRat.le_of_mul_le_mul_right_pos hq_pos
    have h1 : 0 ≤ (q.num * p.den - p.num * q.den) * r.den := Int.mul_nonneg (by omega) (by omega)
    have h2 : 0 ≤ (r.num * q.den - q.num * r.den) * p.den := Int.mul_nonneg (by omega) (by omega)
    rw [Int.sub_mul] at h1 h2
    have e1 : (p.num * r.den) * q.den = (p.num * q.den) * r.den := by
      rw [Int.mul_assoc, Int.mul_comm r.den q.den, ← Int.mul_assoc]
    have e2 : (q.num * p.den) * r.den = (q.num * r.den) * p.den := by
      rw [Int.mul_assoc, Int.mul_comm p.den r.den, ← Int.mul_assoc]
    have e3 : (r.num * q.den) * p.den = (r.num * p.den) * q.den := by
      rw [Int.mul_assoc, Int.mul_comm q.den p.den, ← Int.mul_assoc]
    omega
  le_antisymm a b := by
    refine Quotient.inductionOn₂ a b fun p q hpq hqp => Quotient.sound ?_
    change RawRat.le p q at hpq
    change RawRat.le q p at hqp
    change RawRat.rel p q
    unfold RawRat.le RawRat.rel at *; omega
  le_total a b := Quotient.inductionOn₂ a b fun p q => Int.le_total (p.num * q.den) (q.num * p.den)
  lt_iff_le_not_le _ _ := Iff.rfl
  add_le_add_left a b := by
    refine Quotient.inductionOn₂ a b fun p q hab c => ?_
    refine Quotient.inductionOn c fun r => ?_
    change RawRat.le p q at hab
    change RawRat.le (RawRat.add r p) (RawRat.add r q)
    unfold RawRat.le RawRat.add at *; dsimp
    have hr_pos := r.den_pos
    have hdiff : 0 ≤ (q.num * p.den - p.num * q.den) * (r.den * r.den) :=
      Int.mul_nonneg (by omega) (Int.mul_nonneg (by omega) (by omega))
    rw [Int.sub_mul] at hdiff
    have e1 : (r.num * p.den + p.num * r.den) * (r.den * q.den) =
              (r.num * r.den) * (p.den * q.den) + (p.num * q.den) * (r.den * r.den) := by
      rw [Int.add_mul, RawRat.mul_mul_mul_comm r.num p.den r.den q.den,
          Int.mul_comm r.den q.den, RawRat.mul_mul_mul_comm p.num r.den q.den r.den]
    have e2 : (r.num * q.den + q.num * r.den) * (r.den * p.den) =
              (r.num * r.den) * (p.den * q.den) + (q.num * p.den) * (r.den * r.den) := by
      rw [Int.add_mul, RawRat.mul_mul_mul_comm r.num q.den r.den p.den, Int.mul_comm q.den p.den,
          Int.mul_comm r.den p.den, RawRat.mul_mul_mul_comm q.num r.den p.den r.den]
    omega
  mul_nonneg a b := by
    refine Quotient.inductionOn₂ a b fun p q ha hb => ?_
    change RawRat.le RawRat.zero p at ha
    change RawRat.le RawRat.zero q at hb
    change RawRat.le RawRat.zero (RawRat.mul p q)
    unfold RawRat.le RawRat.mul RawRat.zero at *; dsimp at *
    have hprod : 0 ≤ p.num * q.num := Int.mul_nonneg (by omega) (by omega)
    omega
  mul_pos a b := by
    refine Quotient.inductionOn₂ a b fun p q ha hb => ?_
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    change RawRat.le RawRat.zero p at ha1
    change ¬ RawRat.le p RawRat.zero at ha2
    change RawRat.le RawRat.zero q at hb1
    change ¬ RawRat.le q RawRat.zero at hb2
    refine ⟨?_, ?_⟩
    · change RawRat.le RawRat.zero (RawRat.mul p q)
      unfold RawRat.le RawRat.mul RawRat.zero at *; dsimp at *
      have hprod : 0 ≤ p.num * q.num := Int.mul_nonneg (by omega) (by omega)
      omega
    · change ¬ RawRat.le (RawRat.mul p q) RawRat.zero
      unfold RawRat.le RawRat.mul RawRat.zero at *; dsimp at *
      have hprod : 0 < p.num * q.num := Int.mul_pos (by omega) (by omega)
      omega
  zero_lt_one := by
    refine ⟨?_, ?_⟩
    · change RawRat.le RawRat.zero RawRat.one
      unfold RawRat.le RawRat.zero RawRat.one; dsimp; decide
    · change ¬ RawRat.le RawRat.one RawRat.zero
      unfold RawRat.le RawRat.one RawRat.zero; dsimp; decide
  inv := inv
  inv_zero := Quotient.sound rfl
  mul_inv_cancel a := by
    refine Quotient.inductionOn a fun p ha => ?_
    have hp_ne : p.num ≠ 0 := by
      intro h0
      apply ha
      apply Quotient.sound
      change RawRat.rel p RawRat.zero
      unfold RawRat.rel RawRat.zero; dsimp; omega
    apply Quotient.sound
    change RawRat.rel (RawRat.mul p (RawRat.inv p)) RawRat.one
    unfold RawRat.rel RawRat.mul RawRat.inv RawRat.one
    split
    · next _ => dsimp; rw [Int.mul_one, Int.one_mul, Int.mul_comm]
    · next _ =>
      split
      · next _ =>
        dsimp
        rw [Int.mul_one, Int.one_mul, Int.mul_neg, Int.mul_neg, Int.mul_comm]
      · omega

theorem mk_eq_iff {n1 d1 n2 d2 : Int} (hd1 : 0 < d1) (hd2 : 0 < d2) :
    mk n1 d1 hd1 = mk n2 d2 hd2 ↔ n1 * d2 = n2 * d1 :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem mk_le_iff {n1 d1 n2 d2 : Int} (hd1 : 0 < d1) (hd2 : 0 < d2) :
    mk n1 d1 hd1 ≤ mk n2 d2 hd2 ↔ n1 * d2 ≤ n2 * d1 := Iff.rfl

theorem mk_lt_iff {n1 d1 n2 d2 : Int} (hd1 : 0 < d1) (hd2 : 0 < d2) :
    mk n1 d1 hd1 < mk n2 d2 hd2 ↔ n1 * d2 < n2 * d1 := by
  change (n1 * d2 ≤ n2 * d1 ∧ ¬ n2 * d1 ≤ n1 * d2) ↔ n1 * d2 < n2 * d1
  omega

theorem mk_add {n1 d1 n2 d2 : Int} (hd1 : 0 < d1) (hd2 : 0 < d2) :
    mk n1 d1 hd1 + mk n2 d2 hd2 = mk (n1 * d2 + n2 * d1) (d1 * d2) (Int.mul_pos hd1 hd2) := rfl

theorem mk_neg {n d : Int} (hd : 0 < d) :
    -(mk n d hd) = mk (-n) d hd := rfl

theorem mk_sub {n1 d1 n2 d2 : Int} (hd1 : 0 < d1) (hd2 : 0 < d2) :
    mk n1 d1 hd1 - mk n2 d2 hd2 = mk (n1 * d2 - n2 * d1) (d1 * d2) (Int.mul_pos hd1 hd2) := by
  change mk n1 d1 hd1 + -(mk n2 d2 hd2) = _
  rw [mk_neg, mk_add, mk_eq_iff (Int.mul_pos hd1 hd2) (Int.mul_pos hd1 hd2)]
  rw [Int.neg_mul, ← Int.sub_eq_add_neg]

theorem mk_mul {n1 d1 n2 d2 : Int} (hd1 : 0 < d1) (hd2 : 0 < d2) :
    mk n1 d1 hd1 * mk n2 d2 hd2 = mk (n1 * n2) (d1 * d2) (Int.mul_pos hd1 hd2) := rfl

def ofInt (n : Int) : QField := mk n 1 (by decide)

theorem ofInt_zero : ofInt 0 = 0 := rfl
theorem ofInt_one  : ofInt 1 = 1 := rfl
theorem ofInt_add (a b : Int) : ofInt (a + b) = ofInt a + ofInt b := by
  unfold ofInt; rw [mk_add, mk_eq_iff (by decide) (by decide)]; omega
theorem ofInt_neg (a : Int) : ofInt (-a) = -(ofInt a) := rfl
theorem ofInt_sub (a b : Int) : ofInt (a - b) = ofInt a - ofInt b := by
  unfold ofInt; rw [mk_sub, mk_eq_iff (by decide) (by decide)]; omega
theorem ofInt_mul (a b : Int) : ofInt (a * b) = ofInt a * ofInt b := by
  unfold ofInt; rw [mk_mul, mk_eq_iff (by decide) (by decide)]; omega
theorem ofInt_le_iff (a b : Int) : ofInt a ≤ ofInt b ↔ a ≤ b := by
  unfold ofInt; rw [mk_le_iff]; omega
theorem ofInt_lt_iff (a b : Int) : ofInt a < ofInt b ↔ a < b := by
  unfold ofInt; rw [mk_lt_iff]; omega
theorem ofInt_inj {a b : Int} (h : ofInt a = ofInt b) : a = b := by
  unfold ofInt at h; rw [mk_eq_iff] at h; omega

end QField

-- ============================================================================
-- §2. General Ordered-Ring & Ordered-Field Lemmas
-- ============================================================================

section RingLemmas
variable {R : Type u} [LinearOrderedCommRing R]

theorem add_assoc_r (a b c : R) : a + b + c = a + (b + c) := LinearOrderedCommRing.add_assoc a b c
theorem add_comm_r (a b : R) : a + b = b + a := LinearOrderedCommRing.add_comm a b
theorem zero_add_r (a : R) : 0 + a = a := LinearOrderedCommRing.zero_add a
theorem add_zero_r (a : R) : a + 0 = a := LinearOrderedCommRing.add_zero a
theorem neg_add_cancel_r (a : R) : -a + a = 0 := LinearOrderedCommRing.neg_add_cancel a
theorem sub_eq_add_neg_r (a b : R) : a - b = a + -b := LinearOrderedCommRing.sub_eq_add_neg a b
theorem mul_assoc_r (a b c : R) : a * b * c = a * (b * c) := LinearOrderedCommRing.mul_assoc a b c
theorem mul_comm_r (a b : R) : a * b = b * a := LinearOrderedCommRing.mul_comm a b
theorem one_mul_r (a : R) : 1 * a = a := LinearOrderedCommRing.one_mul a
theorem mul_one_r (a : R) : a * 1 = a := LinearOrderedCommRing.mul_one a
theorem left_distrib_r (a b c : R) : a * (b + c) = a * b + a * c := LinearOrderedCommRing.left_distrib a b c
theorem right_distrib_r (a b c : R) : (a + b) * c = a * c + b * c := LinearOrderedCommRing.right_distrib a b c
theorem le_refl_r (a : R) : a ≤ a := LinearOrderedCommRing.le_refl a
theorem le_trans_r {a b c : R} : a ≤ b → b ≤ c → a ≤ c := LinearOrderedCommRing.le_trans a b c
theorem le_antisymm_r {a b : R} : a ≤ b → b ≤ a → a = b := LinearOrderedCommRing.le_antisymm a b
theorem le_total_r (a b : R) : a ≤ b ∨ b ≤ a := LinearOrderedCommRing.le_total a b
theorem lt_iff_le_not_le_r (a b : R) : a < b ↔ a ≤ b ∧ ¬ b ≤ a := LinearOrderedCommRing.lt_iff_le_not_le a b

theorem add_neg_cancel_r (a : R) : a + -a = 0 := by rw [add_comm_r, neg_add_cancel_r]
theorem sub_self_r (a : R) : a - a = 0 := by rw [sub_eq_add_neg_r, add_neg_cancel_r]

theorem add_left_cancel_r {a b c : R} (h : a + b = a + c) : b = c := by
  calc b = 0 + b := (zero_add_r b).symm
    _ = (-a + a) + b := by rw [neg_add_cancel_r]
    _ = -a + (a + b) := add_assoc_r _ _ _
    _ = -a + (a + c) := by rw [h]
    _ = (-a + a) + c := (add_assoc_r _ _ _).symm
    _ = 0 + c := by rw [neg_add_cancel_r]
    _ = c := zero_add_r c

theorem add_right_cancel_r {a b c : R} (h : a + c = b + c) : a = b := by
  apply add_left_cancel_r (a := c)
  rw [add_comm_r c a, add_comm_r c b, h]

theorem eq_neg_of_add_eq_zero_r {a b : R} (h : a + b = 0) : a = -b := by
  apply add_right_cancel_r (c := b)
  rw [h, neg_add_cancel_r]

theorem neg_zero_r : -(0 : R) = 0 := (eq_neg_of_add_eq_zero_r (zero_add_r 0)).symm

theorem neg_neg_r (a : R) : -(-a) = a := (eq_neg_of_add_eq_zero_r (add_neg_cancel_r a)).symm

theorem neg_add_r (a b : R) : -(a + b) = -a + -b := by
  symm; apply eq_neg_of_add_eq_zero_r
  calc (-a + -b) + (a + b)
      = -a + (-b + (a + b)) := add_assoc_r _ _ _
    _ = -a + ((-b + b) + a) := by rw [add_comm_r a b, ← add_assoc_r (-b) b a]
    _ = -a + (0 + a) := by rw [neg_add_cancel_r]
    _ = -a + a := by rw [zero_add_r]
    _ = 0 := neg_add_cancel_r a

theorem zero_mul_r (a : R) : (0 : R) * a = 0 := by
  apply add_left_cancel_r (a := 0 * a)
  rw [← right_distrib_r, zero_add_r, add_zero_r]

theorem mul_zero_r (a : R) : a * (0 : R) = 0 := by rw [mul_comm_r, zero_mul_r]

theorem neg_mul_r (a b : R) : (-a) * b = -(a * b) := by
  apply eq_neg_of_add_eq_zero_r
  rw [← right_distrib_r, neg_add_cancel_r, zero_mul_r]

theorem mul_neg_r (a b : R) : a * (-b) = -(a * b) := by
  rw [mul_comm_r, neg_mul_r, mul_comm_r]

theorem neg_mul_neg_r (a b : R) : (-a) * (-b) = a * b := by
  rw [neg_mul_r, mul_neg_r, neg_neg_r]

theorem sub_mul_r (a b c : R) : (a - b) * c = a * c - b * c := by
  rw [sub_eq_add_neg_r, right_distrib_r, neg_mul_r, ← sub_eq_add_neg_r]

theorem mul_sub_r (a b c : R) : a * (b - c) = a * b - a * c := by
  rw [sub_eq_add_neg_r, left_distrib_r, mul_neg_r, ← sub_eq_add_neg_r]

theorem sub_eq_zero_iff_r {a b : R} : a - b = 0 ↔ a = b := by
  constructor
  · intro h
    apply add_right_cancel_r (c := -b)
    rw [← sub_eq_add_neg_r, h, add_neg_cancel_r]
  · intro h; rw [h, sub_self_r]

theorem add_le_add_right_r {a b : R} (h : a ≤ b) (c : R) : a + c ≤ b + c := by
  rw [add_comm_r a c, add_comm_r b c]
  exact LinearOrderedCommRing.add_le_add_left a b h c

theorem add_le_add_r {a b c d : R} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  le_trans_r (add_le_add_right_r h1 c) (LinearOrderedCommRing.add_le_add_left c d h2 b)

theorem lt_of_lt_of_le_r {a b c : R} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  rw [lt_iff_le_not_le_r] at *
  refine ⟨le_trans_r h1.1 h2, fun hca => h1.2 (le_trans_r h2 hca)⟩

theorem lt_of_le_of_lt_r {a b c : R} (h1 : a ≤ b) (h2 : b < c) : a < c := by
  rw [lt_iff_le_not_le_r] at *
  refine ⟨le_trans_r h1 h2.1, fun hca => h2.2 (le_trans_r hca h1)⟩

theorem lt_trans_r {a b c : R} (h1 : a < b) (h2 : b < c) : a < c :=
  lt_of_lt_of_le_r h1 ((lt_iff_le_not_le_r b c).mp h2).1

theorem le_of_lt_r {a b : R} (h : a < b) : a ≤ b := ((lt_iff_le_not_le_r a b).mp h).1

theorem ne_of_lt_r {a b : R} (h : a < b) : a ≠ b := by
  intro heq; subst heq
  exact ((lt_iff_le_not_le_r a a).mp h).2 (le_refl_r a)

theorem add_lt_add_left_r {a b : R} (h : a < b) (c : R) : c + a < c + b := by
  rw [lt_iff_le_not_le_r] at *
  refine ⟨LinearOrderedCommRing.add_le_add_left a b h.1 c, fun hle => h.2 ?_⟩
  have h' := LinearOrderedCommRing.add_le_add_left _ _ hle (-c)
  rwa [← add_assoc_r, neg_add_cancel_r, zero_add_r, ← add_assoc_r, neg_add_cancel_r, zero_add_r] at h'

theorem add_lt_add_right_r {a b : R} (h : a < b) (c : R) : a + c < b + c := by
  rw [add_comm_r a c, add_comm_r b c]; exact add_lt_add_left_r h c

theorem add_lt_add_of_lt_of_le_r {a b c d : R} (h1 : a < b) (h2 : c ≤ d) : a + c < b + d :=
  lt_of_lt_of_le_r (add_lt_add_right_r h1 c) (LinearOrderedCommRing.add_le_add_left c d h2 b)

theorem add_lt_add_of_le_of_lt_r {a b c d : R} (h1 : a ≤ b) (h2 : c < d) : a + c < b + d :=
  lt_of_le_of_lt_r (add_le_add_right_r h1 c) (add_lt_add_left_r h2 b)

theorem sub_nonneg_iff_r {a b : R} : 0 ≤ a - b ↔ b ≤ a := by
  constructor
  · intro h
    have h' := add_le_add_right_r h b
    rwa [zero_add_r, sub_eq_add_neg_r, add_assoc_r, neg_add_cancel_r, add_zero_r] at h'
  · intro h
    have h' := add_le_add_right_r h (-b)
    rwa [add_neg_cancel_r, ← sub_eq_add_neg_r] at h'

theorem sub_pos_iff_r {a b : R} : 0 < a - b ↔ b < a := by
  rw [lt_iff_le_not_le_r, lt_iff_le_not_le_r, sub_nonneg_iff_r]
  constructor
  · rintro ⟨hba, hn⟩
    refine ⟨hba, fun hab => hn ?_⟩
    have h' := add_le_add_right_r hab (-b)
    rwa [add_neg_cancel_r, ← sub_eq_add_neg_r] at h'
  · rintro ⟨hba, hnab⟩
    refine ⟨hba, fun hle => hnab ?_⟩
    have h' := add_le_add_right_r hle b
    rwa [zero_add_r, sub_eq_add_neg_r, add_assoc_r, neg_add_cancel_r, add_zero_r] at h'

theorem mul_le_mul_of_nonneg_left_r {a b c : R} (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by
  rw [← sub_nonneg_iff_r, ← mul_sub_r]
  exact LinearOrderedCommRing.mul_nonneg c (b - a) hc (sub_nonneg_iff_r.mpr h)

theorem mul_le_mul_of_nonneg_right_r {a b c : R} (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  rw [mul_comm_r a c, mul_comm_r b c]
  exact mul_le_mul_of_nonneg_left_r h hc

theorem mul_lt_mul_of_pos_right_r {a b c : R} (h : a < b) (hc : 0 < c) : a * c < b * c := by
  rw [← sub_pos_iff_r, ← sub_mul_r]
  exact LinearOrderedCommRing.mul_pos (b - a) c (sub_pos_iff_r.mpr h) hc

theorem sq_nonneg_r (a : R) : 0 ≤ a * a := by
  cases le_total_r 0 a with
  | inl ha => exact LinearOrderedCommRing.mul_nonneg a a ha ha
  | inr ha =>
    have hna : 0 ≤ -a := by
      have h' := add_le_add_right_r ha (-a)
      rwa [add_neg_cancel_r, zero_add_r] at h'
    have hp := LinearOrderedCommRing.mul_nonneg (-a) (-a) hna hna
    rwa [neg_mul_neg_r] at hp

theorem sq_pos_of_ne_zero_r {a : R} (ha : a ≠ 0) : 0 < a * a := by
  cases le_total_r 0 a with
  | inl hge =>
    have hgt : 0 < a := (lt_iff_le_not_le_r 0 a).mpr ⟨hge, fun hle => ha (le_antisymm_r hle hge)⟩
    exact LinearOrderedCommRing.mul_pos a a hgt hgt
  | inr hle =>
    have hlt : a < 0 := (lt_iff_le_not_le_r a 0).mpr ⟨hle, fun hge => ha (le_antisymm_r hle hge)⟩
    have hpos : 0 < -a := by
      have h' := add_lt_add_right_r hlt (-a)
      rwa [add_neg_cancel_r, zero_add_r] at h'
    have hp := LinearOrderedCommRing.mul_pos (-a) (-a) hpos hpos
    rwa [neg_mul_neg_r] at hp

theorem sq_eq_zero_iff_r {a : R} : a * a = 0 ↔ a = 0 := by
  constructor
  · intro h
    by_cases ha : a = 0
    · exact ha
    · exact False.elim ((ne_of_lt_r (sq_pos_of_ne_zero_r ha)) h.symm)
  · intro h; rw [h, zero_mul_r]

theorem two_pos_r : (0 : R) < 1 + 1 := by
  have h := add_lt_add_of_lt_of_le_r (LinearOrderedCommRing.zero_lt_one (R := R)) (le_refl_r (1 : R))
  rw [zero_add_r] at h
  exact lt_trans_r LinearOrderedCommRing.zero_lt_one h

theorem eq_zero_of_add_self_eq_zero_r {a : R} (h : a + a = 0) : a = 0 := by
  by_cases ha : a = 0
  · exact ha
  · cases le_total_r 0 a with
    | inl hge =>
      have hgt : 0 < a := (lt_iff_le_not_le_r 0 a).mpr ⟨hge, fun hle => ha (le_antisymm_r hle hge)⟩
      have h2 : 0 < a + a := by
        have ht := add_lt_add_of_lt_of_le_r hgt hge
        rwa [zero_add_r] at ht
      exact False.elim ((ne_of_lt_r h2) h.symm)
    | inr hle =>
      have hlt : a < 0 := (lt_iff_le_not_le_r a 0).mpr ⟨hle, fun hge => ha (le_antisymm_r hle hge)⟩
      have h2 : a + a < 0 := by
        have ht := add_lt_add_of_lt_of_le_r hlt hle
        rwa [add_zero_r] at ht
      exact False.elim ((ne_of_lt_r h2) h)

end RingLemmas

section FieldLemmas
variable {F : Type u} [LinearOrderedField F]

def twoF : F := 1 + 1
def halfF : F := LinearOrderedField.inv (twoF (F := F))

theorem twoF_ne_zero : (twoF : F) ≠ 0 := (ne_of_lt_r two_pos_r).symm

theorem two_mul_half : (twoF : F) * halfF = 1 :=
  LinearOrderedField.mul_inv_cancel twoF twoF_ne_zero

theorem half_add_half (a : F) : halfF * a + halfF * a = a := by
  rw [← right_distrib_r, show halfF + halfF = (1 + 1 : F) * halfF by
    rw [right_distrib_r, one_mul_r], show (1 + 1 : F) = twoF from rfl, two_mul_half, one_mul_r]

end FieldLemmas

-- ============================================================================
-- §3. Finite Sums, Finite Products, and Cayley-Dickson Complex Numbers
-- ============================================================================

section FinOps
variable {R : Type u} [LinearOrderedCommRing R]

def finSum : (n : Nat) → (Fin n → R) → R
  | 0, _ => 0
  | n + 1, f => f ⟨0, Nat.zero_lt_succ n⟩ + finSum n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

def finProd : (n : Nat) → (Fin n → R) → R
  | 0, _ => 1
  | n + 1, f => f ⟨0, Nat.zero_lt_succ n⟩ * finProd n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

theorem finSum_congr {n : Nat} {f g : Fin n → R} (h : ∀ i, f i = g i) :
    finSum n f = finSum n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [finSum]
    rw [h ⟨0, Nat.zero_lt_succ m⟩, ih (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]

theorem finProd_congr {n : Nat} {f g : Fin n → R} (h : ∀ i, f i = g i) :
    finProd n f = finProd n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [finProd]
    rw [h ⟨0, Nat.zero_lt_succ m⟩, ih (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]

theorem finSum_zero (n : Nat) : finSum n (fun _ => (0 : R)) = 0 := by
  induction n with
  | zero => rfl
  | succ m ih => simp only [finSum]; rw [ih, add_zero_r]

theorem finSum_add (n : Nat) (f g : Fin n → R) :
    finSum n (fun i => f i + g i) = finSum n f + finSum n g := by
  induction n with
  | zero => symm; exact zero_add_r 0
  | succ m ih =>
    simp only [finSum]
    rw [ih]
    calc (f ⟨0, _⟩ + g ⟨0, _⟩) + (finSum m _ + finSum m _)
        = f ⟨0, _⟩ + (g ⟨0, _⟩ + (finSum m _ + finSum m _)) := add_assoc_r _ _ _
      _ = f ⟨0, _⟩ + ((g ⟨0, _⟩ + finSum m _) + finSum m _) := by rw [← add_assoc_r (g ⟨0, _⟩)]
      _ = f ⟨0, _⟩ + ((finSum m _ + g ⟨0, _⟩) + finSum m _) := by rw [add_comm_r (g ⟨0, _⟩)]
      _ = f ⟨0, _⟩ + (finSum m _ + (g ⟨0, _⟩ + finSum m _)) := by rw [add_assoc_r (finSum m _)]
      _ = (f ⟨0, _⟩ + finSum m _) + (g ⟨0, _⟩ + finSum m _) := (add_assoc_r _ _ _).symm

theorem finSum_neg (n : Nat) (f : Fin n → R) :
    finSum n (fun i => -f i) = -finSum n f := by
  induction n with
  | zero => exact neg_zero_r.symm
  | succ m ih => simp only [finSum]; rw [ih, neg_add_r]

theorem finSum_sub (n : Nat) (f g : Fin n → R) :
    finSum n (fun i => f i - g i) = finSum n f - finSum n g := by
  have h : (fun i => f i - g i) = (fun i => f i + -g i) := by
    funext i; exact sub_eq_add_neg_r _ _
  rw [h, finSum_add, finSum_neg, ← sub_eq_add_neg_r]

theorem finSum_mul_left (n : Nat) (c : R) (f : Fin n → R) :
    finSum n (fun i => c * f i) = c * finSum n f := by
  induction n with
  | zero => symm; exact mul_zero_r c
  | succ m ih => simp only [finSum]; rw [ih, left_distrib_r]

theorem finSum_mul_right (n : Nat) (f : Fin n → R) (c : R) :
    finSum n (fun i => f i * c) = finSum n f * c := by
  induction n with
  | zero => symm; exact zero_mul_r c
  | succ m ih => simp only [finSum]; rw [ih, right_distrib_r]

theorem finSum_le {n : Nat} {f g : Fin n → R} (h : ∀ i, f i ≤ g i) :
    finSum n f ≤ finSum n g := by
  induction n with
  | zero => exact le_refl_r 0
  | succ m ih =>
    simp only [finSum]
    exact add_le_add_r (h ⟨0, Nat.zero_lt_succ m⟩) (ih (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))

theorem finSum_nonneg {n : Nat} {f : Fin n → R} (h : ∀ i, 0 ≤ f i) :
    0 ≤ finSum n f := by
  rw [← finSum_zero n]; exact finSum_le h

theorem finProd_nonneg {n : Nat} {f : Fin n → R} (h : ∀ i, 0 ≤ f i) :
    0 ≤ finProd n f := by
  induction n with
  | zero => exact le_of_lt_r LinearOrderedCommRing.zero_lt_one
  | succ m ih =>
    simp only [finProd]
    exact LinearOrderedCommRing.mul_nonneg _ _ (h ⟨0, Nat.zero_lt_succ m⟩)
      (ih (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))

theorem finProd_pos {n : Nat} {f : Fin n → R} (h : ∀ i, 0 < f i) :
    0 < finProd n f := by
  induction n with
  | zero => exact LinearOrderedCommRing.zero_lt_one
  | succ m ih =>
    simp only [finProd]
    exact LinearOrderedCommRing.mul_pos _ _ (h ⟨0, Nat.zero_lt_succ m⟩)
      (ih (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))

theorem finSum_comm (m n : Nat) (f : Fin m → Fin n → R) :
    finSum m (fun i => finSum n (fun j => f i j)) =
    finSum n (fun j => finSum m (fun i => f i j)) := by
  induction m with
  | zero =>
    simp only [finSum]
    symm; exact finSum_zero n
  | succ k ih =>
    simp only [finSum]
    rw [ih, ← finSum_add]

theorem finSum_delta {n : Nat} (i0 : Fin n) (g : Fin n → R) :
    finSum n (fun j => if j = i0 then g j else 0) = g i0 := by
  induction n with
  | zero => exact Fin.elim0 i0
  | succ m ih =>
    simp only [finSum]
    rcases i0 with ⟨k, hk⟩
    cases k with
    | zero =>
      have h0 : (if (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) = ⟨0, hk⟩ then g ⟨0, Nat.zero_lt_succ m⟩ else 0) =
                g ⟨0, hk⟩ := by simp
      have hrest : finSum m (fun j : Fin m =>
          if (⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ : Fin (m + 1)) = ⟨0, hk⟩ then g ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ else 0) = 0 := by
        rw [finSum_congr (g := fun _ => 0)]
        · exact finSum_zero m
        · intro j; simp [Fin.ext_iff]
      rw [h0, hrest, add_zero_r]
    | succ k' =>
      have h0 : (if (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) = ⟨k' + 1, hk⟩ then g ⟨0, Nat.zero_lt_succ m⟩ else 0) = 0 := by
        simp [Fin.ext_iff]
      have hk' : k' < m := Nat.lt_of_succ_lt_succ hk
      have hrest : finSum m (fun j : Fin m =>
          if (⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ : Fin (m + 1)) = ⟨k' + 1, hk⟩
          then g ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ else 0) = g ⟨k' + 1, hk⟩ := by
        have eq_fn : (fun j : Fin m =>
            if (⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ : Fin (m + 1)) = ⟨k' + 1, hk⟩
            then g ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ else 0) =
            (fun j : Fin m => if j = ⟨k', hk'⟩ then g ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ else 0) := by
          funext j
          by_cases hj : j = ⟨k', hk'⟩
          · subst hj; simp
          · have hne : (⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ : Fin (m + 1)) ≠ ⟨k' + 1, hk⟩ := by
              intro heq; apply hj; exact Fin.ext (Nat.succ.inj (Fin.ext_iff.mp heq))
            simp [hj, hne]
        rw [eq_fn, ih ⟨k', hk'⟩ (fun j => g ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)]
      rw [h0, zero_add_r, hrest]

/-- Split a non-zero index `r = ⟨r'+1, _⟩` out of `finSum (m+1) f` for clean 2-element swaps. -/
theorem finSum_extract {n : Nat} (r : Fin n) (f : Fin n → R) :
    finSum n f = f r + finSum n (fun i => if i = r then 0 else f i) := by
  have hdecomp : f = (fun i => (if i = r then f i else 0) + (if i = r then 0 else f i)) := by
    funext i
    by_cases hi : i = r
    · subst hi; simp [add_zero_r]
    · simp [hi, zero_add_r]
  conv => lhs; rw [hdecomp]
  rw [finSum_add, finSum_delta]

theorem finProd_extract {n : Nat} (r : Fin n) (f : Fin n → R) :
    finProd n f = f r * finProd n (fun i => if i = r then 1 else f i) := by
  induction n with
  | zero => exact Fin.elim0 r
  | succ m ih =>
    simp only [finProd]
    rcases r with ⟨k, hk⟩
    cases k with
    | zero =>
      have h0 : (if (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) = ⟨0, hk⟩ then (1 : R) else f ⟨0, Nat.zero_lt_succ m⟩) = 1 := by simp
      have hrest : finProd m (fun i : Fin m =>
          if (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (m + 1)) = ⟨0, hk⟩ then 1 else f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) =
          finProd m (fun i : Fin m => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) := by
        apply finProd_congr; intro i; simp [Fin.ext_iff]
      rw [h0, one_mul_r, hrest]
    | succ k' =>
      have hk' : k' < m := Nat.lt_of_succ_lt_succ hk
      have h0 : (if (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) = ⟨k' + 1, hk⟩ then (1 : R) else f ⟨0, Nat.zero_lt_succ m⟩) =
          f ⟨0, Nat.zero_lt_succ m⟩ := by simp [Fin.ext_iff]
      have hrest : finProd m (fun i : Fin m =>
          if (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (m + 1)) = ⟨k' + 1, hk⟩ then 1 else f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) =
          finProd m (fun i : Fin m => if i = ⟨k', hk'⟩ then 1 else f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) := by
        apply finProd_congr; intro i
        by_cases hi : i = ⟨k', hk'⟩
        · subst hi; simp
        · have hne : (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (m + 1)) ≠ ⟨k' + 1, hk⟩ := by
            intro heq; apply hi; exact Fin.ext (Nat.succ.inj (Fin.ext_iff.mp heq))
          simp [hi, hne]
      rw [h0, hrest, ih ⟨k', hk'⟩ (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]
      calc f ⟨0, _⟩ * (f ⟨k' + 1, hk⟩ * finProd m _)
          = (f ⟨0, _⟩ * f ⟨k' + 1, hk⟩) * finProd m _ := (mul_assoc_r _ _ _).symm
        _ = (f ⟨k' + 1, hk⟩ * f ⟨0, _⟩) * finProd m _ := by rw [mul_comm_r (f ⟨0, _⟩)]
        _ = f ⟨k' + 1, hk⟩ * (f ⟨0, _⟩ * finProd m _) := mul_assoc_r _ _ _

end FinOps

/-- Cayley-Dickson complexification `R + i R` over an ordered commutative ring `R`. -/
structure Complex (R : Type u) where
  re : R
  im : R
deriving DecidableEq

namespace Complex
variable {R : Type u} [LinearOrderedCommRing R]

def zero : Complex R := ⟨0, 0⟩
def one  : Complex R := ⟨1, 0⟩
def I    : Complex R := ⟨0, 1⟩
def ofReal (x : R) : Complex R := ⟨x, 0⟩
def add (z w : Complex R) : Complex R := ⟨z.re + w.re, z.im + w.im⟩
def neg (z : Complex R) : Complex R := ⟨-z.re, -z.im⟩
def sub (z w : Complex R) : Complex R := ⟨z.re - w.re, z.im - w.im⟩
def mul (z w : Complex R) : Complex R := ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩
def conj (z : Complex R) : Complex R := ⟨z.re, -z.im⟩
def normSq (z : Complex R) : R := z.re * z.re + z.im * z.im

instance : OfNat (Complex R) (nat_lit 0) where ofNat := zero
instance : OfNat (Complex R) (nat_lit 1) where ofNat := one
instance : Add (Complex R) where add := add
instance : Neg (Complex R) where neg := neg
instance : Sub (Complex R) where sub := sub
instance : Mul (Complex R) where mul := mul

omit [LinearOrderedCommRing R] in
@[ext] theorem ext {z w : Complex R} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z; cases w; simp_all

theorem normSq_nonneg (z : Complex R) : 0 ≤ normSq z := by
  unfold normSq
  have h := add_le_add_r (sq_nonneg_r z.re) (sq_nonneg_r z.im)
  rwa [zero_add_r] at h

theorem normSq_eq_zero_iff {z : Complex R} : normSq z = 0 ↔ z = 0 := by
  constructor
  · intro h
    unfold normSq at h
    have hre0 : z.re = 0 := by
      by_cases hr : z.re = 0
      · exact hr
      · have hp := add_lt_add_of_lt_of_le_r (sq_pos_of_ne_zero_r hr) (sq_nonneg_r z.im)
        rw [add_zero_r] at hp
        exact False.elim ((ne_of_lt_r hp) h.symm)
    have him0 : z.im = 0 := by
      rw [hre0, zero_mul_r, zero_add_r] at h
      exact sq_eq_zero_iff_r.mp h
    exact ext hre0 him0
  · intro h; subst h; unfold normSq; change 0 * 0 + 0 * 0 = (0 : R); rw [zero_mul_r, add_zero_r]

end Complex

-- ============================================================================
-- §4. Real & Complex Matrix Algebra, Cartesian Decomposition & Bendixson Bound
-- ============================================================================

abbrev RMat (R : Type u) (n : Nat) := Fin n → Fin n → R
abbrev CMat (R : Type u) (n : Nat) := Fin n → Fin n → Complex R

section RealMatrices
variable {R : Type u} [LinearOrderedCommRing R]

def zeroMat (n : Nat) : RMat R n := fun _ _ => 0
def idMat (n : Nat) : RMat R n := fun i j => if i = j then 1 else 0
def diagMat {n : Nat} (d : Fin n → R) : RMat R n := fun i j => if i = j then d i else 0
def matAdd {n : Nat} (A B : RMat R n) : RMat R n := fun i j => A i j + B i j
def matSub {n : Nat} (A B : RMat R n) : RMat R n := fun i j => A i j - B i j
def matNeg {n : Nat} (A : RMat R n) : RMat R n := fun i j => -(A i j)
def matScale {n : Nat} (c : R) (A : RMat R n) : RMat R n := fun i j => c * A i j
def transpose {n : Nat} (A : RMat R n) : RMat R n := fun i j => A j i
def matMul {n : Nat} (A B : RMat R n) : RMat R n :=
  fun i j => finSum n (fun k => A i k * B k j)
def commutator {n : Nat} (A B : RMat R n) : RMat R n :=
  matSub (matMul A B) (matMul B A)
def trace {n : Nat} (A : RMat R n) : R := finSum n (fun i => A i i)
def frobNormSq {n : Nat} (A : RMat R n) : R :=
  finSum n (fun i => finSum n (fun j => A i j * A i j))
def matVec {n : Nat} (A : RMat R n) (x : Fin n → R) : Fin n → R :=
  fun i => finSum n (fun j => A i j * x j)
def dotProd {n : Nat} (x y : Fin n → R) : R :=
  finSum n (fun i => x i * y i)
def quadForm {n : Nat} (A : RMat R n) (x : Fin n → R) : R :=
  dotProd x (matVec A x)

def IsSym {n : Nat} (A : RMat R n) : Prop := transpose A = A
def IsSkewSym {n : Nat} (K : RMat R n) : Prop := transpose K = matNeg K
def IsOrthogonal {n : Nat} (Q : RMat R n) : Prop :=
  matMul (transpose Q) Q = idMat n ∧ matMul Q (transpose Q) = idMat n

theorem trace_add {n : Nat} (A B : RMat R n) : trace (matAdd A B) = trace A + trace B :=
  finSum_add n (fun i => A i i) (fun i => B i i)

theorem isSym_diag {n : Nat} (d : Fin n → R) : IsSym (diagMat d) := by
  funext i j; unfold transpose diagMat
  by_cases h : i = j
  · subst h; simp
  · have hji : j ≠ i := fun e => h e.symm
    simp [h, hji]

theorem isSym_add {n : Nat} {A B : RMat R n} (hA : IsSym A) (hB : IsSym B) :
    IsSym (matAdd A B) := by
  funext i j; unfold transpose matAdd
  have eA : A j i = A i j := congrFun (congrFun hA i) j
  have eB : B j i = B i j := congrFun (congrFun hB i) j
  rw [eA, eB]

theorem isSkewSym_zero (n : Nat) : IsSkewSym (zeroMat n : RMat R n) := by
  funext i j; unfold transpose matNeg zeroMat; exact neg_zero_r.symm

theorem skewSym_diag_zero {n : Nat} {K : RMat R n} (hK : IsSkewSym K) (i : Fin n) :
    K i i = 0 := by
  have hi : K i i = -(K i i) := congrFun (congrFun hK i) i
  apply eq_zero_of_add_self_eq_zero_r
  calc K i i + K i i = K i i + -(K i i) := by rw [← hi]
    _ = 0 := add_neg_cancel_r _

theorem trace_eq_zero_of_isSkewSym {n : Nat} {K : RMat R n} (hK : IsSkewSym K) :
    trace K = 0 := by
  unfold trace
  rw [finSum_congr (g := fun _ => 0)]
  · exact finSum_zero n
  · intro i; exact skewSym_diag_zero hK i

theorem isSkewSym_commutator_of_isSym {n : Nat} {A B : RMat R n}
    (hA : IsSym A) (hB : IsSym B) : IsSkewSym (commutator A B) := by
  funext i j
  unfold transpose matNeg commutator matSub matMul
  have hBA : finSum n (fun k => A j k * B k i) = finSum n (fun k => B i k * A k j) := by
    apply finSum_congr; intro k
    have eA : A j k = A k j := congrFun (congrFun hA k) j
    have eB : B k i = B i k := congrFun (congrFun hB i) k
    rw [eA, eB, mul_comm_r]
  have hAB : finSum n (fun k => B j k * A k i) = finSum n (fun k => A i k * B k j) := by
    apply finSum_congr; intro k
    have eB : B j k = B k j := congrFun (congrFun hB k) j
    have eA : A k i = A i k := congrFun (congrFun hA i) k
    rw [eB, eA, mul_comm_r]
  rw [hBA, hAB, sub_eq_add_neg_r, sub_eq_add_neg_r, neg_add_r, neg_neg_r, add_comm_r]

/-- Bendixson's Quadratic-Form Vanishing Identity: `⟨x, K x⟩ = 0` for all `K^T = -K`. -/
theorem quadForm_skewSym_eq_zero {n : Nat} {K : RMat R n} (hK : IsSkewSym K) (x : Fin n → R) :
    quadForm K x = 0 := by
  apply eq_zero_of_add_self_eq_zero_r
  unfold quadForm dotProd matVec
  have h1 : finSum n (fun i => x i * finSum n (fun j => K i j * x j)) =
            finSum n (fun i => finSum n (fun j => x i * (K i j * x j))) := by
    apply finSum_congr; intro i; exact (finSum_mul_left n (x i) _).symm
  have h2 : finSum n (fun i => finSum n (fun j => x i * (K i j * x j))) =
            finSum n (fun i => finSum n (fun j => -(x i * (K i j * x j)))) := by
    conv => lhs; rw [finSum_comm]
    apply finSum_congr; intro i
    apply finSum_congr; intro j
    have hij : K j i = -(K i j) := congrFun (congrFun hK i) j
    rw [hij, neg_mul_r, mul_neg_r]
    apply congrArg Neg.neg
    calc x j * (K i j * x i)
        = x j * (x i * K i j) := by rw [mul_comm_r (K i j) (x i)]
      _ = (x j * x i) * K i j := (mul_assoc_r _ _ _).symm
      _ = (x i * x j) * K i j := by rw [mul_comm_r (x j) (x i)]
      _ = x i * (x j * K i j) := mul_assoc_r _ _ _
      _ = x i * (K i j * x j) := by rw [mul_comm_r (x j) (K i j)]
  have hsum : finSum n (fun i => finSum n (fun j => x i * (K i j * x j))) +
              finSum n (fun i => finSum n (fun j => x i * (K i j * x j))) = 0 := by
    conv => rhs; rw [← add_neg_cancel_r (finSum n (fun i => finSum n (fun j => x i * (K i j * x j))))]
    apply congrArg (fun t => finSum n (fun i => finSum n (fun j => x i * (K i j * x j))) + t)
    calc finSum n (fun i => finSum n (fun j => x i * (K i j * x j)))
        = finSum n (fun i => finSum n (fun j => -(x i * (K i j * x j)))) := h2
      _ = finSum n (fun i => -finSum n (fun j => x i * (K i j * x j))) :=
            finSum_congr (fun i => finSum_neg n _)
      _ = -finSum n (fun i => finSum n (fun j => x i * (K i j * x j))) := finSum_neg n _
  rw [h1]
  exact hsum

end RealMatrices

section CartesianField
variable {F : Type u} [LinearOrderedField F]

/-- Symmetric part `S(M) = (1/2)(M + M^T)`. -/
def symPart {n : Nat} (M : RMat F n) : RMat F n :=
  matScale halfF (matAdd M (transpose M))

/-- Matrix antisymmetrization (skew-symmetric part) `A(M) = (1/2)(M - M^T)`. -/
def skewPart {n : Nat} (M : RMat F n) : RMat F n :=
  matScale halfF (matSub M (transpose M))

theorem isSym_symPart {n : Nat} (M : RMat F n) : IsSym (symPart M) := by
  funext i j; dsimp [transpose, symPart, matScale, matAdd]
  rw [add_comm_r (M j i) (M i j)]

theorem isSkewSym_skewPart {n : Nat} (M : RMat F n) : IsSkewSym (skewPart M) := by
  funext i j; dsimp [transpose, matNeg, skewPart, matScale, matSub]
  rw [← mul_neg_r]
  apply congrArg (fun t => halfF * t)
  rw [sub_eq_add_neg_r, sub_eq_add_neg_r, neg_add_r, neg_neg_r, add_comm_r]

theorem cartesian_decomp {n : Nat} (M : RMat F n) :
    matAdd (symPart M) (skewPart M) = M := by
  funext i j; dsimp [matAdd, symPart, skewPart, matScale, matSub, transpose]
  rw [← left_distrib_r]
  have h : (M i j + M j i) + (M i j - M j i) = M i j + M i j := by
    calc (M i j + M j i) + (M i j - M j i)
        = M i j + (M j i + (M i j + -(M j i))) := by rw [sub_eq_add_neg_r, add_assoc_r]
      _ = M i j + ((M j i + -(M j i)) + M i j) := by
            rw [add_comm_r (M i j) (-(M j i)), ← add_assoc_r (M j i)]
      _ = M i j + (0 + M i j) := by rw [add_neg_cancel_r]
      _ = M i j + M i j := by rw [zero_add_r]
  rw [h, left_distrib_r, half_add_half]

theorem cartesian_unique {n : Nat} {M S K : RMat F n}
    (hS : IsSym S) (hK : IsSkewSym K) (hsum : matAdd S K = M) :
    S = symPart M ∧ K = skewPart M := by
  constructor
  · funext i j; dsimp [symPart, matScale, matAdd, transpose]
    have h1 : M i j = S i j + K i j := (congrFun (congrFun hsum i) j).symm
    have h2 : M j i = S i j + -(K i j) := by
      have e : M j i = S j i + K j i := (congrFun (congrFun hsum j) i).symm
      have eS : S j i = S i j := congrFun (congrFun hS i) j
      have eK : K j i = -(K i j) := congrFun (congrFun hK i) j
      rw [eS, eK] at e; exact e
    rw [h1, h2]
    have hcancel : (S i j + K i j) + (S i j + -(K i j)) = S i j + S i j := by
      calc (S i j + K i j) + (S i j + -(K i j))
          = S i j + (K i j + (S i j + -(K i j))) := add_assoc_r _ _ _
        _ = S i j + ((K i j + -(K i j)) + S i j) := by
              rw [add_comm_r (S i j) (-(K i j)), ← add_assoc_r (K i j)]
        _ = S i j + (0 + S i j) := by rw [add_neg_cancel_r]
        _ = S i j + S i j := by rw [zero_add_r]
    rw [hcancel, left_distrib_r, half_add_half]
  · funext i j; dsimp [skewPart, matScale, matSub, transpose]
    have h1 : M i j = S i j + K i j := (congrFun (congrFun hsum i) j).symm
    have h2 : M j i = S i j + -(K i j) := by
      have e : M j i = S j i + K j i := (congrFun (congrFun hsum j) i).symm
      have eS : S j i = S i j := congrFun (congrFun hS i) j
      have eK : K j i = -(K i j) := congrFun (congrFun hK i) j
      rw [eS, eK] at e; exact e
    rw [h1, h2]
    have hcancel : (S i j + K i j) - (S i j + -(K i j)) = K i j + K i j := by
      rw [sub_eq_add_neg_r, neg_add_r, neg_neg_r]
      calc (S i j + K i j) + (-S i j + K i j)
          = (K i j + S i j) + (-S i j + K i j) := by rw [add_comm_r (S i j) (K i j)]
        _ = K i j + (S i j + (-S i j + K i j)) := add_assoc_r _ _ _
        _ = K i j + ((S i j + -S i j) + K i j) := by rw [← add_assoc_r (S i j)]
        _ = K i j + (0 + K i j) := by rw [add_neg_cancel_r]
        _ = K i j + K i j := by rw [zero_add_r]
    rw [hcancel, left_distrib_r, half_add_half]

theorem skewPart_eq_zero_iff_isSym {n : Nat} (M : RMat F n) :
    skewPart M = zeroMat n ↔ IsSym M := by
  constructor
  · intro hk
    have hcd := cartesian_decomp M
    rw [hk] at hcd
    have heq : M = symPart M := by
      funext i j
      have e := (congrFun (congrFun hcd i) j).symm
      unfold matAdd zeroMat at e
      rwa [add_zero_r] at e
    rw [heq]; exact isSym_symPart M
  · intro hM
    exact (cartesian_unique hM (isSkewSym_zero n) (by
      funext i j; unfold matAdd zeroMat; exact add_zero_r _)).2.symm

/-- Bendixson quadratic-form identity: antisymmetric part contributes zero to `⟨x, M x⟩`. -/
theorem quadForm_eq_symPart {n : Nat} (M : RMat F n) (x : Fin n → F) :
    quadForm M x = quadForm (symPart M) x := by
  conv => lhs; rw [← cartesian_decomp M]
  have hlin : quadForm (matAdd (symPart M) (skewPart M)) x =
              quadForm (symPart M) x + quadForm (skewPart M) x := by
    unfold quadForm dotProd matVec matAdd
    rw [← finSum_add]
    apply finSum_congr; intro i
    rw [← left_distrib_r, ← finSum_add]
    apply congrArg (fun t => x i * t)
    apply finSum_congr; intro j; exact right_distrib_r _ _ _
  rw [hlin, quadForm_skewSym_eq_zero (isSkewSym_skewPart M) x, add_zero_r]

end CartesianField

-- ============================================================================
-- §5. Positive Benchmark I: All-n Rearrangement & Fiedler Permutation Theorems
-- ============================================================================

section PermRearrangement
variable {R : Type u} [LinearOrderedCommRing R]

abbrev lastFin (m : Nat) : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
abbrev castSuccFin {m : Nat} (i : Fin m) : Fin (m + 1) := ⟨i.1, Nat.lt_succ_of_lt i.2⟩

theorem castSuccFin_inj {m : Nat} {i r : Fin m} (h : castSuccFin i = castSuccFin r) : i = r := by
  rcases i with ⟨iv, _⟩; rcases r with ⟨rv, _⟩
  dsimp [castSuccFin] at h
  injection h with hv
  subst hv; rfl

theorem finSum_snoc (m : Nat) (f : Fin (m + 1) → R) :
    finSum (m + 1) f =
    finSum m (fun i => f (castSuccFin i)) + f (lastFin m) := by
  induction m with
  | zero =>
    change f ⟨0, _⟩ + 0 = 0 + f ⟨0, _⟩
    rw [add_zero_r, zero_add_r]
  | succ k ih =>
    change f ⟨0, _⟩ + finSum (k + 1) (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) =
           (f ⟨0, _⟩ + finSum k (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ (Nat.lt_succ_of_lt i.2)⟩)) + f ⟨k + 1, _⟩
    rw [ih (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩), add_assoc_r]

theorem finProd_snoc (m : Nat) (f : Fin (m + 1) → R) :
    finProd (m + 1) f =
    finProd m (fun i => f (castSuccFin i)) * f (lastFin m) := by
  induction m with
  | zero =>
    change f ⟨0, _⟩ * 1 = 1 * f ⟨0, _⟩
    rw [mul_one_r, one_mul_r]
  | succ k ih =>
    change f ⟨0, _⟩ * finProd (k + 1) (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) =
           (f ⟨0, _⟩ * finProd k (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ (Nat.lt_succ_of_lt i.2)⟩)) * f ⟨k + 1, _⟩
    rw [ih (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩), mul_assoc_r]

/-- Elementary 2-point rearrangement identity: `(a1*b1 + a2*b2) - (a1*b2 + a2*b1) = (a1-a2)*(b1-b2)`. -/
theorem swap_diff_identity (a1 a2 b1 b2 : R) :
    (a1 * b1 + a2 * b2) - (a1 * b2 + a2 * b1) = (a1 - a2) * (b1 - b2) := by
  symm
  rw [sub_mul_r, mul_sub_r, mul_sub_r]
  rw [sub_eq_add_neg_r (a1 * b1 - a1 * b2), sub_eq_add_neg_r (a1 * b1),
      sub_eq_add_neg_r (a2 * b1), neg_add_r, neg_neg_r]
  rw [sub_eq_add_neg_r (a1 * b1 + a2 * b2), neg_add_r]
  calc (a1 * b1 + -(a1 * b2)) + (-(a2 * b1) + a2 * b2)
      = a1 * b1 + (-(a1 * b2) + (a2 * b2 + -(a2 * b1))) := by
          rw [add_comm_r (-(a2 * b1)) (a2 * b2), add_assoc_r]
    _ = a1 * b1 + (a2 * b2 + (-(a1 * b2) + -(a2 * b1))) := by
          rw [← add_assoc_r (-(a1 * b2)), add_comm_r (-(a1 * b2)) (a2 * b2), add_assoc_r]
    _ = (a1 * b1 + a2 * b2) + (-(a1 * b2) + -(a2 * b1)) := (add_assoc_r _ _ _).symm

theorem rearrangement_2_le {a1 a2 b1 b2 : R} (ha : a2 ≤ a1) (hb : b2 ≤ b1) :
    a1 * b2 + a2 * b1 ≤ a1 * b1 + a2 * b2 := by
  rw [← sub_nonneg_iff_r, swap_diff_identity]
  exact LinearOrderedCommRing.mul_nonneg _ _ (sub_nonneg_iff_r.mpr ha) (sub_nonneg_iff_r.mpr hb)

theorem rearrangement_2_lt {a1 a2 b1 b2 : R} (ha : a2 < a1) (hb : b2 < b1) :
    a1 * b2 + a2 * b1 < a1 * b1 + a2 * b2 := by
  rw [← sub_pos_iff_r, swap_diff_identity]
  exact LinearOrderedCommRing.mul_pos _ _ (sub_pos_iff_r.mpr ha) (sub_pos_iff_r.mpr hb)

/-- Fiedler's 2-point product swap identity: `(a1+b2)*(a2+b1) - (a1+b1)*(a2+b2) = (a1-a2)*(b1-b2)`. -/
theorem fiedler_swap_identity (a1 a2 b1 b2 : R) :
    (a1 + b2) * (a2 + b1) - (a1 + b1) * (a2 + b2) = (a1 - a2) * (b1 - b2) := by
  have expand (x y u v : R) : (x + y) * (u + v) = (x * u + y * v) + (x * v + y * u) := by
    rw [right_distrib_r, left_distrib_r, left_distrib_r]
    calc (x * u + x * v) + (y * u + y * v)
        = x * u + (x * v + (y * u + y * v)) := add_assoc_r _ _ _
      _ = x * u + ((x * v + y * u) + y * v) := by rw [← add_assoc_r (x * v)]
      _ = x * u + (y * v + (x * v + y * u)) := by rw [add_comm_r (x * v + y * u) (y * v)]
      _ = (x * u + y * v) + (x * v + y * u) := (add_assoc_r _ _ _).symm
  rw [expand a1 b2 a2 b1, expand a1 b1 a2 b2, mul_comm_r b2 b1]
  have hcancel : ((a1 * a2 + b1 * b2) + (a1 * b1 + b2 * a2)) -
                 ((a1 * a2 + b1 * b2) + (a1 * b2 + b1 * a2)) =
                 (a1 * b1 + a2 * b2) - (a1 * b2 + a2 * b1) := by
    rw [mul_comm_r b2 a2, mul_comm_r b1 a2]
    let C := a1 * a2 + b1 * b2
    let X := a1 * b1 + a2 * b2
    let Y := a1 * b2 + a2 * b1
    change (C + X) - (C + Y) = X - Y
    rw [sub_eq_add_neg_r, neg_add_r]
    calc (C + X) + (-C + -Y)
        = (X + C) + (-C + -Y) := by rw [add_comm_r C X]
      _ = X + (C + (-C + -Y)) := add_assoc_r _ _ _
      _ = X + ((C + -C) + -Y) := by rw [← add_assoc_r C]
      _ = X + (0 + -Y) := by rw [add_neg_cancel_r]
      _ = X + -Y := by rw [zero_add_r]
      _ = X - Y := (sub_eq_add_neg_r X Y).symm
  rw [hcancel, swap_diff_identity]

theorem fiedler_swap_le {a1 a2 b1 b2 : R} (ha : a2 ≤ a1) (hb : b2 ≤ b1) :
    (a1 + b1) * (a2 + b2) ≤ (a1 + b2) * (a2 + b1) := by
  rw [← sub_nonneg_iff_r, fiedler_swap_identity]
  exact LinearOrderedCommRing.mul_nonneg _ _ (sub_nonneg_iff_r.mpr ha) (sub_nonneg_iff_r.mpr hb)

theorem fiedler_swap_lt {a1 a2 b1 b2 : R} (ha : a2 < a1) (hb : b2 < b1) :
    (a1 + b1) * (a2 + b2) < (a1 + b2) * (a2 + b1) := by
  rw [← sub_pos_iff_r, fiedler_swap_identity]
  exact LinearOrderedCommRing.mul_pos _ _ (sub_pos_iff_r.mpr ha) (sub_pos_iff_r.mpr hb)

/-- Bijections of `Fin n` (the symmetric group `S_n`). -/
structure Perm (n : Nat) where
  toFun     : Fin n → Fin n
  invFun    : Fin n → Fin n
  left_inv  : ∀ i, invFun (toFun i) = i
  right_inv : ∀ i, toFun (invFun i) = i

def idPerm (n : Nat) : Perm n where
  toFun i := i
  invFun i := i
  left_inv _ := rfl
  right_inv _ := rfl

def compPerm {n : Nat} (p q : Perm n) : Perm n where
  toFun i := p.toFun (q.toFun i)
  invFun i := q.invFun (p.invFun i)
  left_inv i := by rw [p.left_inv, q.left_inv]
  right_inv i := by rw [q.right_inv, p.right_inv]

def swapPerm {n : Nat} (u v : Fin n) : Perm n where
  toFun i := if i = u then v else if i = v then u else i
  invFun i := if i = u then v else if i = v then u else i
  left_inv i := by
    by_cases hiu : i = u
    · subst hiu
      by_cases huv : v = i
      · subst huv; simp
      · simp [huv]
    · by_cases hiv : i = v
      · subst hiv; simp
      · simp [hiu, hiv]
  right_inv i := by
    by_cases hiu : i = u
    · subst hiu
      by_cases huv : v = i
      · subst huv; simp
      · simp [huv]
    · by_cases hiv : i = v
      · subst hiv; simp
      · simp [hiu, hiv]

/-- The order-reversing permutation `w_0(i) = n - 1 - i` on `Fin n`. -/
def revPerm (n : Nat) : Perm n where
  toFun i := ⟨n - 1 - i.1, by omega⟩
  invFun i := ⟨n - 1 - i.1, by omega⟩
  left_inv i := by apply Fin.ext; dsimp; omega
  right_inv i := by apply Fin.ext; dsimp; omega

theorem revPerm_invol (n : Nat) (x : Fin n) :
    (revPerm n).toFun ((revPerm n).toFun x) = x :=
  (revPerm n).left_inv x

def restrictPermLast {m : Nat} (p : Perm (m + 1)) (hp : p.toFun (lastFin m) = lastFin m) : Perm m where
  toFun i :=
    ⟨(p.toFun (castSuccFin i)).1, by
      have hne : p.toFun (castSuccFin i) ≠ lastFin m := by
        intro heq
        have h1 : p.invFun (p.toFun (castSuccFin i)) = p.invFun (lastFin m) := congrArg p.invFun heq
        have h2 : p.invFun (p.toFun (lastFin m)) = p.invFun (lastFin m) := congrArg p.invFun hp
        rw [p.left_inv] at h1 h2
        have hi : castSuccFin i = lastFin m := h1.trans h2.symm
        have : i.1 = m := Fin.ext_iff.mp hi
        omega
      have hlt := (p.toFun (castSuccFin i)).2
      have hval : (p.toFun (castSuccFin i)).1 ≠ m := fun e => hne (Fin.ext e)
      omega⟩
  invFun i :=
    ⟨(p.invFun (castSuccFin i)).1, by
      have hinv : p.invFun (lastFin m) = lastFin m := by
        have h2 : p.invFun (p.toFun (lastFin m)) = p.invFun (lastFin m) := congrArg p.invFun hp
        rw [p.left_inv] at h2
        exact h2.symm
      have hne : p.invFun (castSuccFin i) ≠ lastFin m := by
        intro heq
        have h1 : p.toFun (p.invFun (castSuccFin i)) = p.toFun (lastFin m) := congrArg p.toFun heq
        have h2 : p.toFun (p.invFun (lastFin m)) = p.toFun (lastFin m) := congrArg p.toFun hinv
        rw [p.right_inv] at h1 h2
        have hi : castSuccFin i = lastFin m := h1.trans h2.symm
        have : i.1 = m := Fin.ext_iff.mp hi
        omega
      have hlt := (p.invFun (castSuccFin i)).2
      have hval : (p.invFun (castSuccFin i)).1 ≠ m := fun e => hne (Fin.ext e)
      omega⟩
  left_inv i := by
    apply Fin.ext; dsimp
    have hcast : (⟨(p.toFun (castSuccFin i)).1, _⟩ : Fin (m + 1)) = p.toFun (castSuccFin i) :=
      Fin.ext rfl
    change (p.invFun ⟨(p.toFun (castSuccFin i)).1, _⟩).1 = i.1
    rw [hcast, p.left_inv]
  right_inv i := by
    apply Fin.ext; dsimp
    have hcast : (⟨(p.invFun (castSuccFin i)).1, _⟩ : Fin (m + 1)) = p.invFun (castSuccFin i) :=
      Fin.ext rfl
    change (p.toFun ⟨(p.invFun (castSuccFin i)).1, _⟩).1 = i.1
    rw [hcast, p.right_inv]

def NonIncreasing {n : Nat} (v : Fin n → R) : Prop :=
  ∀ i j : Fin n, i.1 ≤ j.1 → v j ≤ v i

def StrictlyDecreasing {n : Nat} (v : Fin n → R) : Prop :=
  ∀ i j : Fin n, i.1 < j.1 → v j < v i

theorem nonIncreasing_of_strictlyDecreasing {n : Nat} {v : Fin n → R}
    (hv : StrictlyDecreasing v) : NonIncreasing v := by
  intro i j hij
  by_cases heq : i.1 = j.1
  · have : i = j := Fin.ext heq; subst this; exact le_refl_r _
  · exact le_of_lt_r (hv i j (by omega))

/-- All-n Upper Rearrangement Inequality: `∑ α_i β_{p(i)} ≤ ∑ α_i β_i`. -/
theorem rearrangement_upper_all_n :
    ∀ (n : Nat) (α β : Fin n → R),
      NonIncreasing α → NonIncreasing β → ∀ (p : Perm n),
      finSum n (fun i => α i * β (p.toFun i)) ≤ finSum n (fun i => α i * β i)
  | 0, _, _, _, _, _ => le_refl_r 0
  | m + 1, α, β, hα, hβ, p => by
    let α' : Fin m → R := fun i => α (castSuccFin i)
    let β' : Fin m → R := fun i => β (castSuccFin i)
    have hα' : NonIncreasing α' := fun i j hij => hα (castSuccFin i) (castSuccFin j) hij
    have hβ' : NonIncreasing β' := fun i j hij => hβ (castSuccFin i) (castSuccFin j) hij
    by_cases hfix : p.toFun (lastFin m) = lastFin m
    · let q := restrictPermLast p hfix
      rw [finSum_snoc m (fun i => α i * β (p.toFun i)), finSum_snoc m (fun i => α i * β i), hfix]
      have hmatch : (fun i : Fin m => α (castSuccFin i) * β (p.toFun (castSuccFin i))) =
                    (fun i : Fin m => α' i * β' (q.toFun i)) := by
        funext i; dsimp [α', β', q, restrictPermLast, castSuccFin]
      rw [hmatch]
      exact add_le_add_right_r (rearrangement_upper_all_n m α' β' hα' hβ' q) _
    · let r0 := p.invFun (lastFin m)
      have hr0_ne : r0 ≠ lastFin m :=
        fun heq => hfix ((congrArg p.toFun heq).symm.trans (p.right_inv (lastFin m)))
      have hr0_lt : r0.1 < m := by
        have h1 := r0.2; have h2 : r0.1 ≠ m := fun e => hr0_ne (Fin.ext e); omega
      let r : Fin m := ⟨r0.1, hr0_lt⟩
      have hr_cast : castSuccFin r = r0 := Fin.ext rfl
      let s0 := p.toFun (lastFin m)
      have hs0_lt : s0.1 < m := by
        have h1 := s0.2; have h2 : s0.1 ≠ m := fun e => hfix (Fin.ext e); omega
      let p' := compPerm p (swapPerm r0 (lastFin m))
      have hp'_fix : p'.toFun (lastFin m) = lastFin m := by
        dsimp [p', compPerm, swapPerm]
        have hne : lastFin m ≠ r0 := fun e => hr0_ne e.symm
        simp [hne, r0, p.right_inv]
      have hp'_r : p'.toFun r0 = s0 := by
        dsimp [p', compPerm, swapPerm]; simp [s0]
      have hstep : finSum (m + 1) (fun i => α i * β (p.toFun i)) ≤
                   finSum (m + 1) (fun i => α i * β (p'.toFun i)) := by
        rw [finSum_snoc m (fun i => α i * β (p.toFun i)),
            finSum_snoc m (fun i => α i * β (p'.toFun i)),
            finSum_extract r (fun i => α (castSuccFin i) * β (p.toFun (castSuccFin i))),
            finSum_extract r (fun i => α (castSuccFin i) * β (p'.toFun (castSuccFin i)))]
        have hrest : finSum m (fun i => if i = r then 0 else α (castSuccFin i) * β (p.toFun (castSuccFin i))) =
                     finSum m (fun i => if i = r then 0 else α (castSuccFin i) * β (p'.toFun (castSuccFin i))) := by
          apply finSum_congr; intro i
          by_cases hir : i = r
          · subst hir; simp
          · have hne1 : castSuccFin i ≠ r0 :=
              fun e => hir (castSuccFin_inj (e.trans hr_cast.symm))
            have hne2 : castSuccFin i ≠ lastFin m := by
              intro e; have : i.1 = m := Fin.ext_iff.mp e; omega
            dsimp [p', compPerm, swapPerm]
            simp [hir, hne1, hne2]
        rw [hrest, hr_cast, show p.toFun r0 = lastFin m from p.right_inv (lastFin m), hp'_r, hp'_fix]
        let rest := finSum m (fun i => if i = r then 0 else α (castSuccFin i) * β (p'.toFun (castSuccFin i)))
        have hswap := rearrangement_2_le
          (hα r0 (lastFin m) (Nat.le_of_lt hr0_lt))
          (hβ s0 (lastFin m) (Nat.le_of_lt hs0_lt))
        calc (α r0 * β (lastFin m) + rest) + α (lastFin m) * β s0
            = (α r0 * β (lastFin m) + α (lastFin m) * β s0) + rest := by
                rw [add_assoc_r, add_comm_r rest, ← add_assoc_r]
          _ ≤ (α r0 * β s0 + α (lastFin m) * β (lastFin m)) + rest :=
                add_le_add_right_r hswap rest
          _ = (α r0 * β s0 + rest) + α (lastFin m) * β (lastFin m) := by
                rw [add_assoc_r, add_comm_r _ rest, ← add_assoc_r]
      let q := restrictPermLast p' hp'_fix
      have htail : finSum (m + 1) (fun i => α i * β (p'.toFun i)) ≤
                   finSum (m + 1) (fun i => α i * β i) := by
        rw [finSum_snoc m (fun i => α i * β (p'.toFun i)), finSum_snoc m (fun i => α i * β i), hp'_fix]
        have hmatch : (fun i : Fin m => α (castSuccFin i) * β (p'.toFun (castSuccFin i))) =
                      (fun i : Fin m => α' i * β' (q.toFun i)) := by
          funext i; dsimp [α', β', q, restrictPermLast, castSuccFin]
        rw [hmatch]
        exact add_le_add_right_r (rearrangement_upper_all_n m α' β' hα' hβ' q) _
      exact le_trans_r hstep htail

/-- All-n Two-Sided Rearrangement Inequality: `∑ α_i β_{n-1-i} ≤ ∑ α_i β_{p(i)} ≤ ∑ α_i β_i`. -/
theorem rearrangement_bounds_all_n (n : Nat) (α β : Fin n → R)
    (hα : NonIncreasing α) (hβ : NonIncreasing β) (p : Perm n) :
    finSum n (fun i => α i * β ((revPerm n).toFun i)) ≤ finSum n (fun i => α i * β (p.toFun i)) ∧
    finSum n (fun i => α i * β (p.toFun i)) ≤ finSum n (fun i => α i * β i) := by
  refine ⟨?_, rearrangement_upper_all_n n α β hα hβ p⟩
  let β_neg_rev : Fin n → R := fun i => -(β ((revPerm n).toFun i))
  have hβ_nr : NonIncreasing β_neg_rev := by
    intro i j hij
    dsimp [β_neg_rev, revPerm]
    have hrev : n - 1 - j.1 ≤ n - 1 - i.1 := by omega
    have hle := hβ ⟨n - 1 - j.1, by omega⟩ ⟨n - 1 - i.1, by omega⟩ hrev
    rw [← sub_nonneg_iff_r, sub_eq_add_neg_r, neg_neg_r, add_comm_r, ← sub_eq_add_neg_r, sub_nonneg_iff_r]
    exact hle
  let q := compPerm (revPerm n) p
  have hup := rearrangement_upper_all_n n α β_neg_rev hα hβ_nr q
  have hq : finSum n (fun i => α i * β_neg_rev (q.toFun i)) =
            -finSum n (fun i => α i * β (p.toFun i)) := by
    rw [← finSum_neg]
    apply finSum_congr; intro i
    dsimp [β_neg_rev, q, compPerm]
    rw [revPerm_invol n (p.toFun i), mul_neg_r]
  have hr : finSum n (fun i => α i * β_neg_rev i) =
            -finSum n (fun i => α i * β ((revPerm n).toFun i)) := by
    rw [← finSum_neg]
    apply finSum_congr; intro i
    dsimp [β_neg_rev]; rw [mul_neg_r]
  rw [hq, hr] at hup
  rw [← sub_nonneg_iff_r]
  have hup' := sub_nonneg_iff_r.mpr hup
  rwa [sub_eq_add_neg_r, neg_neg_r, add_comm_r, ← sub_eq_add_neg_r] at hup'

/-- All-n Fiedler (1971) Lower Permutation Product Bound: `∏ (α_i + β_i) ≤ ∏ (α_i + β_{p(i)})`. -/
theorem fiedler_prod_lower_all_n :
    ∀ (n : Nat) (α β : Fin n → R),
      NonIncreasing α → NonIncreasing β →
      (∀ i, 0 ≤ α i) → (∀ i, 0 ≤ β i) → ∀ (p : Perm n),
      finProd n (fun i => α i + β i) ≤ finProd n (fun i => α i + β (p.toFun i))
  | 0, _, _, _, _, _, _, _ => le_refl_r 1
  | m + 1, α, β, hα, hβ, hα0, hβ0, p => by
    let α' : Fin m → R := fun i => α (castSuccFin i)
    let β' : Fin m → R := fun i => β (castSuccFin i)
    have hα' : NonIncreasing α' := fun i j hij => hα (castSuccFin i) (castSuccFin j) hij
    have hβ' : NonIncreasing β' := fun i j hij => hβ (castSuccFin i) (castSuccFin j) hij
    have hα0' : ∀ i, 0 ≤ α' i := fun i => hα0 (castSuccFin i)
    have hβ0' : ∀ i, 0 ≤ β' i := fun i => hβ0 (castSuccFin i)
    by_cases hfix : p.toFun (lastFin m) = lastFin m
    · let q := restrictPermLast p hfix
      rw [finProd_snoc m (fun i => α i + β i), finProd_snoc m (fun i => α i + β (p.toFun i)), hfix]
      have hmatch : (fun i : Fin m => α (castSuccFin i) + β (p.toFun (castSuccFin i))) =
                    (fun i : Fin m => α' i + β' (q.toFun i)) := by
        funext i; dsimp [α', β', q, restrictPermLast, castSuccFin]
      rw [hmatch]
      have hfac : 0 ≤ α (lastFin m) + β (lastFin m) := by
        have h := add_le_add_r (hα0 (lastFin m)) (hβ0 (lastFin m)); rwa [zero_add_r] at h
      exact mul_le_mul_of_nonneg_right_r (fiedler_prod_lower_all_n m α' β' hα' hβ' hα0' hβ0' q) hfac
    · let r0 := p.invFun (lastFin m)
      have hr0_ne : r0 ≠ lastFin m :=
        fun heq => hfix ((congrArg p.toFun heq).symm.trans (p.right_inv (lastFin m)))
      have hr0_lt : r0.1 < m := by
        have h1 := r0.2; have h2 : r0.1 ≠ m := fun e => hr0_ne (Fin.ext e); omega
      let r : Fin m := ⟨r0.1, hr0_lt⟩
      have hr_cast : castSuccFin r = r0 := Fin.ext rfl
      let s0 := p.toFun (lastFin m)
      have hs0_lt : s0.1 < m := by
        have h1 := s0.2; have h2 : s0.1 ≠ m := fun e => hfix (Fin.ext e); omega
      let p' := compPerm p (swapPerm r0 (lastFin m))
      have hp'_fix : p'.toFun (lastFin m) = lastFin m := by
        dsimp [p', compPerm, swapPerm]
        have hne : lastFin m ≠ r0 := fun e => hr0_ne e.symm
        simp [hne, r0, p.right_inv]
      have hp'_r : p'.toFun r0 = s0 := by dsimp [p', compPerm, swapPerm]; simp [s0]
      let q := restrictPermLast p' hp'_fix
      have htail : finProd (m + 1) (fun i => α i + β i) ≤
                   finProd (m + 1) (fun i => α i + β (p'.toFun i)) := by
        rw [finProd_snoc m (fun i => α i + β i), finProd_snoc m (fun i => α i + β (p'.toFun i)), hp'_fix]
        have hmatch : (fun i : Fin m => α (castSuccFin i) + β (p'.toFun (castSuccFin i))) =
                      (fun i : Fin m => α' i + β' (q.toFun i)) := by
          funext i; dsimp [α', β', q, restrictPermLast, castSuccFin]
        rw [hmatch]
        have hfac : 0 ≤ α (lastFin m) + β (lastFin m) := by
          have h := add_le_add_r (hα0 (lastFin m)) (hβ0 (lastFin m)); rwa [zero_add_r] at h
        exact mul_le_mul_of_nonneg_right_r (fiedler_prod_lower_all_n m α' β' hα' hβ' hα0' hβ0' q) hfac
      have hstep : finProd (m + 1) (fun i => α i + β (p'.toFun i)) ≤
                   finProd (m + 1) (fun i => α i + β (p.toFun i)) := by
        rw [finProd_snoc m (fun i => α i + β (p'.toFun i)),
            finProd_snoc m (fun i => α i + β (p.toFun i)),
            finProd_extract r (fun i => α (castSuccFin i) + β (p'.toFun (castSuccFin i))),
            finProd_extract r (fun i => α (castSuccFin i) + β (p.toFun (castSuccFin i)))]
        have hrest : finProd m (fun i => if i = r then 1 else α (castSuccFin i) + β (p'.toFun (castSuccFin i))) =
                     finProd m (fun i => if i = r then 1 else α (castSuccFin i) + β (p.toFun (castSuccFin i))) := by
          apply finProd_congr; intro i
          by_cases hir : i = r
          · subst hir; simp
          · have hne1 : castSuccFin i ≠ r0 :=
              fun e => hir (castSuccFin_inj (e.trans hr_cast.symm))
            have hne2 : castSuccFin i ≠ lastFin m := by
              intro e; have : i.1 = m := Fin.ext_iff.mp e; omega
            dsimp [p', compPerm, swapPerm]; simp [hir, hne1, hne2]
        rw [hrest, hr_cast, show p.toFun r0 = lastFin m from p.right_inv (lastFin m), hp'_r, hp'_fix]
        let rest := finProd m (fun i => if i = r then 1 else α (castSuccFin i) + β (p.toFun (castSuccFin i)))
        have hrest_nn : 0 ≤ rest := by
          apply finProd_nonneg; intro i
          by_cases hir : i = r
          · subst hir; simp; exact le_of_lt_r LinearOrderedCommRing.zero_lt_one
          · simp [hir]
            have h := add_le_add_r (hα0 (castSuccFin i)) (hβ0 (p.toFun (castSuccFin i)))
            rwa [zero_add_r] at h
        have hswap := fiedler_swap_le
          (hα r0 (lastFin m) (Nat.le_of_lt hr0_lt))
          (hβ s0 (lastFin m) (Nat.le_of_lt hs0_lt))
        calc ((α r0 + β s0) * rest) * (α (lastFin m) + β (lastFin m))
            = ((α r0 + β s0) * (α (lastFin m) + β (lastFin m))) * rest := by
                rw [mul_assoc_r, mul_comm_r rest, ← mul_assoc_r]
          _ ≤ ((α r0 + β (lastFin m)) * (α (lastFin m) + β s0)) * rest :=
                mul_le_mul_of_nonneg_right_r hswap hrest_nn
          _ = ((α r0 + β (lastFin m)) * rest) * (α (lastFin m) + β s0) := by
                rw [mul_assoc_r, mul_comm_r _ rest, ← mul_assoc_r]
      exact le_trans_r htail hstep

/-- All-n Fiedler (1971) Upper Permutation Product Bound via `revPerm` auxiliary induction. -/
theorem fiedler_prod_upper_aux :
    ∀ (n : Nat) (α β : Fin n → R),
      NonIncreasing α → NonIncreasing β →
      (∀ i, 0 ≤ α i) → (∀ i, 0 ≤ β i) → ∀ (q : Perm n),
      finProd n (fun i => α i + β ((revPerm n).toFun (q.toFun i))) ≤
      finProd n (fun i => α i + β ((revPerm n).toFun i))
  | 0, _, _, _, _, _, _, _ => le_refl_r 1
  | m + 1, α, β, hα, hβ, hα0, hβ0, q => by
    let α' : Fin m → R := fun i => α (castSuccFin i)
    let β_tail : Fin m → R := fun i => β ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
    have hα' : NonIncreasing α' := fun i j hij => hα (castSuccFin i) (castSuccFin j) hij
    have hβ' : NonIncreasing β_tail := fun i j hij =>
      hβ ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ (Nat.add_le_add_right hij 1)
    have hα0' : ∀ i, 0 ≤ α' i := fun i => hα0 (castSuccFin i)
    have hβ0' : ∀ i, 0 ≤ β_tail i := fun i => hβ0 ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
    have hrev_shift : ∀ j : Fin m,
        β ((revPerm (m + 1)).toFun (castSuccFin j)) = β_tail ((revPerm m).toFun j) := by
      intro j; dsimp [β_tail, revPerm, castSuccFin]
      apply congrArg β; apply Fin.ext; dsimp; omega
    by_cases hfix : q.toFun (lastFin m) = lastFin m
    · let q_sub := restrictPermLast q hfix
      rw [finProd_snoc m (fun i => α i + β ((revPerm (m + 1)).toFun (q.toFun i))),
          finProd_snoc m (fun i => α i + β ((revPerm (m + 1)).toFun i)), hfix]
      have hmatch1 : (fun i : Fin m => α (castSuccFin i) + β ((revPerm (m + 1)).toFun (q.toFun (castSuccFin i)))) =
                     (fun i : Fin m => α' i + β_tail ((revPerm m).toFun (q_sub.toFun i))) := by
        funext i
        have hqc : q.toFun (castSuccFin i) = castSuccFin (q_sub.toFun i) := Fin.ext rfl
        rw [hqc, hrev_shift]
      have hmatch2 : (fun i : Fin m => α (castSuccFin i) + β ((revPerm (m + 1)).toFun (castSuccFin i))) =
                     (fun i : Fin m => α' i + β_tail ((revPerm m).toFun i)) := by
        funext i; rw [hrev_shift]
      rw [hmatch1, hmatch2]
      have hfac : 0 ≤ α (lastFin m) + β ((revPerm (m + 1)).toFun (lastFin m)) := by
        have h := add_le_add_r (hα0 (lastFin m)) (hβ0 ((revPerm (m + 1)).toFun (lastFin m)))
        rwa [zero_add_r] at h
      exact mul_le_mul_of_nonneg_right_r (fiedler_prod_upper_aux m α' β_tail hα' hβ' hα0' hβ0' q_sub) hfac
    · let r0 := q.invFun (lastFin m)
      have hr0_ne : r0 ≠ lastFin m :=
        fun heq => hfix ((congrArg q.toFun heq).symm.trans (q.right_inv (lastFin m)))
      have hr0_lt : r0.1 < m := by
        have h1 := r0.2; have h2 : r0.1 ≠ m := fun e => hr0_ne (Fin.ext e); omega
      let r : Fin m := ⟨r0.1, hr0_lt⟩
      have hr_cast : castSuccFin r = r0 := Fin.ext rfl
      let s0 := q.toFun (lastFin m)
      have hs0_lt : s0.1 < m := by
        have h1 := s0.2; have h2 : s0.1 ≠ m := fun e => hfix (Fin.ext e); omega
      let q' := compPerm q (swapPerm r0 (lastFin m))
      have hq'_fix : q'.toFun (lastFin m) = lastFin m := by
        dsimp [q', compPerm, swapPerm]
        have hne : lastFin m ≠ r0 := fun e => hr0_ne e.symm
        simp [hne, r0, q.right_inv]
      have hq'_r : q'.toFun r0 = s0 := by dsimp [q', compPerm, swapPerm]; simp [s0]
      have hstep : finProd (m + 1) (fun i => α i + β ((revPerm (m + 1)).toFun (q.toFun i))) ≤
                   finProd (m + 1) (fun i => α i + β ((revPerm (m + 1)).toFun (q'.toFun i))) := by
        rw [finProd_snoc m (fun i => α i + β ((revPerm (m + 1)).toFun (q.toFun i))),
            finProd_snoc m (fun i => α i + β ((revPerm (m + 1)).toFun (q'.toFun i))),
            finProd_extract r (fun i => α (castSuccFin i) + β ((revPerm (m + 1)).toFun (q.toFun (castSuccFin i)))),
            finProd_extract r (fun i => α (castSuccFin i) + β ((revPerm (m + 1)).toFun (q'.toFun (castSuccFin i))))]
        have hrest : finProd m (fun i => if i = r then 1 else α (castSuccFin i) + β ((revPerm (m + 1)).toFun (q.toFun (castSuccFin i)))) =
                     finProd m (fun i => if i = r then 1 else α (castSuccFin i) + β ((revPerm (m + 1)).toFun (q'.toFun (castSuccFin i)))) := by
          apply finProd_congr; intro i
          by_cases hir : i = r
          · subst hir; simp
          · have hne1 : castSuccFin i ≠ r0 :=
              fun e => hir (castSuccFin_inj (e.trans hr_cast.symm))
            have hne2 : castSuccFin i ≠ lastFin m := by
              intro e; have : i.1 = m := Fin.ext_iff.mp e; omega
            dsimp [q', compPerm, swapPerm]; simp [hir, hne1, hne2]
        rw [hrest, hr_cast, show q.toFun r0 = lastFin m from q.right_inv (lastFin m), hq'_r, hq'_fix]
        let rest := finProd m (fun i => if i = r then 1 else α (castSuccFin i) + β ((revPerm (m + 1)).toFun (q'.toFun (castSuccFin i))))
        have hrest_nn : 0 ≤ rest := by
          apply finProd_nonneg; intro i
          by_cases hir : i = r
          · subst hir; simp; exact le_of_lt_r LinearOrderedCommRing.zero_lt_one
          · simp [hir]
            have h := add_le_add_r (hα0 (castSuccFin i)) (hβ0 ((revPerm (m + 1)).toFun (q'.toFun (castSuccFin i))))
            rwa [zero_add_r] at h
        have hb_ord : β ((revPerm (m + 1)).toFun s0) ≤ β ((revPerm (m + 1)).toFun (lastFin m)) := by
          apply hβ; dsimp [revPerm, lastFin]; omega
        have hswap := fiedler_swap_le (hα r0 (lastFin m) (Nat.le_of_lt hr0_lt)) hb_ord
        calc ((α r0 + β ((revPerm (m + 1)).toFun (lastFin m))) * rest) * (α (lastFin m) + β ((revPerm (m + 1)).toFun s0))
            = ((α r0 + β ((revPerm (m + 1)).toFun (lastFin m))) * (α (lastFin m) + β ((revPerm (m + 1)).toFun s0))) * rest := by
                rw [mul_assoc_r, mul_comm_r rest, ← mul_assoc_r]
          _ ≤ ((α r0 + β ((revPerm (m + 1)).toFun s0)) * (α (lastFin m) + β ((revPerm (m + 1)).toFun (lastFin m)))) * rest :=
                mul_le_mul_of_nonneg_right_r hswap hrest_nn
          _ = ((α r0 + β ((revPerm (m + 1)).toFun s0)) * rest) * (α (lastFin m) + β ((revPerm (m + 1)).toFun (lastFin m))) := by
                rw [mul_assoc_r, mul_comm_r _ rest, ← mul_assoc_r]
      let q_sub := restrictPermLast q' hq'_fix
      have htail : finProd (m + 1) (fun i => α i + β ((revPerm (m + 1)).toFun (q'.toFun i))) ≤
                   finProd (m + 1) (fun i => α i + β ((revPerm (m + 1)).toFun i)) := by
        rw [finProd_snoc m (fun i => α i + β ((revPerm (m + 1)).toFun (q'.toFun i))),
            finProd_snoc m (fun i => α i + β ((revPerm (m + 1)).toFun i)), hq'_fix]
        have hmatch1 : (fun i : Fin m => α (castSuccFin i) + β ((revPerm (m + 1)).toFun (q'.toFun (castSuccFin i)))) =
                       (fun i : Fin m => α' i + β_tail ((revPerm m).toFun (q_sub.toFun i))) := by
          funext i
          have hqc : q'.toFun (castSuccFin i) = castSuccFin (q_sub.toFun i) := Fin.ext rfl
          rw [hqc, hrev_shift]
        have hmatch2 : (fun i : Fin m => α (castSuccFin i) + β ((revPerm (m + 1)).toFun (castSuccFin i))) =
                       (fun i : Fin m => α' i + β_tail ((revPerm m).toFun i)) := by
          funext i; rw [hrev_shift]
        rw [hmatch1, hmatch2]
        have hfac : 0 ≤ α (lastFin m) + β ((revPerm (m + 1)).toFun (lastFin m)) := by
          have h := add_le_add_r (hα0 (lastFin m)) (hβ0 ((revPerm (m + 1)).toFun (lastFin m)))
          rwa [zero_add_r] at h
        exact mul_le_mul_of_nonneg_right_r (fiedler_prod_upper_aux m α' β_tail hα' hβ' hα0' hβ0' q_sub) hfac
      exact le_trans_r hstep htail

/-- Fiedler's (1971) Two-Sided Permutation Product Theorem for all `n ∈ Nat`:
    `∏ (α_i + β_i) ≤ ∏ (α_i + β_{p(i)}) ≤ ∏ (α_i + β_{n-1-i})`. -/
theorem fiedler_perm_prod_bounds_all_n (n : Nat) (α β : Fin n → R)
    (hα : NonIncreasing α) (hβ : NonIncreasing β)
    (hα0 : ∀ i, 0 ≤ α i) (hβ0 : ∀ i, 0 ≤ β i) (p : Perm n) :
    finProd n (fun i => α i + β i) ≤ finProd n (fun i => α i + β (p.toFun i)) ∧
    finProd n (fun i => α i + β (p.toFun i)) ≤ finProd n (fun i => α i + β ((revPerm n).toFun i)) := by
  refine ⟨fiedler_prod_lower_all_n n α β hα hβ hα0 hβ0 p, ?_⟩
  let q := compPerm (revPerm n) p
  have haux := fiedler_prod_upper_aux n α β hα hβ hα0 hβ0 q
  have hmatch : finProd n (fun i => α i + β ((revPerm n).toFun (q.toFun i))) =
                finProd n (fun i => α i + β (p.toFun i)) := by
    apply finProd_congr; intro i
    dsimp [q, compPerm]; rw [revPerm_invol n (p.toFun i)]
  rwa [hmatch] at haux

theorem fiedler_upper_aux_eq_iff :
    ∀ (n : Nat) (α β : Fin n → R),
      StrictlyDecreasing α → StrictlyDecreasing β →
      (∀ i, 0 < α i) → (∀ i, 0 < β i) → ∀ (q : Perm n),
      finProd n (fun i => α i + β ((revPerm n).toFun (q.toFun i))) =
      finProd n (fun i => α i + β ((revPerm n).toFun i)) ↔
      (∀ i, q.toFun i = i)
  | 0, _, _, _, _, _, _, _ => ⟨fun _ i => Fin.elim0 i, fun _ => rfl⟩
  | m + 1, α, β, hα, hβ, hαp, hβp, q => by
    let α' : Fin m → R := fun i => α (castSuccFin i)
    let β_tail : Fin m → R := fun i => β ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
    have hα' : StrictlyDecreasing α' := fun i j hij => hα (castSuccFin i) (castSuccFin j) hij
    have hβ' : StrictlyDecreasing β_tail := fun i j hij =>
      hβ ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ (Nat.add_lt_add_right hij 1)
    have hαp' : ∀ i, 0 < α' i := fun i => hαp (castSuccFin i)
    have hβp' : ∀ i, 0 < β_tail i := fun i => hβp ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
    have hα0 : ∀ i, 0 ≤ α i := fun i => le_of_lt_r (hαp i)
    have hβ0 : ∀ i, 0 ≤ β i := fun i => le_of_lt_r (hβp i)
    have hα0' : ∀ i, 0 ≤ α' i := fun i => le_of_lt_r (hαp' i)
    have hβ0' : ∀ i, 0 ≤ β_tail i := fun i => le_of_lt_r (hβp' i)
    have hrev_shift : ∀ j : Fin m,
        β ((revPerm (m + 1)).toFun (castSuccFin j)) = β_tail ((revPerm m).toFun j) := by
      intro j; dsimp [β_tail, revPerm, castSuccFin]
      apply congrArg β; apply Fin.ext; dsimp; omega
    constructor
    · intro heq
      by_cases hfix : q.toFun (lastFin m) = lastFin m
      · let q_sub := restrictPermLast q hfix
        rw [finProd_snoc m (fun i => α i + β ((revPerm (m + 1)).toFun (q.toFun i))),
            finProd_snoc m (fun i => α i + β ((revPerm (m + 1)).toFun i)), hfix] at heq
        have hmatch1 : (fun i : Fin m => α (castSuccFin i) + β ((revPerm (m + 1)).toFun (q.toFun (castSuccFin i)))) =
                       (fun i : Fin m => α' i + β_tail ((revPerm m).toFun (q_sub.toFun i))) := by
          funext i
          have hqc : q.toFun (castSuccFin i) = castSuccFin (q_sub.toFun i) := Fin.ext rfl
          rw [hqc, hrev_shift]
        have hmatch2 : (fun i : Fin m => α (castSuccFin i) + β ((revPerm (m + 1)).toFun (castSuccFin i))) =
                       (fun i : Fin m => α' i + β_tail ((revPerm m).toFun i)) := by
          funext i; rw [hrev_shift]
        rw [hmatch1, hmatch2] at heq
        have hfac_pos : 0 < α (lastFin m) + β ((revPerm (m + 1)).toFun (lastFin m)) := by
          have h := add_lt_add_of_lt_of_le_r (hαp (lastFin m)) (hβ0 ((revPerm (m + 1)).toFun (lastFin m)))
          rwa [zero_add_r] at h
        have hsub_eq : finProd m (fun i => α' i + β_tail ((revPerm m).toFun (q_sub.toFun i))) =
                       finProd m (fun i => α' i + β_tail ((revPerm m).toFun i)) := by
          have hdiff : (finProd m (fun i => α' i + β_tail ((revPerm m).toFun i)) -
                        finProd m (fun i => α' i + β_tail ((revPerm m).toFun (q_sub.toFun i)))) *
                       (α (lastFin m) + β ((revPerm (m + 1)).toFun (lastFin m))) = 0 := by
            rw [sub_mul_r, heq, sub_self_r]
          by_cases hs : finProd m (fun i => α' i + β_tail ((revPerm m).toFun (q_sub.toFun i))) =
                        finProd m (fun i => α' i + β_tail ((revPerm m).toFun i))
          · exact hs
          · have hle := fiedler_prod_upper_aux m α' β_tail
              (nonIncreasing_of_strictlyDecreasing hα') (nonIncreasing_of_strictlyDecreasing hβ') hα0' hβ0' q_sub
            have hlt : finProd m (fun i => α' i + β_tail ((revPerm m).toFun (q_sub.toFun i))) <
                       finProd m (fun i => α' i + β_tail ((revPerm m).toFun i)) :=
              (lt_iff_le_not_le_r _ _).mpr ⟨hle, fun hge => hs (le_antisymm_r hle hge)⟩
            have hp := LinearOrderedCommRing.mul_pos _ _ (sub_pos_iff_r.mpr hlt) hfac_pos
            exact False.elim ((ne_of_lt_r hp) hdiff.symm)
        have hq_id := (fiedler_upper_aux_eq_iff m α' β_tail hα' hβ' hαp' hβp' q_sub).mp hsub_eq
        intro i
        by_cases hil : i.1 < m
        · have hi_eq : i = castSuccFin ⟨i.1, hil⟩ := Fin.ext rfl
          have hqc : q.toFun (castSuccFin ⟨i.1, hil⟩) = castSuccFin (q_sub.toFun ⟨i.1, hil⟩) := Fin.ext rfl
          rw [hi_eq, hqc, hq_id ⟨i.1, hil⟩]
        · have hi_lt := i.2
          have hi_m : i = lastFin m := by apply Fin.ext; dsimp [lastFin]; omega
          rw [hi_m]; exact hfix
      · let r0 := q.invFun (lastFin m)
        have hr0_ne : r0 ≠ lastFin m :=
          fun e => hfix ((congrArg q.toFun e).symm.trans (q.right_inv (lastFin m)))
        have hr0_lt : r0.1 < m := by
          have h1 := r0.2; have h2 : r0.1 ≠ m := fun e => hr0_ne (Fin.ext e); omega
        let r : Fin m := ⟨r0.1, hr0_lt⟩
        have hr_cast : castSuccFin r = r0 := Fin.ext rfl
        let s0 := q.toFun (lastFin m)
        have hs0_lt : s0.1 < m := by
          have h1 := s0.2; have h2 : s0.1 ≠ m := fun e => hfix (Fin.ext e); omega
        let q' := compPerm q (swapPerm r0 (lastFin m))
        have hq'_fix : q'.toFun (lastFin m) = lastFin m := by
          dsimp [q', compPerm, swapPerm]
          have hne : lastFin m ≠ r0 := fun e => hr0_ne e.symm
          simp [hne, r0, q.right_inv]
        have hq'_r : q'.toFun r0 = s0 := by dsimp [q', compPerm, swapPerm]; simp [s0]
        have hstrict : finProd (m + 1) (fun i => α i + β ((revPerm (m + 1)).toFun (q.toFun i))) <
                       finProd (m + 1) (fun i => α i + β ((revPerm (m + 1)).toFun (q'.toFun i))) := by
          rw [finProd_snoc m (fun i => α i + β ((revPerm (m + 1)).toFun (q.toFun i))),
              finProd_snoc m (fun i => α i + β ((revPerm (m + 1)).toFun (q'.toFun i))),
              finProd_extract r (fun i => α (castSuccFin i) + β ((revPerm (m + 1)).toFun (q.toFun (castSuccFin i)))),
              finProd_extract r (fun i => α (castSuccFin i) + β ((revPerm (m + 1)).toFun (q'.toFun (castSuccFin i))))]
          have hrest : finProd m (fun i => if i = r then 1 else α (castSuccFin i) + β ((revPerm (m + 1)).toFun (q.toFun (castSuccFin i)))) =
                       finProd m (fun i => if i = r then 1 else α (castSuccFin i) + β ((revPerm (m + 1)).toFun (q'.toFun (castSuccFin i)))) := by
            apply finProd_congr; intro i
            by_cases hir : i = r
            · subst hir; simp
            · have hne1 : castSuccFin i ≠ r0 :=
                fun e => hir (castSuccFin_inj (e.trans hr_cast.symm))
              have hne2 : castSuccFin i ≠ lastFin m := by
                intro e; have : i.1 = m := Fin.ext_iff.mp e; omega
              dsimp [q', compPerm, swapPerm]; simp [hir, hne1, hne2]
          rw [hrest, hr_cast, show q.toFun r0 = lastFin m from q.right_inv (lastFin m), hq'_r, hq'_fix]
          let rest := finProd m (fun i => if i = r then 1 else α (castSuccFin i) + β ((revPerm (m + 1)).toFun (q'.toFun (castSuccFin i))))
          have hrest_pos : 0 < rest := by
            apply finProd_pos; intro i
            by_cases hir : i = r
            · subst hir; simp; exact LinearOrderedCommRing.zero_lt_one
            · simp [hir]
              have h := add_lt_add_of_lt_of_le_r (hαp (castSuccFin i)) (hβ0 ((revPerm (m + 1)).toFun (q'.toFun (castSuccFin i))))
              rwa [zero_add_r] at h
          have hb_lt : β ((revPerm (m + 1)).toFun s0) < β ((revPerm (m + 1)).toFun (lastFin m)) := by
            apply hβ; dsimp [revPerm, lastFin]; omega
          have hswap := fiedler_swap_lt (hα r0 (lastFin m) hr0_lt) hb_lt
          calc ((α r0 + β ((revPerm (m + 1)).toFun (lastFin m))) * rest) * (α (lastFin m) + β ((revPerm (m + 1)).toFun s0))
              = ((α r0 + β ((revPerm (m + 1)).toFun (lastFin m))) * (α (lastFin m) + β ((revPerm (m + 1)).toFun s0))) * rest := by
                  rw [mul_assoc_r, mul_comm_r rest, ← mul_assoc_r]
            _ < ((α r0 + β ((revPerm (m + 1)).toFun s0)) * (α (lastFin m) + β ((revPerm (m + 1)).toFun (lastFin m)))) * rest :=
                  mul_lt_mul_of_pos_right_r hswap hrest_pos
            _ = ((α r0 + β ((revPerm (m + 1)).toFun s0)) * rest) * (α (lastFin m) + β ((revPerm (m + 1)).toFun (lastFin m))) := by
                  rw [mul_assoc_r, mul_comm_r _ rest, ← mul_assoc_r]
        have htail := fiedler_prod_upper_aux (m + 1) α β
          (nonIncreasing_of_strictlyDecreasing hα) (nonIncreasing_of_strictlyDecreasing hβ) hα0 hβ0 q'
        exact False.elim ((ne_of_lt_r (lt_of_lt_of_le_r hstrict htail)) heq)
    · intro hq
      apply finProd_congr; intro i; rw [hq i]

/-- Strict Uniqueness of the Order-Reversing Permutation `revPerm n` in Fiedler's Upper Bound:
    When `α, β` are strictly decreasing and strictly positive, Fiedler's upper bound
    is attained if and only if `∀ i, p(i) = n - 1 - i`. -/
theorem fiedler_perm_prod_eq_max_iff_revPerm (n : Nat) (α β : Fin n → R)
    (hα : StrictlyDecreasing α) (hβ : StrictlyDecreasing β)
    (hαp : ∀ i, 0 < α i) (hβp : ∀ i, 0 < β i) (p : Perm n) :
    finProd n (fun i => α i + β (p.toFun i)) =
    finProd n (fun i => α i + β ((revPerm n).toFun i)) ↔
    (∀ i, p.toFun i = (revPerm n).toFun i) := by
  let q := compPerm (revPerm n) p
  have hmatch : finProd n (fun i => α i + β (p.toFun i)) =
                finProd n (fun i => α i + β ((revPerm n).toFun (q.toFun i))) := by
    apply finProd_congr; intro i
    dsimp [q, compPerm]; rw [revPerm_invol n (p.toFun i)]
  rw [hmatch, fiedler_upper_aux_eq_iff n α β hα hβ hαp hβp q]
  constructor
  · intro hq i
    have hi : (revPerm n).toFun (p.toFun i) = i := hq i
    have h1 := congrArg (revPerm n).toFun hi
    rwa [revPerm_invol] at h1
  · intro hp i
    dsimp [q, compPerm]
    rw [hp i, revPerm_invol]

end PermRearrangement

-- ============================================================================
-- §6. Positive Benchmark II: All-n Ky Fan Majorization & 2x2 Lidskii-Fiedler
-- ============================================================================

section KyFanAndLidskiiFiedler
variable {R : Type u} [LinearOrderedCommRing R]

theorem finSum_eq_zero_of_nonneg {n : Nat} {f : Fin n → R}
    (hf : ∀ i, 0 ≤ f i) (hsum : finSum n f = 0) : ∀ i, f i = 0 := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ m ih =>
    simp only [finSum] at hsum
    have htail_nn : 0 ≤ finSum m (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) :=
      finSum_nonneg (fun i => hf ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    have h0 : f ⟨0, Nat.zero_lt_succ m⟩ = 0 := by
      by_cases hz : f ⟨0, Nat.zero_lt_succ m⟩ = 0
      · exact hz
      · have hpos : 0 < f ⟨0, Nat.zero_lt_succ m⟩ :=
          (lt_iff_le_not_le_r _ _).mpr ⟨hf _, fun hle => hz (le_antisymm_r hle (hf _))⟩
        have htot := add_lt_add_of_lt_of_le_r hpos htail_nn
        rw [zero_add_r] at htot
        exact False.elim ((ne_of_lt_r htot) hsum.symm)
    rw [h0, zero_add_r] at hsum
    have hrest := ih (fun i => hf ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) hsum
    intro i
    rcases i with ⟨k, hk⟩
    cases k with
    | zero => exact h0
    | succ k' => exact hrest ⟨k', Nat.lt_of_succ_lt_succ hk⟩

def topKIndicator (R : Type u) [LinearOrderedCommRing R] (n k : Nat) : Fin n → R :=
  fun i => if i.1 < k then 1 else 0

/-- Ky Fan's Extremal Weight Principle for all `n, k ∈ Nat` (`k ≤ n`):
    For non-increasing `α` and weights `0 ≤ w_i ≤ 1` with `∑ w_i = k`,
    `∑ w_i α_i ≤ ∑_{i < k} α_i`. -/
theorem ky_fan_weights_upper (n k : Nat) (hk : k ≤ n) (α w : Fin n → R)
    (hα : NonIncreasing α) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    (hsum : finSum n w = finSum n (topKIndicator R n k)) :
    finSum n (fun i => w i * α i) ≤ finSum n (fun i => topKIndicator R n k i * α i) := by
  by_cases hklt : k < n
  · let piv : R := α ⟨k, hklt⟩
    rw [← sub_nonneg_iff_r, ← finSum_sub]
    have hpt : ∀ i : Fin n,
        (topKIndicator R n k i - w i) * piv ≤ (topKIndicator R n k i) * α i - w i * α i := by
      intro i
      rw [← sub_mul_r]
      dsimp [topKIndicator]
      by_cases hik : i.1 < k
      · simp [hik]
        exact mul_le_mul_of_nonneg_left_r (hα i ⟨k, hklt⟩ (Nat.le_of_lt hik)) (sub_nonneg_iff_r.mpr (hw1 i))
      · simp [hik]
        rw [sub_eq_add_neg_r 0, zero_add_r, neg_mul_r, neg_mul_r]
        have hle : w i * α i ≤ w i * piv :=
          mul_le_mul_of_nonneg_left_r (hα ⟨k, hklt⟩ i (Nat.le_of_not_lt hik)) (hw0 i)
        rw [← sub_nonneg_iff_r, sub_eq_add_neg_r, neg_neg_r, add_comm_r, ← sub_eq_add_neg_r]
        exact sub_nonneg_iff_r.mpr hle
    have hsum_piv : finSum n (fun i => (topKIndicator R n k i - w i) * piv) = 0 := by
      rw [finSum_mul_right, finSum_sub, hsum, sub_self_r, zero_mul_r]
    rw [← hsum_piv]
    exact finSum_le hpt
  · have hkn : k = n := by omega
    subst hkn
    have htop1 : ∀ i : Fin k, topKIndicator R k k i = 1 := by
      intro i; dsimp [topKIndicator]; simp [i.2]
    have hdiff0 : finSum k (fun i => 1 - w i) = 0 := by
      have heq : (fun i : Fin k => (1 : R) - w i) = (fun i : Fin k => topKIndicator R k k i - w i) := by
        funext i; rw [htop1 i]
      rw [heq, finSum_sub, hsum, sub_self_r]
    have hwi1 : ∀ i : Fin k, w i = 1 := by
      intro i
      have hz := finSum_eq_zero_of_nonneg (fun j => sub_nonneg_iff_r.mpr (hw1 j)) hdiff0 i
      exact (sub_eq_zero_iff_r.mp hz).symm
    have hcongr : finSum k (fun i => w i * α i) = finSum k (fun i => topKIndicator R k k i * α i) := by
      apply finSum_congr; intro i; rw [hwi1 i, htop1 i]
    rw [hcongr]; exact le_refl_r _

theorem matMul_assoc {n : Nat} (A B C : RMat R n) :
    matMul (matMul A B) C = matMul A (matMul B C) := by
  funext i l; unfold matMul
  have h1 : finSum n (fun k => finSum n (fun j => A i j * B j k) * C k l) =
            finSum n (fun k => finSum n (fun j => (A i j * B j k) * C k l)) :=
    finSum_congr (fun k => (finSum_mul_right n _ (C k l)).symm)
  have h2 : finSum n (fun j => A i j * finSum n (fun k => B j k * C k l)) =
            finSum n (fun j => finSum n (fun k => A i j * (B j k * C k l))) :=
    finSum_congr (fun j => (finSum_mul_left n (A i j) _).symm)
  rw [h1, h2, finSum_comm]
  apply finSum_congr; intro j; apply finSum_congr; intro k; exact mul_assoc_r _ _ _

theorem matMul_id_left {n : Nat} (A : RMat R n) : matMul (idMat n) A = A := by
  funext i j; unfold matMul idMat
  have h : (fun k : Fin n => (if i = k then (1 : R) else 0) * A k j) =
           (fun k : Fin n => if k = i then A k j else 0) := by
    funext k
    by_cases hik : i = k
    · subst hik; simp [one_mul_r]
    · have hki : k ≠ i := fun e => hik e.symm
      simp [hik, hki, zero_mul_r]
  rw [h, finSum_delta]

theorem matMul_id_right {n : Nat} (A : RMat R n) : matMul A (idMat n) = A := by
  funext i j; unfold matMul idMat
  have h : (fun k : Fin n => A i k * (if k = j then (1 : R) else 0)) =
           (fun k : Fin n => if k = j then A i k else 0) := by
    funext k
    by_cases hkj : k = j
    · subst hkj; simp [mul_one_r]
    · simp [hkj, mul_zero_r]
  rw [h, finSum_delta]

theorem transpose_mul {n : Nat} (A B : RMat R n) :
    transpose (matMul A B) = matMul (transpose B) (transpose A) := by
  funext i j; dsimp [transpose, matMul]
  apply finSum_congr; intro k; exact mul_comm_r _ _

theorem isOrthogonal_mul {n : Nat} {U Q : RMat R n}
    (hU : IsOrthogonal U) (hQ : IsOrthogonal Q) : IsOrthogonal (matMul U Q) := by
  constructor
  · rw [transpose_mul, matMul_assoc, ← matMul_assoc (transpose U) U Q, hU.1, matMul_id_left, hQ.1]
  · rw [transpose_mul, matMul_assoc, ← matMul_assoc Q (transpose Q) (transpose U), hQ.2, matMul_id_left, hU.2]

theorem isOrthogonal_transpose {n : Nat} {U : RMat R n} (hU : IsOrthogonal U) :
    IsOrthogonal (transpose U) := by
  have htt : transpose (transpose U) = U := rfl
  exact ⟨by rw [htt]; exact hU.2, by rw [htt]; exact hU.1⟩

/-- Orthogonal spectral decomposition `A = Q diag(α) Q^T` with non-increasing eigenvalues `α`. -/
def HasOrthoDiag {n : Nat} (A : RMat R n) (α : Fin n → R) (Q : RMat R n) : Prop :=
  IsOrthogonal Q ∧ NonIncreasing α ∧ A = matMul Q (matMul (diagMat α) (transpose Q))

def colVec {n : Nat} (U : RMat R n) (r : Fin n) : Fin n → R := fun i => U i r

theorem quadForm_orthoDiag {n : Nat} {A Q : RMat R n} {α : Fin n → R}
    (hA : A = matMul Q (matMul (diagMat α) (transpose Q))) (x : Fin n → R) :
    quadForm A x = finSum n (fun j => (matVec (transpose Q) x j * matVec (transpose Q) x j) * α j) := by
  rw [hA]
  unfold quadForm dotProd matVec matMul diagMat transpose
  have step1 : finSum n (fun i => x i * finSum n (fun l => finSum n (fun j =>
      Q i j * (finSum n (fun k => (if j = k then α j else 0) * Q l k))) * x l)) =
      finSum n (fun i => x i * finSum n (fun l => finSum n (fun j =>
      Q i j * (α j * Q l j)) * x l)) := by
    apply finSum_congr; intro i
    apply congrArg (fun t => x i * t)
    apply finSum_congr; intro l
    apply congrArg (fun t => t * x l)
    apply finSum_congr; intro j
    apply congrArg (fun t => Q i j * t)
    have hd : (fun k : Fin n => (if j = k then α j else 0) * Q l k) =
              (fun k : Fin n => if k = j then α j * Q l k else 0) := by
      funext k
      by_cases hjk : j = k
      · subst hjk; simp
      · have hkj : k ≠ j := fun e => hjk e.symm
        simp [hjk, hkj, zero_mul_r]
    rw [hd, finSum_delta]
  rw [step1]
  have step2 : finSum n (fun i => x i * finSum n (fun l => finSum n (fun j => Q i j * (α j * Q l j)) * x l)) =
               finSum n (fun i => finSum n (fun l => finSum n (fun j => (x i * Q i j) * (Q l j * x l) * α j))) := by
    apply finSum_congr; intro i
    rw [← finSum_mul_left]
    apply finSum_congr; intro l
    rw [← finSum_mul_right, ← finSum_mul_left]
    apply finSum_congr; intro j
    calc x i * ((Q i j * (α j * Q l j)) * x l)
        = (x i * (Q i j * (α j * Q l j))) * x l := (mul_assoc_r _ _ _).symm
      _ = ((x i * Q i j) * (α j * Q l j)) * x l := by rw [← mul_assoc_r (x i) (Q i j)]
      _ = (x i * Q i j) * ((α j * Q l j) * x l) := mul_assoc_r _ _ _
      _ = (x i * Q i j) * (α j * (Q l j * x l)) := by rw [mul_assoc_r (α j)]
      _ = (x i * Q i j) * ((Q l j * x l) * α j) := by rw [mul_comm_r (α j)]
      _ = (x i * Q i j) * (Q l j * x l) * α j := (mul_assoc_r _ _ _).symm
  rw [step2]
  have swap_lj : finSum n (fun i => finSum n (fun l => finSum n (fun j => (x i * Q i j) * (Q l j * x l) * α j))) =
                 finSum n (fun i => finSum n (fun j => finSum n (fun l => (x i * Q i j) * (Q l j * x l) * α j))) :=
    finSum_congr (fun _ => finSum_comm n n _)
  rw [swap_lj, finSum_comm]
  apply finSum_congr; intro j
  have factor_j : finSum n (fun i => finSum n (fun l => (x i * Q i j) * (Q l j * x l) * α j)) =
                  (finSum n (fun i => Q i j * x i) * finSum n (fun l => Q l j * x l)) * α j := by
    calc finSum n (fun i => finSum n (fun l => (x i * Q i j) * (Q l j * x l) * α j))
        = finSum n (fun i => finSum n (fun l => (Q i j * x i) * ((Q l j * x l) * α j))) := by
            apply finSum_congr; intro i; apply finSum_congr; intro l
            rw [mul_comm_r (x i) (Q i j), mul_assoc_r]
      _ = finSum n (fun i => (Q i j * x i) * finSum n (fun l => (Q l j * x l) * α j)) :=
            finSum_congr (fun i => finSum_mul_left n _ _)
      _ = finSum n (fun i => Q i j * x i) * finSum n (fun l => (Q l j * x l) * α j) :=
            finSum_mul_right n _ _
      _ = (finSum n (fun i => Q i j * x i) * finSum n (fun l => Q l j * x l)) * α j := by
            rw [finSum_mul_right, mul_assoc_r]
  exact factor_j

theorem quadForm_self_col {n : Nat} {A U : RMat R n} {γ : Fin n → R}
    (hU : IsOrthogonal U) (hA : A = matMul U (matMul (diagMat γ) (transpose U))) (r : Fin n) :
    quadForm A (colVec U r) = γ r := by
  rw [quadForm_orthoDiag hA]
  have hcol : ∀ j : Fin n, matVec (transpose U) (colVec U r) j = idMat n j r := by
    intro j
    have e := congrFun (congrFun hU.1 j) r
    exact e
  have hfn : (fun j : Fin n => (matVec (transpose U) (colVec U r) j * matVec (transpose U) (colVec U r) j) * γ j) =
             (fun j : Fin n => if j = r then γ j else 0) := by
    funext j; rw [hcol j]; dsimp [idMat]
    by_cases hjr : j = r
    · subst hjr; simp [one_mul_r]
    · simp [hjr, zero_mul_r]
  rw [hfn, finSum_delta]

theorem ky_fan_frame_trace_bound {n : Nat} (k : Nat) (hk : k ≤ n)
    {A Q U : RMat R n} {α : Fin n → R}
    (hA : HasOrthoDiag A α Q) (hU : IsOrthogonal U) :
    finSum n (fun r => topKIndicator R n k r * quadForm A (colVec U r)) ≤
    finSum n (fun i => topKIndicator R n k i * α i) := by
  rcases hA with ⟨hQ, hα, hAeq⟩
  let W := matMul (transpose U) Q
  have hW : IsOrthogonal W := isOrthogonal_mul (isOrthogonal_transpose hU) hQ
  have hentry : ∀ r j : Fin n, matVec (transpose Q) (colVec U r) j = W r j := by
    intro r j; dsimp [matVec, colVec, W, matMul, transpose]
    apply finSum_congr; intro i; exact mul_comm_r _ _
  let w : Fin n → R := fun j => finSum n (fun r => topKIndicator R n k r * (W r j * W r j))
  have hlhs : finSum n (fun r => topKIndicator R n k r * quadForm A (colVec U r)) =
              finSum n (fun j => w j * α j) := by
    calc finSum n (fun r => topKIndicator R n k r * quadForm A (colVec U r))
        = finSum n (fun r => topKIndicator R n k r * finSum n (fun j => (W r j * W r j) * α j)) := by
            apply finSum_congr; intro r
            rw [quadForm_orthoDiag hAeq]
            apply congrArg (fun t => topKIndicator R n k r * t)
            apply finSum_congr; intro j; rw [hentry r j]
      _ = finSum n (fun r => finSum n (fun j => (topKIndicator R n k r * (W r j * W r j)) * α j)) := by
            apply finSum_congr; intro r
            rw [← finSum_mul_left]
            apply finSum_congr; intro j
            exact (mul_assoc_r (topKIndicator R n k r) (W r j * W r j) (α j)).symm
      _ = finSum n (fun j => finSum n (fun r => (topKIndicator R n k r * (W r j * W r j)) * α j)) :=
            finSum_comm n n _
      _ = finSum n (fun j => w j * α j) :=
            finSum_congr (fun j => finSum_mul_right n _ (α j))
  have hw0 : ∀ j, 0 ≤ w j := by
    intro j; apply finSum_nonneg; intro r
    have ht0 : 0 ≤ topKIndicator R n k r := by
      dsimp [topKIndicator]
      by_cases hr : r.1 < k
      · simp [hr]; exact le_of_lt_r LinearOrderedCommRing.zero_lt_one
      · simp [hr]; exact le_refl_r 0
    exact LinearOrderedCommRing.mul_nonneg _ _ ht0 (sq_nonneg_r (W r j))
  have hw1 : ∀ j, w j ≤ 1 := by
    intro j
    have hcol1 : finSum n (fun r => W r j * W r j) = 1 := by
      have e := congrFun (congrFun hW.1 j) j
      dsimp [matMul, transpose, idMat] at e; simp at e; exact e
    rw [← hcol1]
    apply finSum_le; intro r
    dsimp [topKIndicator]
    by_cases hr : r.1 < k
    · simp [hr, one_mul_r]; exact le_refl_r _
    · simp [hr, zero_mul_r]; exact sq_nonneg_r (W r j)
  have hwsum : finSum n w = finSum n (topKIndicator R n k) := by
    dsimp [w]
    rw [finSum_comm]
    apply finSum_congr; intro r
    rw [finSum_mul_left]
    have hrow1 : finSum n (fun j => W r j * W r j) = 1 := by
      have e := congrFun (congrFun hW.2 r) r
      dsimp [matMul, transpose, idMat] at e; simp at e; exact e
    rw [hrow1, mul_one_r]
  rw [hlhs]
  exact ky_fan_weights_upper n k hk α w hα hw0 hw1 hwsum

theorem trace_orthoDiag {n : Nat} {A Q : RMat R n} {α : Fin n → R}
    (hA : HasOrthoDiag A α Q) : trace A = finSum n α := by
  rcases hA with ⟨hQ, _, hAeq⟩
  have hsum : finSum n (fun r => topKIndicator R n n r * quadForm A (colVec Q r)) = finSum n α := by
    apply finSum_congr; intro r
    rw [quadForm_self_col hQ hAeq r]
    dsimp [topKIndicator]; simp [r.2, one_mul_r]
  have hstd : finSum n (fun i => topKIndicator R n n i * quadForm A (colVec (idMat n) i)) = trace A := by
    unfold trace
    apply finSum_congr; intro i
    dsimp [topKIndicator]; simp [i.2, one_mul_r]
    unfold quadForm dotProd matVec colVec idMat
    have h1 : (fun r : Fin n => (if r = i then (1 : R) else 0) * finSum n (fun j => A r j * (if j = i then 1 else 0))) =
              (fun r : Fin n => if r = i then A r i else 0) := by
      funext r
      by_cases hri : r = i
      · subst hri; simp [one_mul_r]
        have h2 : (fun j : Fin n => A r j * (if j = r then (1 : R) else 0)) =
                  (fun j : Fin n => if j = r then A r j else 0) := by
          funext j
          by_cases hjr : j = r
          · subst hjr; simp [mul_one_r]
          · simp [hjr, mul_zero_r]
        rw [h2, finSum_delta]
      · simp [hri, zero_mul_r]
    rw [h1, finSum_delta]
  have hid : IsOrthogonal (idMat n : RMat R n) := by
    have ht : transpose (idMat n : RMat R n) = idMat n := by
      funext i j; dsimp [transpose, idMat]
      by_cases h : i = j
      · subst h; simp
      · have hji : j ≠ i := fun e => h e.symm
        simp [h, hji]
    exact ⟨by rw [ht, matMul_id_left], by rw [ht, matMul_id_left]⟩
  rw [← hstd]
  let W := matMul (transpose (idMat n)) Q
  have hW : IsOrthogonal W := isOrthogonal_mul (isOrthogonal_transpose hid) hQ
  calc finSum n (fun r => topKIndicator R n n r * quadForm A (colVec (idMat n) r))
      = finSum n (fun r => finSum n (fun j => (W r j * W r j) * α j)) := by
          apply finSum_congr; intro r
          dsimp [topKIndicator]; simp [r.2, one_mul_r]
          rw [quadForm_orthoDiag hAeq]
          apply finSum_congr; intro j
          have he : matVec (transpose Q) (colVec (idMat n) r) j = W r j := by
            dsimp [matVec, colVec, W, matMul, transpose]
            apply finSum_congr; intro l; exact mul_comm_r _ _
          rw [he]
    _ = finSum n (fun j => finSum n (fun r => (W r j * W r j) * α j)) := finSum_comm n n _
    _ = finSum n (fun j => finSum n (fun r => W r j * W r j) * α j) :=
          finSum_congr (fun j => finSum_mul_right n _ (α j))
    _ = finSum n α := by
          apply finSum_congr; intro j
          have hcol1 : finSum n (fun r => W r j * W r j) = 1 := by
            have e := congrFun (congrFun hW.1 j) j
            dsimp [matMul, transpose, idMat] at e; simp at e; exact e
          rw [hcol1, one_mul_r]

/-- Full `n x n` Ky Fan Additive Majorization Theorem (`λ^↓(A+B) ≺ λ^↓(A) + λ^↓(B)`):
    For all `n, k ∈ Nat` (`k ≤ n`) and orthogonally diagonalizable `A, B, A+B`,
    `∑_{i < k} γ_i ≤ ∑_{i < k} α_i + ∑_{i < k} β_i` and `∑ γ_i = ∑ α_i + ∑ β_i`. -/
theorem ky_fan_additive_majorization_all_n (n k : Nat) (hk : k ≤ n)
    {A B QA QB QAB : RMat R n} {α β γ : Fin n → R}
    (hA : HasOrthoDiag A α QA) (hB : HasOrthoDiag B β QB)
    (hAB : HasOrthoDiag (matAdd A B) γ QAB) :
    finSum n (fun i => topKIndicator R n k i * γ i) ≤
      finSum n (fun i => topKIndicator R n k i * α i) +
      finSum n (fun i => topKIndicator R n k i * β i) ∧
    finSum n γ = finSum n α + finSum n β := by
  constructor
  · rcases hAB with ⟨hU, _, hABeq⟩
    have hlhs : finSum n (fun i => topKIndicator R n k i * γ i) =
                finSum n (fun r => topKIndicator R n k r * quadForm (matAdd A B) (colVec QAB r)) := by
      apply finSum_congr; intro r; rw [quadForm_self_col hU hABeq r]
    have hsplit : finSum n (fun r => topKIndicator R n k r * quadForm (matAdd A B) (colVec QAB r)) =
                  finSum n (fun r => topKIndicator R n k r * quadForm A (colVec QAB r)) +
                  finSum n (fun r => topKIndicator R n k r * quadForm B (colVec QAB r)) := by
      rw [← finSum_add]
      apply finSum_congr; intro r
      rw [← left_distrib_r]
      apply congrArg (fun t => topKIndicator R n k r * t)
      unfold quadForm dotProd matVec matAdd
      rw [← finSum_add]
      apply finSum_congr; intro i
      rw [← left_distrib_r, ← finSum_add]
      apply congrArg (fun t => colVec QAB r i * t)
      apply finSum_congr; intro j; exact right_distrib_r _ _ _
    rw [hlhs, hsplit]
    exact add_le_add_r
      (ky_fan_frame_trace_bound k hk hA hU)
      (ky_fan_frame_trace_bound k hk hB hU)
  · rw [← trace_orthoDiag hAB, ← trace_orthoDiag hA, ← trace_orthoDiag hB, trace_add]

theorem rayleigh_bounds_2x2 {A Q : RMat R 2} {α : Fin 2 → R}
    (hA : HasOrthoDiag A α Q) (u : Fin 2 → R) (hu : dotProd u u = 1) :
    α ⟨1, by decide⟩ ≤ quadForm A u ∧ quadForm A u ≤ α ⟨0, by decide⟩ := by
  rcases hA with ⟨hQ, hα, hAeq⟩
  rw [quadForm_orthoDiag hAeq]
  let y := matVec (transpose Q) u
  have hy_norm : y ⟨0, by decide⟩ * y ⟨0, by decide⟩ + y ⟨1, by decide⟩ * y ⟨1, by decide⟩ = 1 := by
    have hid := quadForm_orthoDiag (α := fun _ => (1 : R)) (A := idMat 2) (Q := Q) (by
      have hd1 : diagMat (fun _ : Fin 2 => (1 : R)) = idMat 2 := rfl
      rw [hd1, matMul_id_left, hQ.2]) u
    have hqf_id : quadForm (idMat 2) u = dotProd u u := by
      unfold quadForm dotProd matVec idMat
      apply finSum_congr; intro i
      apply congrArg (fun t => u i * t)
      have hfn : (fun j : Fin 2 => (if i = j then (1 : R) else 0) * u j) =
                 (fun j : Fin 2 => if j = i then u j else 0) := by
        funext j
        by_cases hij : i = j
        · subst hij; simp [one_mul_r]
        · have hji : j ≠ i := fun e => hij e.symm
          simp [hij, hji, zero_mul_r]
      rw [hfn, finSum_delta]
    rw [hqf_id, hu] at hid
    have hrhs : finSum 2 (fun j => (matVec (transpose Q) u j * matVec (transpose Q) u j) * (1 : R)) =
                y ⟨0, by decide⟩ * y ⟨0, by decide⟩ + y ⟨1, by decide⟩ * y ⟨1, by decide⟩ := by
      simp only [finSum, mul_one_r]; rw [add_zero_r]
    rw [hrhs] at hid
    exact hid.symm
  have hexp_q : finSum 2 (fun j => (y j * y j) * α j) =
                (y ⟨0, by decide⟩ * y ⟨0, by decide⟩) * α ⟨0, by decide⟩ +
                (y ⟨1, by decide⟩ * y ⟨1, by decide⟩) * α ⟨1, by decide⟩ := by
    simp only [finSum]; rw [add_zero_r]
  rw [hexp_q]
  have hord : α ⟨1, by decide⟩ ≤ α ⟨0, by decide⟩ := hα ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
  constructor
  · have h1 := mul_le_mul_of_nonneg_left_r hord (sq_nonneg_r (y ⟨0, by decide⟩))
    have h2 := add_le_add_right_r h1 ((y ⟨1, by decide⟩ * y ⟨1, by decide⟩) * α ⟨1, by decide⟩)
    rwa [← right_distrib_r, hy_norm, one_mul_r] at h2
  · have h1 := mul_le_mul_of_nonneg_left_r hord (sq_nonneg_r (y ⟨1, by decide⟩))
    have h2 := add_le_add_r (le_refl_r ((y ⟨0, by decide⟩ * y ⟨0, by decide⟩) * α ⟨0, by decide⟩)) h1
    rwa [← right_distrib_r, hy_norm, one_mul_r] at h2

theorem prod_majorization_2x2 {x0 x1 y0 y1 : R}
    (hsum : x0 + x1 = y0 + y1) (hy : y1 ≤ y0) (hyx : y0 ≤ x0) :
    x0 * x1 ≤ y0 * y1 := by
  have hx1 : x1 = (y0 + y1) - x0 := by
    apply add_left_cancel_r (a := x0)
    rw [hsum, sub_eq_add_neg_r, add_comm_r x0, add_assoc_r, neg_add_cancel_r, add_zero_r]
  have hid : y0 * y1 - x0 * x1 = (x0 - y0) * (x0 - y1) := by
    rw [hx1]
    calc y0 * y1 - x0 * ((y0 + y1) - x0)
        = y0 * y1 - (x0 * y0 + x0 * y1 - x0 * x0) := by rw [mul_sub_r, left_distrib_r]
      _ = (x0 * x0 - x0 * y0) - (x0 * y1 - y0 * y1) := by
            rw [sub_eq_add_neg_r, sub_eq_add_neg_r (x0 * y0 + x0 * y1), neg_add_r, neg_neg_r, neg_add_r,
                sub_eq_add_neg_r (x0 * x0 - x0 * y0), sub_eq_add_neg_r (x0 * x0), sub_eq_add_neg_r (x0 * y1),
                neg_add_r, neg_neg_r]
            let a := y0 * y1; let b := -(x0 * y0); let c := -(x0 * y1); let d := x0 * x0
            change a + ((b + c) + d) = (d + b) + (c + a)
            calc a + ((b + c) + d)
                = a + (d + (b + c)) := by rw [add_comm_r (b + c) d]
              _ = d + (a + (b + c)) := by rw [← add_assoc_r a d, add_comm_r a d, add_assoc_r]
              _ = d + (b + (a + c)) := by rw [← add_assoc_r a b c, add_comm_r a b, add_assoc_r]
              _ = (d + b) + (c + a) := by rw [← add_assoc_r d b, add_comm_r a c]
      _ = x0 * (x0 - y0) - y1 * (x0 - y0) := by
            rw [← mul_sub_r x0 x0 y0, ← sub_mul_r x0 y0 y1, mul_comm_r (x0 - y0) y1]
      _ = (x0 - y1) * (x0 - y0) := (sub_mul_r _ _ _).symm
      _ = (x0 - y0) * (x0 - y1) := mul_comm_r _ _
  rw [← sub_nonneg_iff_r, hid]
  exact LinearOrderedCommRing.mul_nonneg _ _
    (sub_nonneg_iff_r.mpr hyx)
    (sub_nonneg_iff_r.mpr (le_trans_r hy hyx))

/-- Complete `2 x 2` Non-Commuting Lidskii-Wielandt-Fiedler Theorem:
    Proves two-sided additive majorization `(α^↓ + β^↑)^↓ ≺ γ^↓ ≺ α^↓ + β^↓`
    and Fiedler's determinant inequality `(α_0+β_0)(α_1+β_1) ≤ γ_0 γ_1 ≤ (α_0+β_1)(α_1+β_0)`. -/
theorem lidskii_wielandt_fiedler_2x2
    {A B QA QB QAB : RMat R 2} {α β γ : Fin 2 → R}
    (hA : HasOrthoDiag A α QA) (hB : HasOrthoDiag B β QB)
    (hAB : HasOrthoDiag (matAdd A B) γ QAB) :
    let i0 : Fin 2 := ⟨0, by decide⟩
    let i1 : Fin 2 := ⟨1, by decide⟩
    γ i0 + γ i1 = (α i0 + α i1) + (β i0 + β i1) ∧
    γ i0 ≤ α i0 + β i0 ∧
    α i0 + β i1 ≤ γ i0 ∧
    α i1 + β i0 ≤ γ i0 ∧
    (α i0 + β i0) * (α i1 + β i1) ≤ γ i0 * γ i1 ∧
    γ i0 * γ i1 ≤ (α i0 + β i1) * (α i1 + β i0) := by
  let i0 : Fin 2 := ⟨0, by decide⟩
  let i1 : Fin 2 := ⟨1, by decide⟩
  have hkf1 := (ky_fan_additive_majorization_all_n 2 1 (by decide) hA hB hAB).1
  have hkf2 := (ky_fan_additive_majorization_all_n 2 2 (by decide) hA hB hAB).2
  have htop1 : ∀ v : Fin 2 → R, finSum 2 (fun i => topKIndicator R 2 1 i * v i) = v i0 := by
    intro v; simp only [finSum, topKIndicator]; dsimp
    rw [one_mul_r, zero_mul_r, add_zero_r, add_zero_r]
    exact congrArg v rfl
  rw [htop1 γ, htop1 α, htop1 β] at hkf1
  have hsum2 : ∀ v : Fin 2 → R, finSum 2 v = v i0 + v i1 := by
    intro v; simp only [finSum]; rw [add_zero_r]
  rw [hsum2 γ, hsum2 α, hsum2 β] at hkf2
  have huA : dotProd (colVec QA i0) (colVec QA i0) = 1 := by
    have e := congrFun (congrFun hA.1.1 i0) i0
    dsimp [i0, matMul, transpose, idMat] at e
    exact e
  have huB : dotProd (colVec QB i0) (colVec QB i0) = 1 := by
    have e := congrFun (congrFun hB.1.1 i0) i0
    dsimp [i0, matMul, transpose, idMat] at e
    exact e
  have hquad_add : ∀ u : Fin 2 → R, quadForm (matAdd A B) u = quadForm A u + quadForm B u := by
    intro u; unfold quadForm dotProd matVec matAdd
    rw [← finSum_add]; apply finSum_congr; intro i
    rw [← left_distrib_r, ← finSum_add]; apply congrArg (fun t => u i * t)
    apply finSum_congr; intro j; exact right_distrib_r _ _ _
  have hlow1 : α i0 + β i1 ≤ γ i0 := by
    have hrAB := (rayleigh_bounds_2x2 hAB (colVec QA i0) huA).2
    rw [hquad_add, quadForm_self_col hA.1 hA.2.2 i0] at hrAB
    exact le_trans_r (LinearOrderedCommRing.add_le_add_left _ _
      (rayleigh_bounds_2x2 hB (colVec QA i0) huA).1 (α i0)) hrAB
  have hlow2 : α i1 + β i0 ≤ γ i0 := by
    have hrAB := (rayleigh_bounds_2x2 hAB (colVec QB i0) huB).2
    rw [hquad_add, quadForm_self_col hB.1 hB.2.2 i0] at hrAB
    exact le_trans_r (add_le_add_right_r (rayleigh_bounds_2x2 hA (colVec QB i0) huB).1 (β i0)) hrAB
  have hsum_same : (α i0 + β i0) + (α i1 + β i1) = γ i0 + γ i1 := by
    rw [hkf2]
    calc (α i0 + β i0) + (α i1 + β i1)
        = α i0 + (β i0 + (α i1 + β i1)) := add_assoc_r _ _ _
      _ = α i0 + (α i1 + (β i0 + β i1)) := by
            rw [← add_assoc_r (β i0), add_comm_r (β i0) (α i1), add_assoc_r]
      _ = (α i0 + α i1) + (β i0 + β i1) := (add_assoc_r _ _ _).symm
  have hsum_rev : γ i0 + γ i1 = (α i0 + β i1) + (α i1 + β i0) := by
    rw [hkf2]
    calc (α i0 + α i1) + (β i0 + β i1)
        = α i0 + (α i1 + (β i0 + β i1)) := add_assoc_r _ _ _
      _ = α i0 + (β i1 + (α i1 + β i0)) := by
            rw [add_comm_r (β i0) (β i1), ← add_assoc_r (α i1), add_comm_r (α i1) (β i1), add_assoc_r]
      _ = (α i0 + β i1) + (α i1 + β i0) := (add_assoc_r _ _ _).symm
  have hdet_low : (α i0 + β i0) * (α i1 + β i1) ≤ γ i0 * γ i1 :=
    prod_majorization_2x2 hsum_same (hAB.2.1 i0 i1 (by decide)) hkf1
  have hdet_high : γ i0 * γ i1 ≤ (α i0 + β i1) * (α i1 + β i0) := by
    cases le_total_r (α i1 + β i0) (α i0 + β i1) with
    | inl hle => exact prod_majorization_2x2 hsum_rev hle hlow1
    | inr hle =>
      rw [mul_comm_r (α i0 + β i1) (α i1 + β i0)]
      have hsum_rev' : γ i0 + γ i1 = (α i1 + β i0) + (α i0 + β i1) := by
        rw [hsum_rev, add_comm_r]
      exact prod_majorization_2x2 hsum_rev' hle hlow2
  exact ⟨hkf2, hkf1, hlow1, hlow2, hdet_low, hdet_high⟩

end KyFanAndLidskiiFiedler

-- ============================================================================
-- §7. Exhaustive Refutations of All Five Readings of Antisymmetrization (n ≥ 2)
-- ============================================================================

section AllFiveRefutations

def det2 {R : Type u} [LinearOrderedCommRing R] (M : RMat R 2) : R :=
  M ⟨0, by decide⟩ ⟨0, by decide⟩ * M ⟨1, by decide⟩ ⟨1, by decide⟩ -
  M ⟨0, by decide⟩ ⟨1, by decide⟩ * M ⟨1, by decide⟩ ⟨0, by decide⟩

def charDisc2 {R : Type u} [LinearOrderedCommRing R] (M : RMat R 2) : R :=
  let tr := M ⟨0, by decide⟩ ⟨0, by decide⟩ + M ⟨1, by decide⟩ ⟨1, by decide⟩
  let four : R := (1 + 1) * (1 + 1)
  tr * tr - four * det2 M

def det3 {R : Type u} [LinearOrderedCommRing R] (M : RMat R 3) : R :=
  let i0 : Fin 3 := ⟨0, by decide⟩
  let i1 : Fin 3 := ⟨1, by decide⟩
  let i2 : Fin 3 := ⟨2, by decide⟩
  M i0 i0 * (M i1 i1 * M i2 i2 - M i1 i2 * M i2 i1) -
  M i0 i1 * (M i1 i0 * M i2 i2 - M i1 i2 * M i2 i0) +
  M i0 i2 * (M i1 i0 * M i2 i1 - M i1 i1 * M i2 i0)

theorem fin2_all {P : Fin 2 → Prop}
    (h0 : P ⟨0, by decide⟩) (h1 : P ⟨1, by decide⟩) : ∀ i : Fin 2, P i
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨k + 2, hk⟩ => False.elim (by omega)

theorem fin3_all {P : Fin 3 → Prop}
    (h0 : P ⟨0, by decide⟩) (h1 : P ⟨1, by decide⟩) (h2 : P ⟨2, by decide⟩) : ∀ i : Fin 3, P i
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2
  | ⟨k + 3, hk⟩ => False.elim (by omega)

def ofNatR (R : Type u) [LinearOrderedCommRing R] : Nat → R
  | 0 => 0
  | k + 1 => ofNatR R k + 1

theorem ofNatR_pos {R : Type u} [LinearOrderedCommRing R] : ∀ k : Nat, (0 : R) < ofNatR R (k + 1)
  | 0 => by simp only [ofNatR]; rw [zero_add_r]; exact LinearOrderedCommRing.zero_lt_one
  | k + 1 => by
    simp only [ofNatR]
    have h := add_lt_add_of_lt_of_le_r (ofNatR_pos (R := R) k) (le_of_lt_r LinearOrderedCommRing.zero_lt_one)
    rwa [add_zero_r] at h

-- ----------------------------------------------------------------------------
-- Reading 1: Matrix Antisymmetrization A(M) = (1/2)(M - M^T)
-- ----------------------------------------------------------------------------

section Reading1
variable {F : Type u} [LinearOrderedField F]

def posDiagA (n : Nat) : RMat F n := diagMat (fun i => ofNatR F (n - i.1))
def posDiagBRev (n : Nat) : RMat F n := diagMat (fun i => ofNatR F (i.1 + 1))

/-- Non-Hermitian `n x n` witness pair (`n = m + 2 ≥ 2`) with nontrivial antisymmetric parts:
    `M_1 = [[4, 1], [-1, 2]] ⊕ 3 I_m`, `M_2 = [[4, -1], [1, 2]] ⊕ 3 I_m`. -/
def nonHermM1 (m : Nat) : RMat F (m + 2) := fun i j =>
  if i.1 = 0 ∧ j.1 = 0 then ofNatR F 4
  else if i.1 = 0 ∧ j.1 = 1 then 1
  else if i.1 = 1 ∧ j.1 = 0 then -(1 : F)
  else if i.1 = 1 ∧ j.1 = 1 then ofNatR F 2
  else if i = j then ofNatR F 3
  else 0

def nonHermM2 (m : Nat) : RMat F (m + 2) := transpose (nonHermM1 m)

def hkComplex2 : RMat F 2 := fun i j =>
  if i.1 = 0 ∧ j.1 = 0 then ofNatR F 4
  else if i.1 = 0 ∧ j.1 = 1 then ofNatR F 3
  else if i.1 = 1 ∧ j.1 = 0 then -(ofNatR F 3)
  else 0

/-- Refutation of Reading 1 for all `n = m + 2 ≥ 2`:
    (1A) On the symmetric domain, `skewPart` vanishes identically (trace `0`), whereas the
         true reverse-order optimum `posDiagA + posDiagBRev` is purely symmetric with positive trace.
    (1B) On non-symmetric decompositions `M = S(M) + A(M)`, `nonHermM1` and `nonHermM2` have
         nonzero `skewPart`, satisfy `(M_r - 3 I)^2 = 0` (all eigenvalues equal `3`), yet
         `M_1 + M_2` has top eigenvalue `8 > 3 + 3 = 6` and 2x2 determinant `32 < 36`;
         moreover `hkComplex2 = diag(4,0) + [[0,3],[-3,0]]` has negative discriminant `-20 < 0`. -/
theorem refute_reading1_matrix_antisymmetrization (m : Nat) :
    (∀ A B : RMat F (m + 2), IsSym A → IsSym B →
      skewPart A = zeroMat (m + 2) ∧ skewPart B = zeroMat (m + 2) ∧
      skewPart (matAdd A B) = zeroMat (m + 2)) ∧
    (IsSym (matAdd (posDiagA (m + 2) : RMat F (m + 2)) (posDiagBRev (m + 2))) ∧
      trace (skewPart (matAdd (posDiagA (m + 2) : RMat F (m + 2)) (posDiagBRev (m + 2)))) = 0 ∧
      0 < trace (matAdd (posDiagA (m + 2) : RMat F (m + 2)) (posDiagBRev (m + 2)))) ∧
    (skewPart (nonHermM1 m : RMat F (m + 2)) ≠ zeroMat (m + 2) ∧
      matVec (matAdd (nonHermM1 m : RMat F (m + 2)) (nonHermM2 m))
        (fun i => if i.1 = 0 then (1 : F) else 0) =
        (fun i => if i.1 = 0 then ofNatR F 8 else 0) ∧
      ofNatR F 6 < ofNatR F 8 ∧
      det2 (matAdd (nonHermM1 0 : RMat F 2) (nonHermM2 0)) < ofNatR F 6 * ofNatR F 6 ∧
      charDisc2 (hkComplex2 : RMat F 2) < 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A B hA hB
    exact ⟨(skewPart_eq_zero_iff_isSym A).mpr hA,
           (skewPart_eq_zero_iff_isSym B).mpr hB,
           (skewPart_eq_zero_iff_isSym (matAdd A B)).mpr (isSym_add hA hB)⟩
  · have hsym : IsSym (matAdd (posDiagA (m + 2) : RMat F (m + 2)) (posDiagBRev (m + 2))) :=
      isSym_add (isSym_diag _) (isSym_diag _)
    refine ⟨hsym, ?_, ?_⟩
    · rw [(skewPart_eq_zero_iff_isSym _).mpr hsym]; exact finSum_zero (m + 2)
    · unfold trace
      simp only [finSum]
      have h0 : 0 < matAdd (posDiagA (m + 2) : RMat F (m + 2)) (posDiagBRev (m + 2))
                  ⟨0, Nat.zero_lt_succ (m + 1)⟩ ⟨0, Nat.zero_lt_succ (m + 1)⟩ := by
        dsimp [matAdd, posDiagA, posDiagBRev, diagMat]
        have ht := add_lt_add_of_lt_of_le_r (ofNatR_pos (R := F) (m + 1)) (le_of_lt_r (ofNatR_pos (R := F) 0))
        rwa [zero_add_r] at ht
      have hrest : 0 ≤ finSum (m + 1) (fun i =>
          matAdd (posDiagA (m + 2) : RMat F (m + 2)) (posDiagBRev (m + 2))
            ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) := by
        apply finSum_nonneg; intro i
        dsimp [matAdd, posDiagA, posDiagBRev, diagMat]
        rw [if_pos rfl, if_pos rfl]
        have ha : m + 2 - (i.1 + 1) = (m - i.1) + 1 := by omega
        rw [ha]
        have h := add_le_add_r (le_of_lt_r (ofNatR_pos (R := F) (m - i.1))) (le_of_lt_r (ofNatR_pos (R := F) (i.1 + 1)))
        rwa [zero_add_r] at h
      have htot := add_lt_add_of_lt_of_le_r h0 hrest
      rwa [zero_add_r] at htot
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hzero
      have hsym := (skewPart_eq_zero_iff_isSym (nonHermM1 m : RMat F (m + 2))).mp hzero
      have e := congrFun (congrFun hsym ⟨0, by omega⟩) ⟨1, by omega⟩
      dsimp [transpose, nonHermM1] at e
      have h1_eq_neg1 : -(1 : F) = 1 := e
      have htwo0 : (1 : F) + 1 = 0 := by
        conv => lhs; arg 1; rw [← h1_eq_neg1]
        exact neg_add_cancel_r 1
      exact (ne_of_lt_r two_pos_r) htwo0.symm
    · funext i
      unfold matVec
      let z0 : Fin (m + 2) := ⟨0, Nat.zero_lt_succ (m + 1)⟩
      have hfn : (fun j : Fin (m + 2) => matAdd (nonHermM1 m : RMat F (m + 2)) (nonHermM2 m) i j *
                  (if j.1 = 0 then (1 : F) else 0)) =
                 (fun j : Fin (m + 2) => if j = z0 then
                   matAdd (nonHermM1 m : RMat F (m + 2)) (nonHermM2 m) i z0 else 0) := by
        funext j
        by_cases hj : j = z0
        · subst hj; dsimp [z0]; simp [mul_one_r]
        · have hj0 : j.1 ≠ 0 := fun e => hj (Fin.ext e)
          simp [hj, hj0, mul_zero_r]
      rw [hfn, finSum_delta]
      unfold matAdd nonHermM2 transpose nonHermM1
      by_cases hi0 : i.1 = 0
      · have hz0 : z0.1 = 0 := rfl
        simp [hi0, hz0]
        simp only [ofNatR, zero_add_r]
        let o : F := 1
        change (((o + o) + o) + o) + (((o + o) + o) + o) =
               ((((((o + o) + o) + o) + o) + o) + o) + o
        rw [← add_assoc_r, ← add_assoc_r, ← add_assoc_r]
      · by_cases hi1 : i.1 = 1
        · have hz0 : z0.1 = 0 := rfl
          simp [hi0, hi1, hz0, neg_add_cancel_r]
        · have hz0 : z0.1 = 0 := rfl
          have hne0 : i ≠ z0 := fun e => hi0 (congrArg Fin.val e)
          have hne0' : z0 ≠ i := fun e => hne0 e.symm
          simp [hi0, hi1, hz0, hne0, hne0', add_zero_r]
    · -- ofNatR F 6 < ofNatR F 8
      have h7 : ofNatR F 6 < ofNatR F 7 := by
        change ofNatR F 6 < ofNatR F 6 + 1
        have h := add_lt_add_left_r (LinearOrderedCommRing.zero_lt_one (R := F)) (ofNatR F 6)
        rwa [add_zero_r] at h
      have h8 : ofNatR F 7 < ofNatR F 8 := by
        change ofNatR F 7 < ofNatR F 7 + 1
        have h := add_lt_add_left_r (LinearOrderedCommRing.zero_lt_one (R := F)) (ofNatR F 7)
        rwa [add_zero_r] at h
      exact lt_trans_r h7 h8
    · -- det2(M1_0 + M2_0) = 8 * 4 - 0 * 0 = 32 < 36 = 6 * 6
      unfold det2
      dsimp [matAdd, nonHermM2, transpose, nonHermM1]
      rw [neg_add_cancel_r, add_neg_cancel_r, mul_zero_r, sub_eq_add_neg_r, neg_zero_r, add_zero_r]
      -- Show (4 + 4) * (2 + 2) < 6 * 6 via 6*6 - (4+4)*(2+2) = (6-4)*(6-2) ... Wait:
      -- Use fiedler_swap_lt! (4 + 4)? Wait: (6 + 0)? Even simpler:
      -- 6 = 4 + 2, 6 = 4 + 2? No: (4 + 4) * (2 + 2) = 8 * 4, and 6 * 6 = (4 + 2) * (2 + 4)!!
      -- fiedler_swap_lt on a1 = 4, a2 = 2, b1 = 4, b2 = 2 gives:
      -- (4 + 4) * (2 + 2) < (4 + 2) * (2 + 4)!!
      have h2_lt_4 : ofNatR F 2 < ofNatR F 4 := by
        have h3 : ofNatR F 2 < ofNatR F 3 := by
          change ofNatR F 2 < ofNatR F 2 + 1
          have h := add_lt_add_left_r (LinearOrderedCommRing.zero_lt_one (R := F)) (ofNatR F 2)
          rwa [add_zero_r] at h
        have h4 : ofNatR F 3 < ofNatR F 4 := by
          change ofNatR F 3 < ofNatR F 3 + 1
          have h := add_lt_add_left_r (LinearOrderedCommRing.zero_lt_one (R := F)) (ofNatR F 3)
          rwa [add_zero_r] at h
        exact lt_trans_r h3 h4
      have hsw := fiedler_swap_lt h2_lt_4 h2_lt_4
      have h42 : ofNatR F 4 + ofNatR F 2 = ofNatR F 6 := by
        simp only [ofNatR, zero_add_r]
        rw [← add_assoc_r]
      have h24 : ofNatR F 2 + ofNatR F 4 = ofNatR F 6 := by
        rw [add_comm_r, h42]
      rwa [h42, h24] at hsw
    · -- charDisc2 hkComplex2 = (4 + 0)^2 - 4 * (4*0 - 3*(-3)) = 16 - 36 < 0
      unfold charDisc2 det2
      dsimp [hkComplex2]
      rw [add_zero_r, mul_zero_r, mul_neg_r, sub_eq_add_neg_r 0, zero_add_r, neg_neg_r]
      -- Goal: 4 * 4 - ((1+1)*(1+1)) * (3 * 3) < 0, i.e., 4 * 4 < 4 * (3 * 3)
      have h4eq : ((1 : F) + 1) * (1 + 1) = ofNatR F 4 := by
        simp only [ofNatR, zero_add_r, right_distrib_r, left_distrib_r, one_mul_r]
        rw [← add_assoc_r]
      rw [h4eq]
      have h4_lt_9 : ofNatR F 4 < ofNatR F 3 * ofNatR F 3 := by
        -- 3 * 3 = 3 * (2 + 1) = 3 * 2 + 3 = 6 + 3 > 4
        have h3_gt_1 : (1 : F) < ofNatR F 3 := by
          simp only [ofNatR, zero_add_r]
          have h2 : (1 : F) < 1 + 1 := by
            have ht := add_lt_add_left_r (LinearOrderedCommRing.zero_lt_one (R := F)) 1
            rwa [add_zero_r] at ht
          have h3 : (1 : F) + 1 < (1 + 1) + 1 := by
            have ht := add_lt_add_left_r (LinearOrderedCommRing.zero_lt_one (R := F)) (1 + 1)
            rwa [add_zero_r] at ht
          exact lt_trans_r h2 h3
        -- (3 - 2) > 0 => 3*3 = (2+1)*(2+1) = 4 + 4 + 1 > 4
        have h3eq : ofNatR F 3 = ofNatR F 2 + 1 := rfl
        have h22 : ofNatR F 2 * ofNatR F 2 = ofNatR F 4 := by
          have h2eq : ofNatR F 2 = (1 : F) + 1 := by simp only [ofNatR, zero_add_r]
          rw [h2eq, h4eq]
        rw [h3eq, right_distrib_r, left_distrib_r, left_distrib_r, h22, mul_one_r, one_mul_r, one_mul_r]
        have hpos_rem : (0 : F) < ofNatR F 2 + (ofNatR F 2 + 1) := by
          have ht := add_lt_add_of_lt_of_le_r (ofNatR_pos (R := F) 1) (le_of_lt_r (ofNatR_pos (R := F) 2))
          rwa [zero_add_r] at ht
        have htot : ofNatR F 4 + 0 < ofNatR F 4 + (ofNatR F 2 + (ofNatR F 2 + 1)) :=
          add_lt_add_left_r hpos_rem (ofNatR F 4)
        rw [add_zero_r, ← add_assoc_r (ofNatR F 4) (ofNatR F 2)] at htot
        exact htot
      have hmul : ofNatR F 4 * ofNatR F 4 < ofNatR F 4 * (ofNatR F 3 * ofNatR F 3) := by
        rw [mul_comm_r (ofNatR F 4) (ofNatR F 3 * ofNatR F 3)]
        exact mul_lt_mul_of_pos_right_r h4_lt_9 (ofNatR_pos (R := F) 3)
      have hdiff_pos : (0 : F) < ofNatR F 4 * (ofNatR F 3 * ofNatR F 3) - ofNatR F 4 * ofNatR F 4 :=
        sub_pos_iff_r.mpr hmul
      -- a - b < 0 ↔ a < b
      rw [lt_iff_le_not_le_r]
      refine ⟨?_, ?_⟩
      · have hle := le_of_lt_r hmul
        have h' := add_le_add_right_r hle (-(ofNatR F 4 * (ofNatR F 3 * ofNatR F 3)))
        rwa [add_neg_cancel_r, ← sub_eq_add_neg_r] at h'
      · intro hge
        have hle := sub_nonneg_iff_r.mp hge
        exact ((lt_iff_le_not_le_r _ _).mp hmul).2 hle

end Reading1

-- ----------------------------------------------------------------------------
-- Reading 2: Skew-Symmetric / Skew-Hermitian Basis Conjugation A + K B K^*
-- ----------------------------------------------------------------------------

section Reading2

/-- Odd-dimension singularity (`n = 3` over any `LinearOrderedCommRing R`):
    Every `3 x 3` skew-symmetric matrix has determinant `0` and hence cannot be orthogonal. -/
theorem det3_eq_zero_of_isSkewSym {R : Type u} [LinearOrderedCommRing R]
    {K : RMat R 3} (hK : IsSkewSym K) : det3 K = 0 := by
  let i0 : Fin 3 := ⟨0, by decide⟩
  let i1 : Fin 3 := ⟨1, by decide⟩
  let i2 : Fin 3 := ⟨2, by decide⟩
  have d0 : K i0 i0 = 0 := skewSym_diag_zero hK i0
  have d1 : K i1 i1 = 0 := skewSym_diag_zero hK i1
  have d2 : K i2 i2 = 0 := skewSym_diag_zero hK i2
  have s10 : K i1 i0 = -(K i0 i1) := congrFun (congrFun hK i0) i1
  have s20 : K i2 i0 = -(K i0 i2) := congrFun (congrFun hK i0) i2
  have s21 : K i2 i1 = -(K i1 i2) := congrFun (congrFun hK i1) i2
  change K i0 i0 * (K i1 i1 * K i2 i2 - K i1 i2 * K i2 i1) -
         K i0 i1 * (K i1 i0 * K i2 i2 - K i1 i2 * K i2 i0) +
         K i0 i2 * (K i1 i0 * K i2 i1 - K i1 i1 * K i2 i0) = 0
  rw [d0, d1, d2, s10, s20, s21]
  rw [zero_mul_r, zero_mul_r, mul_zero_r]
  let u := K i0 i1
  let v := K i0 i2
  let w := K i1 i2
  change (0 - u * (0 - w * -v)) + v * (-u * -w - 0) = 0
  rw [sub_eq_add_neg_r 0, zero_add_r, sub_eq_add_neg_r 0, zero_add_r,
      sub_eq_add_neg_r (-u * -w) 0, neg_zero_r, add_zero_r,
      mul_neg_r w v, neg_neg_r, neg_mul_neg_r u w]
  have heq : v * (u * w) = u * (w * v) := by
    calc v * (u * w) = (u * w) * v := mul_comm_r _ _
      _ = u * (w * v) := mul_assoc_r _ _ _
  rw [heq, neg_add_cancel_r]

/-- Universal 2x2 Rational Counterexample over `QField` (and lifted to all `n ≥ 2`):
    `A = diag(25, 0)`, `B = [[16, 12], [12, 9]]`.
    Symmetric orthogonal `Q = (1/5)[[-3, 4], [4, 3]]` achieves `det(A + Q B Q^T) = 625`,
    whereas EVERY orthogonal skew-symmetric `K` gives `det(A + K B K^T) = 400 < 625`. -/
def rotA2Q : RMat QField 2 := fun i j =>
  if i.1 = 0 ∧ j.1 = 0 then QField.ofInt 25 else 0

def rotB2Q : RMat QField 2 := fun i j =>
  if i.1 = 0 ∧ j.1 = 0 then QField.ofInt 16
  else if i.1 = 1 ∧ j.1 = 1 then QField.ofInt 9
  else QField.ofInt 12

def symReflectQ2 : RMat QField 2 := fun i j =>
  if i.1 = 0 ∧ j.1 = 0 then QField.mk (-3) 5 (by decide)
  else if i.1 = 1 ∧ j.1 = 1 then QField.mk 3 5 (by decide)
  else QField.mk 4 5 (by decide)

theorem refute_reading2_real_skew_conj_2x2 :
    IsSym symReflectQ2 ∧
    IsOrthogonal symReflectQ2 ∧
    det2 (matAdd rotA2Q (matMul symReflectQ2 (matMul rotB2Q (transpose symReflectQ2)))) =
      QField.ofInt 625 ∧
    ∀ K : RMat QField 2, IsSkewSym K → IsOrthogonal K →
      det2 (matAdd rotA2Q (matMul K (matMul rotB2Q (transpose K)))) = QField.ofInt 400 ∧
      det2 (matAdd rotA2Q (matMul K (matMul rotB2Q (transpose K)))) <
        det2 (matAdd rotA2Q (matMul symReflectQ2 (matMul rotB2Q (transpose symReflectQ2)))) := by
  have hsymQ : IsSym symReflectQ2 := by
    funext i j; revert i j; apply fin2_all <;> apply fin2_all <;> rfl
  have horthQ : IsOrthogonal symReflectQ2 := by
    constructor <;> (
      funext i j; revert i j; apply fin2_all <;> apply fin2_all <;> (
        unfold matMul transpose symReflectQ2 idMat
        simp only [finSum]
        dsimp
        rw [QField.mk_mul, QField.mk_mul, add_zero_r, QField.mk_add]
        apply (QField.mk_eq_iff _ (by decide)).mpr
        decide))
  have hdetOpt : det2 (matAdd rotA2Q (matMul symReflectQ2 (matMul rotB2Q (transpose symReflectQ2)))) =
                 QField.ofInt 625 := by
    unfold det2 matAdd rotA2Q matMul symReflectQ2 rotB2Q transpose QField.ofInt
    simp only [finSum]
    dsimp
    repeat rw [add_zero_r]
    repeat rw [zero_add_r]
    repeat rw [QField.mk_mul]
    repeat rw [QField.mk_add]
    repeat rw [QField.mk_mul]
    repeat rw [QField.mk_add]
    repeat rw [QField.mk_mul]
    rw [QField.mk_sub]
    apply (QField.mk_eq_iff _ (by decide)).mpr
    decide
  refine ⟨hsymQ, horthQ, hdetOpt, ?_⟩
  intro K hKskew hKorth
  let i0 : Fin 2 := ⟨0, Nat.zero_lt_succ 1⟩
  let i1 : Fin 2 := ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩
  have hk00 : K i0 i0 = 0 := skewSym_diag_zero hKskew i0
  have hk11 : K i1 i1 = 0 := skewSym_diag_zero hKskew i1
  have hk10 : K i1 i0 = -(K i0 i1) := congrFun (congrFun hKskew i0) i1
  let s := K i0 i1
  have hs2 : s * s = 1 := by
    have e := congrFun (congrFun hKorth.1 i1) i1
    unfold matMul transpose idMat at e
    simp only [finSum] at e
    change K i0 i1 * K i0 i1 + (K i1 i1 * K i1 i1 + 0) = 1 at e
    rw [hk11, zero_mul_r, add_zero_r, add_zero_r] at e
    exact e
  have hKBKT_00 : matMul K (matMul rotB2Q (transpose K)) i0 i0 = QField.ofInt 9 := by
    unfold matMul transpose rotB2Q
    simp only [finSum]
    change K i0 i0 * (QField.ofInt 16 * K i0 i0 + (QField.ofInt 12 * K i0 i1 + 0)) +
           (K i0 i1 * (QField.ofInt 12 * K i0 i0 + (QField.ofInt 9 * K i0 i1 + 0)) + 0) = QField.ofInt 9
    rw [hk00]
    change (0 * (QField.ofInt 16 * 0 + (QField.ofInt 12 * s + 0)) +
            (s * (QField.ofInt 12 * 0 + (QField.ofInt 9 * s + 0)) + 0)) = QField.ofInt 9
    rw [mul_zero_r, mul_zero_r, zero_add_r, zero_add_r, add_zero_r, add_zero_r, zero_mul_r,
        zero_add_r, add_zero_r, ← mul_assoc_r s (QField.ofInt 9) s, mul_comm_r s (QField.ofInt 9),
        mul_assoc_r, hs2, mul_one_r]
  have hKBKT_11 : matMul K (matMul rotB2Q (transpose K)) i1 i1 = QField.ofInt 16 := by
    unfold matMul transpose rotB2Q
    simp only [finSum]
    change K i1 i0 * (QField.ofInt 16 * K i1 i0 + (QField.ofInt 12 * K i1 i1 + 0)) +
           (K i1 i1 * (QField.ofInt 12 * K i1 i0 + (QField.ofInt 9 * K i1 i1 + 0)) + 0) = QField.ofInt 16
    rw [hk11, hk10]
    change (-s * (QField.ofInt 16 * -s + (QField.ofInt 12 * 0 + 0)) +
            (0 * (QField.ofInt 12 * -s + (QField.ofInt 9 * 0 + 0)) + 0)) = QField.ofInt 16
    rw [mul_zero_r, add_zero_r, add_zero_r, zero_mul_r, add_zero_r, add_zero_r,
        mul_neg_r (QField.ofInt 16) s, neg_mul_neg_r, ← mul_assoc_r s (QField.ofInt 16) s,
        mul_comm_r s (QField.ofInt 16), mul_assoc_r, hs2, mul_one_r]
  have hKBKT_01 : matMul K (matMul rotB2Q (transpose K)) i0 i1 = QField.ofInt (-12) := by
    unfold matMul transpose rotB2Q
    simp only [finSum]
    change K i0 i0 * (QField.ofInt 16 * K i1 i0 + (QField.ofInt 12 * K i1 i1 + 0)) +
           (K i0 i1 * (QField.ofInt 12 * K i1 i0 + (QField.ofInt 9 * K i1 i1 + 0)) + 0) = QField.ofInt (-12)
    rw [hk00, hk11, hk10]
    change (0 * (QField.ofInt 16 * -s + (QField.ofInt 12 * 0 + 0)) +
            (s * (QField.ofInt 12 * -s + (QField.ofInt 9 * 0 + 0)) + 0)) = QField.ofInt (-12)
    rw [zero_mul_r, zero_add_r, add_zero_r, mul_zero_r, add_zero_r, add_zero_r,
        mul_neg_r (QField.ofInt 12) s, mul_neg_r s, ← mul_assoc_r s (QField.ofInt 12) s,
        mul_comm_r s (QField.ofInt 12), mul_assoc_r, hs2, mul_one_r, QField.ofInt_neg]
  have hKBKT_10 : matMul K (matMul rotB2Q (transpose K)) i1 i0 = QField.ofInt (-12) := by
    unfold matMul transpose rotB2Q
    simp only [finSum]
    change K i1 i0 * (QField.ofInt 16 * K i0 i0 + (QField.ofInt 12 * K i0 i1 + 0)) +
           (K i1 i1 * (QField.ofInt 12 * K i0 i0 + (QField.ofInt 9 * K i0 i1 + 0)) + 0) = QField.ofInt (-12)
    rw [hk00, hk11, hk10]
    change (-s * (QField.ofInt 16 * 0 + (QField.ofInt 12 * s + 0)) +
            (0 * (QField.ofInt 12 * 0 + (QField.ofInt 9 * s + 0)) + 0)) = QField.ofInt (-12)
    rw [mul_zero_r, zero_add_r, add_zero_r, zero_mul_r, add_zero_r, add_zero_r,
        neg_mul_r, ← mul_assoc_r s (QField.ofInt 12) s,
        mul_comm_r s (QField.ofInt 12), mul_assoc_r, hs2, mul_one_r, QField.ofInt_neg]
  have hdetK : det2 (matAdd rotA2Q (matMul K (matMul rotB2Q (transpose K)))) = QField.ofInt 400 := by
    unfold det2 matAdd
    change (rotA2Q i0 i0 + matMul K (matMul rotB2Q (transpose K)) i0 i0) *
           (rotA2Q i1 i1 + matMul K (matMul rotB2Q (transpose K)) i1 i1) -
           (rotA2Q i0 i1 + matMul K (matMul rotB2Q (transpose K)) i0 i1) *
           (rotA2Q i1 i0 + matMul K (matMul rotB2Q (transpose K)) i1 i0) = QField.ofInt 400
    rw [hKBKT_00, hKBKT_11, hKBKT_01, hKBKT_10]
    change (QField.ofInt 25 + QField.ofInt 9) * (0 + QField.ofInt 16) -
           (0 + QField.ofInt (-12)) * (0 + QField.ofInt (-12)) = QField.ofInt 400
    repeat rw [zero_add_r]
    rw [← QField.ofInt_add, ← QField.ofInt_mul, ← QField.ofInt_mul, ← QField.ofInt_sub]
    rfl
  refine ⟨hdetK, ?_⟩
  rw [hdetK, hdetOpt, QField.ofInt_lt_iff]
  decide

/- Complex Skew-Hermitian 3-Cycle Obstruction (`n = 3` over `Complex R`): -/
section ComplexThreeCycle
variable {R : Type u} [LinearOrderedCommRing R]

def cFinSum : (n : Nat) → (Fin n → Complex R) → Complex R
  | 0, _ => 0
  | n + 1, f => f ⟨0, Nat.zero_lt_succ n⟩ + cFinSum n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

def cMatAdd {n : Nat} (A B : CMat R n) : CMat R n := fun i j => A i j + B i j
def cMatNeg {n : Nat} (A : CMat R n) : CMat R n := fun i j => -(A i j)
def cAdj {n : Nat} (A : CMat R n) : CMat R n := fun i j => Complex.conj (A j i)
def cMatMul {n : Nat} (A B : CMat R n) : CMat R n :=
  fun i j => cFinSum n (fun k => A i k * B k j)
def cDiag {n : Nat} (d : Fin n → R) : CMat R n :=
  fun i j => if i = j then Complex.ofReal (d i) else 0

def IsSkewHermitian {n : Nat} (U : CMat R n) : Prop := cAdj U = cMatNeg U
def IsUnitary {n : Nat} (U : CMat R n) : Prop :=
  cMatMul (cAdj U) U = cDiag (fun _ => 1) ∧ cMatMul U (cAdj U) = cDiag (fun _ => 1)

def cycleA3 : CMat R 3 := cDiag fun i =>
  if i.1 = 0 then ofNatR R 3 else if i.1 = 1 then ofNatR R 2 else 1

def cycleB3 : CMat R 3 := cDiag fun i =>
  if i.1 = 0 then ofNatR R 2 else if i.1 = 1 then ofNatR R 3 else 1

def cycleP3 : CMat R 3 := fun i j =>
  if (i.1 = 0 ∧ j.1 = 2) ∨ (i.1 = 1 ∧ j.1 = 0) ∨ (i.1 = 2 ∧ j.1 = 1) then 1 else 0

theorem cAdd_zero (z : Complex R) : z + 0 = z := by
  apply Complex.ext <;> exact add_zero_r _

theorem cZero_add (z : Complex R) : 0 + z = z := by
  apply Complex.ext <;> exact zero_add_r _

theorem cMul_zero (z : Complex R) : z * 0 = 0 := by
  apply Complex.ext
  · change z.re * 0 - z.im * 0 = 0; rw [mul_zero_r, mul_zero_r, sub_self_r]
  · change z.re * 0 + z.im * 0 = 0; rw [mul_zero_r, mul_zero_r, add_zero_r]

theorem cZero_mul (z : Complex R) : 0 * z = 0 := by
  apply Complex.ext
  · change 0 * z.re - 0 * z.im = 0; rw [zero_mul_r, zero_mul_r, sub_self_r]
  · change 0 * z.im + 0 * z.re = 0; rw [zero_mul_r, zero_mul_r, add_zero_r]

theorem cMul_conj_self (z : Complex R) : (z * Complex.conj z).re = Complex.normSq z := by
  change z.re * z.re - z.im * (-z.im) = z.re * z.re + z.im * z.im
  rw [mul_neg_r, sub_eq_add_neg_r, neg_neg_r]

theorem refute_reading2_complex_skewHermitian_3cycle :
    IsUnitary (cycleP3 : CMat R 3) ∧
    cMatAdd cycleA3 (cMatMul cycleP3 (cMatMul cycleB3 (cAdj cycleP3))) =
      cDiag (fun _ => ofNatR R 4) ∧
    ∀ U : CMat R 3, IsSkewHermitian U → IsUnitary U →
      cMatAdd cycleA3 (cMatMul U (cMatMul cycleB3 (cAdj U))) ≠
        cDiag (fun _ => ofNatR R 4) := by
  have hc0_re : (0 : Complex R).re = 0 := rfl
  have hc0_im : (0 : Complex R).im = 0 := rfl
  have hc1_re : (1 : Complex R).re = 1 := rfl
  have hc1_im : (1 : Complex R).im = 0 := rfl
  have hadd_re (z w : Complex R) : (z + w).re = z.re + w.re := rfl
  have hadd_im (z w : Complex R) : (z + w).im = z.im + w.im := rfl
  have hmul_re (z w : Complex R) : (z * w).re = z.re * w.re - z.im * w.im := rfl
  have hmul_im (z w : Complex R) : (z * w).im = z.re * w.im + z.im * w.re := rfl
  have hsub_zero (x : R) : x - 0 = x := by
    rw [sub_eq_add_neg_r, neg_zero_r, add_zero_r]
  have hunitP : IsUnitary (cycleP3 : CMat R 3) := by
    constructor <;> (
      funext i j; revert i j; apply fin3_all <;> apply fin3_all <;> (
        unfold cMatMul cAdj cycleP3 cDiag
        simp only [cFinSum]
        apply Complex.ext <;> (
          dsimp [Complex.conj, Complex.ofReal]
          simp [hc0_re, hc0_im, hc1_re, hc1_im, hadd_re, hadd_im, hmul_re, hmul_im,
                mul_zero_r, zero_mul_r, mul_one_r, one_mul_r, add_zero_r, zero_add_r,
                sub_self_r, hsub_zero, neg_zero_r])))
  have hoptP : cMatAdd cycleA3 (cMatMul cycleP3 (cMatMul cycleB3 (cAdj cycleP3))) =
               cDiag (fun _ => ofNatR R 4) := by
    funext i j; revert i j; apply fin3_all <;> apply fin3_all <;> (
      unfold cMatAdd cycleA3 cycleP3 cycleB3 cMatMul cAdj cDiag
      simp only [cFinSum]
      apply Complex.ext <;> (
        dsimp [ofNatR, Complex.conj, Complex.ofReal]
        simp [hc0_re, hc0_im, hc1_re, hc1_im, hadd_re, hadd_im, hmul_re, hmul_im,
              mul_zero_r, zero_mul_r, mul_one_r, one_mul_r, add_zero_r, zero_add_r,
              sub_self_r, hsub_zero, neg_zero_r]
        repeat rw [← add_assoc_r]))
  refine ⟨hunitP, hoptP, ?_⟩
  intro U hSkew hUnit heq
  let i0 : Fin 3 := ⟨0, Nat.zero_lt_succ 2⟩
  let i1 : Fin 3 := ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 1)⟩
  let i2 : Fin 3 := ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 0))⟩
  let M := cMatMul U (cMatMul cycleB3 (cAdj U))
  have hM00 : (M i0 i0).re = 1 := by
    have e := congrFun (congrFun heq i0) i0
    have ere : (cMatAdd cycleA3 M i0 i0).re = ofNatR R 4 := congrArg Complex.re e
    change ofNatR R 3 + (M i0 i0).re = ofNatR R 3 + 1 at ere
    exact add_left_cancel_r ere
  have hM22 : (M i2 i2).re = ofNatR R 3 := by
    have e := congrFun (congrFun heq i2) i2
    have ere : (cMatAdd cycleA3 M i2 i2).re = ofNatR R 4 := congrArg Complex.re e
    change 1 + (M i2 i2).re = ofNatR R 4 at ere
    have h4 : ofNatR R 4 = 1 + ofNatR R 3 := by
      simp only [ofNatR, zero_add_r]
      rw [← add_assoc_r, ← add_assoc_r]
    rw [h4] at ere
    exact add_left_cancel_r ere
  have expandDiag (r : Fin 3) :
      (M r r).re = ofNatR R 2 * Complex.normSq (U r i0) +
                   (ofNatR R 3 * Complex.normSq (U r i1) + Complex.normSq (U r i2)) := by
    have term_eq (z : Complex R) (b : R) :
        (z * (Complex.ofReal b * Complex.conj z)).re = b * Complex.normSq z := by
      change z.re * (b * z.re - 0 * -z.im) - z.im * (b * -z.im + 0 * z.re) =
             b * (z.re * z.re + z.im * z.im)
      rw [zero_mul_r, zero_mul_r, sub_eq_add_neg_r (b * z.re) 0, neg_zero_r, add_zero_r,
          add_zero_r, mul_neg_r b z.im, mul_neg_r z.im, sub_eq_add_neg_r, neg_neg_r]
      calc z.re * (b * z.re) + z.im * (b * z.im)
          = b * (z.re * z.re) + b * (z.im * z.im) := by
              rw [← mul_assoc_r z.re b z.re, mul_comm_r z.re b, mul_assoc_r b z.re z.re,
                  ← mul_assoc_r z.im b z.im, mul_comm_r z.im b, mul_assoc_r b z.im z.im]
        _ = b * (z.re * z.re + z.im * z.im) := (left_distrib_r _ _ _).symm
    have hMB (k : Fin 3) :
        cMatMul cycleB3 (cAdj U) k r =
        (if k.1 = 0 then Complex.ofReal (ofNatR R 2)
         else if k.1 = 1 then Complex.ofReal (ofNatR R 3)
         else Complex.ofReal 1) * Complex.conj (U r k) := by
      revert k; apply fin3_all <;> (
        unfold cMatMul cycleB3 cDiag cAdj
        simp only [cFinSum]
        dsimp
        simp [cZero_mul, cZero_add, cAdd_zero])
    have hexpM : M r r =
        U r i0 * (Complex.ofReal (ofNatR R 2) * Complex.conj (U r i0)) +
        (U r i1 * (Complex.ofReal (ofNatR R 3) * Complex.conj (U r i1)) +
         (U r i2 * (Complex.ofReal 1 * Complex.conj (U r i2)) + 0)) := by
      change cFinSum 3 (fun k => U r k * cMatMul cycleB3 (cAdj U) k r) = _
      simp only [cFinSum]
      change U r i0 * cMatMul cycleB3 (cAdj U) i0 r +
             (U r i1 * cMatMul cycleB3 (cAdj U) i1 r +
              (U r i2 * cMatMul cycleB3 (cAdj U) i2 r + 0)) = _
      rw [hMB i0, hMB i1, hMB i2]; rfl
    rw [hexpM]
    change (U r i0 * (Complex.ofReal (ofNatR R 2) * Complex.conj (U r i0))).re +
           ((U r i1 * (Complex.ofReal (ofNatR R 3) * Complex.conj (U r i1))).re +
            ((U r i2 * (Complex.ofReal 1 * Complex.conj (U r i2))).re + 0)) = _
    rw [add_zero_r, term_eq (U r i0) (ofNatR R 2), term_eq (U r i1) (ofNatR R 3),
        term_eq (U r i2) 1, one_mul_r]
  have expandRow (r : Fin 3) :
      Complex.normSq (U r i0) + (Complex.normSq (U r i1) + Complex.normSq (U r i2)) = 1 := by
    have e := congrArg Complex.re (congrFun (congrFun hUnit.2 r) r)
    have hrhs : (cDiag (fun _ : Fin 3 => (1 : R)) r r).re = 1 := by
      dsimp [cDiag]; rw [if_pos rfl]; rfl
    rw [hrhs] at e
    change (U r i0 * Complex.conj (U r i0)).re +
           ((U r i1 * Complex.conj (U r i1)).re +
            ((U r i2 * Complex.conj (U r i2)).re + 0)) = 1 at e
    rwa [add_zero_r, cMul_conj_self, cMul_conj_self, cMul_conj_self] at e
  have hrow0 := expandRow i0
  have hdiag0 := (expandDiag i0).symm.trans hM00
  have hu00_0 : Complex.normSq (U i0 i0) = 0 := by
    have hdiff : (Complex.normSq (U i0 i0) + (ofNatR R 2 * Complex.normSq (U i0 i1))) + 1 = 0 + 1 := by
      rw [zero_add_r]
      calc (Complex.normSq (U i0 i0) + (ofNatR R 2 * Complex.normSq (U i0 i1))) + 1
          = (Complex.normSq (U i0 i0) + (ofNatR R 2 * Complex.normSq (U i0 i1))) +
            (Complex.normSq (U i0 i0) + (Complex.normSq (U i0 i1) + Complex.normSq (U i0 i2))) := by rw [hrow0]
        _ = ofNatR R 2 * Complex.normSq (U i0 i0) +
            (ofNatR R 3 * Complex.normSq (U i0 i1) + Complex.normSq (U i0 i2)) := by
              have h2x (x : R) : x + x = ofNatR R 2 * x := by
                simp only [ofNatR, zero_add_r, right_distrib_r, one_mul_r]
              have h3x (x : R) : ofNatR R 2 * x + x = ofNatR R 3 * x := by
                have h3eq : ofNatR R 3 = ofNatR R 2 + 1 := rfl
                rw [h3eq, right_distrib_r, one_mul_r]
              calc (Complex.normSq (U i0 i0) + ofNatR R 2 * Complex.normSq (U i0 i1)) +
                   (Complex.normSq (U i0 i0) + (Complex.normSq (U i0 i1) + Complex.normSq (U i0 i2)))
                  = (Complex.normSq (U i0 i0) + Complex.normSq (U i0 i0)) +
                    ((ofNatR R 2 * Complex.normSq (U i0 i1) + Complex.normSq (U i0 i1)) + Complex.normSq (U i0 i2)) := by
                      let a := Complex.normSq (U i0 i0)
                      let b := ofNatR R 2 * Complex.normSq (U i0 i1)
                      let c := Complex.normSq (U i0 i1)
                      let d := Complex.normSq (U i0 i2)
                      change (a + b) + (a + (c + d)) = (a + a) + ((b + c) + d)
                      calc (a + b) + (a + (c + d))
                          = a + (b + (a + (c + d))) := add_assoc_r _ _ _
                        _ = a + (a + (b + (c + d))) := by
                              rw [← add_assoc_r b a, add_comm_r b a, add_assoc_r]
                        _ = (a + a) + ((b + c) + d) := by
                              rw [← add_assoc_r a a, ← add_assoc_r b c]
                _ = ofNatR R 2 * Complex.normSq (U i0 i0) +
                    (ofNatR R 3 * Complex.normSq (U i0 i1) + Complex.normSq (U i0 i2)) := by
                      rw [h2x, h3x]
        _ = 1 := hdiag0
    have hsum0 := add_right_cancel_r hdiff
    have hnn1 := Complex.normSq_nonneg (U i0 i0)
    have hnn2 := LinearOrderedCommRing.mul_nonneg _ _ (le_of_lt_r (ofNatR_pos (R := R) 1)) (Complex.normSq_nonneg (U i0 i1))
    by_cases hz : Complex.normSq (U i0 i0) = 0
    · exact hz
    · have hp : 0 < Complex.normSq (U i0 i0) :=
        (lt_iff_le_not_le_r _ _).mpr ⟨hnn1, fun hle => hz (le_antisymm_r hle hnn1)⟩
      have htot := add_lt_add_of_lt_of_le_r hp hnn2
      rw [zero_add_r] at htot
      exact False.elim ((ne_of_lt_r htot) hsum0.symm)
  have hu01_0 : Complex.normSq (U i0 i1) = 0 := by
    rw [hu00_0, mul_zero_r, zero_add_r] at hdiag0
    rw [hu00_0, zero_add_r] at hrow0
    have h3 : ofNatR R 3 * Complex.normSq (U i0 i1) + Complex.normSq (U i0 i2) =
              ofNatR R 2 * Complex.normSq (U i0 i1) + (Complex.normSq (U i0 i1) + Complex.normSq (U i0 i2)) := by
      have h3eq : ofNatR R 3 = ofNatR R 2 + 1 := rfl
      rw [h3eq, right_distrib_r, one_mul_r, add_assoc_r]
    rw [h3, hrow0] at hdiag0
    have hdiag0' : ofNatR R 2 * Complex.normSq (U i0 i1) + 1 = 0 + 1 := by
      rw [zero_add_r]; exact hdiag0
    have h20 := add_right_cancel_r hdiag0'
    by_cases hz : Complex.normSq (U i0 i1) = 0
    · exact hz
    · have hnn := Complex.normSq_nonneg (U i0 i1)
      have hp : 0 < Complex.normSq (U i0 i1) :=
        (lt_iff_le_not_le_r _ _).mpr ⟨hnn, fun hle => hz (le_antisymm_r hle hnn)⟩
      have hprod := LinearOrderedCommRing.mul_pos _ _ (ofNatR_pos (R := R) 1) hp
      exact False.elim ((ne_of_lt_r hprod) h20.symm)
  have hu02_1 : Complex.normSq (U i0 i2) = 1 := by
    rwa [hu00_0, hu01_0, zero_add_r, zero_add_r] at hrow0
  have hrow2 := expandRow i2
  have hdiag2 := (expandDiag i2).symm.trans hM22
  have hu20_0 : Complex.normSq (U i2 i0) = 0 := by
    have h3row : ofNatR R 3 * Complex.normSq (U i2 i0) +
                 (ofNatR R 3 * Complex.normSq (U i2 i1) + ofNatR R 3 * Complex.normSq (U i2 i2)) =
                 ofNatR R 3 := by
      rw [← left_distrib_r, ← left_distrib_r, hrow2, mul_one_r]
    have hsplit3 : ofNatR R 3 * Complex.normSq (U i2 i0) +
                   (ofNatR R 3 * Complex.normSq (U i2 i1) + ofNatR R 3 * Complex.normSq (U i2 i2)) =
                   (Complex.normSq (U i2 i0) + ofNatR R 2 * Complex.normSq (U i2 i2)) +
                   (ofNatR R 2 * Complex.normSq (U i2 i0) +
                    (ofNatR R 3 * Complex.normSq (U i2 i1) + Complex.normSq (U i2 i2))) := by
      have h3a : ofNatR R 3 * Complex.normSq (U i2 i0) =
                 Complex.normSq (U i2 i0) + ofNatR R 2 * Complex.normSq (U i2 i0) := by
        have h : ofNatR R 3 = 1 + ofNatR R 2 := by
          simp only [ofNatR, zero_add_r]; rw [← add_assoc_r]
        rw [h, right_distrib_r, one_mul_r]
      have h3c : ofNatR R 3 * Complex.normSq (U i2 i2) =
                 ofNatR R 2 * Complex.normSq (U i2 i2) + Complex.normSq (U i2 i2) := by
        have h : ofNatR R 3 = ofNatR R 2 + 1 := rfl
        rw [h, right_distrib_r, one_mul_r]
      rw [h3a, h3c]
      let a1 := Complex.normSq (U i2 i0)
      let a2 := ofNatR R 2 * Complex.normSq (U i2 i0)
      let b := ofNatR R 3 * Complex.normSq (U i2 i1)
      let c2 := ofNatR R 2 * Complex.normSq (U i2 i2)
      let c1 := Complex.normSq (U i2 i2)
      change (a1 + a2) + (b + (c2 + c1)) = (a1 + c2) + (a2 + (b + c1))
      calc (a1 + a2) + (b + (c2 + c1))
          = a1 + (a2 + ((b + c1) + c2)) := by
              rw [add_comm_r c2 c1, ← add_assoc_r b c1 c2, add_assoc_r a1]
        _ = a1 + (c2 + (a2 + (b + c1))) := by
              rw [add_comm_r (b + c1) c2, ← add_assoc_r a2 c2, add_comm_r a2 c2, add_assoc_r]
        _ = (a1 + c2) + (a2 + (b + c1)) := (add_assoc_r _ _ _).symm
    rw [hsplit3, hdiag2] at h3row
    have h3row' : (Complex.normSq (U i2 i0) + ofNatR R 2 * Complex.normSq (U i2 i2)) + ofNatR R 3 =
                  0 + ofNatR R 3 := by
      rw [zero_add_r]; exact h3row
    have hsum0 := add_right_cancel_r h3row'
    have hnn1 := Complex.normSq_nonneg (U i2 i0)
    have hnn2 := LinearOrderedCommRing.mul_nonneg _ _ (le_of_lt_r (ofNatR_pos (R := R) 1)) (Complex.normSq_nonneg (U i2 i2))
    by_cases hz : Complex.normSq (U i2 i0) = 0
    · exact hz
    · have hp : 0 < Complex.normSq (U i2 i0) :=
        (lt_iff_le_not_le_r _ _).mpr ⟨hnn1, fun hle => hz (le_antisymm_r hle hnn1)⟩
      have htot := add_lt_add_of_lt_of_le_r hp hnn2
      rw [zero_add_r] at htot
      exact False.elim ((ne_of_lt_r htot) hsum0.symm)
  have hu20_eq : U i2 i0 = 0 := Complex.normSq_eq_zero_iff.mp hu20_0
  have hskew02 := congrFun (congrFun hSkew i0) i2
  dsimp [cAdj, cMatNeg] at hskew02
  rw [hu20_eq] at hskew02
  have hu02_eq : U i0 i2 = 0 := by
    apply Complex.ext
    · have ere : (0 : R) = -((U i0 i2).re) := congrArg Complex.re hskew02
      have hneg := congrArg Neg.neg ere
      rw [neg_zero_r, neg_neg_r] at hneg
      exact hneg.symm
    · have eim : -(0 : R) = -((U i0 i2).im) := congrArg Complex.im hskew02
      have hneg := congrArg Neg.neg eim
      rw [neg_neg_r, neg_neg_r] at hneg
      exact hneg.symm
  rw [Complex.normSq_eq_zero_iff.mpr hu02_eq] at hu02_1
  exact (ne_of_lt_r (LinearOrderedCommRing.zero_lt_one (R := R))) hu02_1

end ComplexThreeCycle
end Reading2

-- ----------------------------------------------------------------------------
-- Reading 3: Lie-Algebraic Commutator Antisymmetrization [A, B] = A B - B A
-- ----------------------------------------------------------------------------

section Reading3
variable {R : Type u} [LinearOrderedCommRing R]

def blochA (a : R) : RMat R 2 := fun i j =>
  if i.1 = 0 ∧ j.1 = 0 then a else if i.1 = 1 ∧ j.1 = 1 then -a else 0

def blochB (b c s : R) : RMat R 2 := fun i j =>
  if i.1 = 0 ∧ j.1 = 0 then b * c
  else if i.1 = 1 ∧ j.1 = 1 then -(b * c)
  else b * s

/-- Refutation of Reading 3 (Bloch-Sphere Commutator Identity):
    For `A = diag(a, -a)` and `B = [[b c, b s], [b s, -b c]]` (`c^2 + s^2 = 1`, `0 < a, b`),
    `-det_2(A + B) = a^2 + b^2 + 2 a b c` while `‖[A, B]‖_F^2 = 8 a^2 b^2 s^2`:
    - BOTH Lidskii-Fiedler extrema (`c = 1` same-order, `c = -1` reverse-order) have `[A, B] = 0`;
    - Maximal commutator (`c = 0, s = 1`) has `‖[A, B]‖_F^2 > 0` and strictly interior
      squared eigenvalue `(a - b)^2 < -det_2(A + B) < (a + b)^2`. -/
theorem refute_reading3_commutator_antisymmetrization
    {a b : R} (ha : 0 < a) (hb : 0 < b) :
    commutator (blochA a) (blochB b 1 0) = zeroMat 2 ∧
    commutator (blochA a) (blochB b (-1) 0) = zeroMat 2 ∧
    0 < frobNormSq (commutator (blochA a) (blochB b 0 1)) ∧
    (a - b) * (a - b) < -(det2 (matAdd (blochA a) (blochB b 0 1))) ∧
    -(det2 (matAdd (blochA a) (blochB b 0 1))) < (a + b) * (a + b) := by
  have hcomm1 : commutator (blochA a) (blochB b 1 0) = zeroMat 2 := by
    funext i j; revert i j; apply fin2_all <;> apply fin2_all <;> (
      unfold commutator matSub matMul blochA blochB zeroMat
      simp only [finSum]; dsimp
      simp only [mul_zero_r, zero_mul_r, add_zero_r, zero_add_r, sub_self_r]
      try (rw [mul_comm_r]; exact sub_self_r _))
  have hcomm_neg1 : commutator (blochA a) (blochB b (-1) 0) = zeroMat 2 := by
    funext i j; revert i j; apply fin2_all <;> apply fin2_all <;> (
      unfold commutator matSub matMul blochA blochB zeroMat
      simp only [finSum]; dsimp
      simp only [mul_zero_r, zero_mul_r, add_zero_r, zero_add_r, sub_self_r]
      try (rw [mul_comm_r]; exact sub_self_r _))
  have hfrob_pos : 0 < frobNormSq (commutator (blochA a) (blochB b 0 1)) := by
    unfold frobNormSq
    simp only [finSum]
    have h01 : 0 < commutator (blochA a) (blochB b 0 1) ⟨0, by decide⟩ ⟨1, by decide⟩ := by
      unfold commutator matSub matMul blochA blochB
      simp only [finSum]; dsimp
      rw [mul_zero_r, zero_mul_r, mul_zero_r, mul_one_r, add_zero_r, add_zero_r, add_zero_r,
          mul_neg_r, zero_add_r, sub_eq_add_neg_r, neg_neg_r, mul_comm_r b a]
      have hab := LinearOrderedCommRing.mul_pos a b ha hb
      have h := add_lt_add_of_lt_of_le_r hab (le_of_lt_r hab)
      rwa [zero_add_r] at h
    have hsq01 := LinearOrderedCommRing.mul_pos _ _ h01 h01
    let c00 := commutator (blochA a) (blochB b 0 1) ⟨0, by decide⟩ ⟨0, by decide⟩
    let c01 := commutator (blochA a) (blochB b 0 1) ⟨0, by decide⟩ ⟨1, by decide⟩
    let c10 := commutator (blochA a) (blochB b 0 1) ⟨1, by decide⟩ ⟨0, by decide⟩
    let c11 := commutator (blochA a) (blochB b 0 1) ⟨1, by decide⟩ ⟨1, by decide⟩
    change 0 < (c00 * c00 + (c01 * c01 + 0)) + ((c10 * c10 + (c11 * c11 + 0)) + 0)
    rw [add_zero_r, add_zero_r, add_zero_r]
    have hrow0 : 0 < c00 * c00 + c01 * c01 := by
      have ht := add_lt_add_of_le_of_lt_r (sq_nonneg_r c00) hsq01
      rwa [zero_add_r] at ht
    have hrow1 : 0 ≤ c10 * c10 + c11 * c11 := by
      have ht := add_le_add_r (sq_nonneg_r c10) (sq_nonneg_r c11)
      rwa [zero_add_r] at ht
    have htot := add_lt_add_of_lt_of_le_r hrow0 hrow1
    rwa [zero_add_r] at htot
  have hdet_mid : -(det2 (matAdd (blochA a) (blochB b 0 1))) = a * a + b * b := by
    unfold det2 matAdd blochA blochB; dsimp
    rw [mul_zero_r, add_zero_r, neg_zero_r, add_zero_r, zero_add_r, mul_one_r,
        mul_neg_r a a, sub_eq_add_neg_r, neg_add_r, neg_neg_r, neg_neg_r]
  have hab_pos : 0 < a * b + a * b := by
    have hab := LinearOrderedCommRing.mul_pos a b ha hb
    have ht := add_lt_add_of_lt_of_le_r hab (le_of_lt_r hab)
    rwa [zero_add_r] at ht
  refine ⟨hcomm1, hcomm_neg1, hfrob_pos, ?_, ?_⟩
  · rw [hdet_mid]
    have hexp : (a - b) * (a - b) + (a * b + a * b) = a * a + b * b := by
      rw [sub_mul_r, mul_sub_r, mul_sub_r, mul_comm_r b a]
      -- (a^2 - ab) - (ab - b^2) + (ab + ab) = a^2 + b^2
      rw [sub_eq_add_neg_r, sub_eq_add_neg_r, sub_eq_add_neg_r, neg_add_r, neg_neg_r]
      calc ((a * a + -(a * b)) + (-(a * b) + b * b)) + (a * b + a * b)
          = a * a + (b * b + ((-(a * b) + -(a * b)) + (a * b + a * b))) := by
              let x := a * a; let y := a * b; let z := b * b
              change ((x + -y) + (-y + z)) + (y + y) = x + (z + ((-y + -y) + (y + y)))
              calc ((x + -y) + (-y + z)) + (y + y)
                  = (x + (-y + (-y + z))) + (y + y) := by rw [add_assoc_r x]
                _ = (x + ((-y + -y) + z)) + (y + y) := by rw [← add_assoc_r (-y) (-y) z]
                _ = (x + (z + (-y + -y))) + (y + y) := by rw [add_comm_r (-y + -y) z]
                _ = x + (z + ((-y + -y) + (y + y))) := by rw [add_assoc_r x, add_assoc_r z]
        _ = a * a + b * b := by
              rw [← neg_add_r, neg_add_cancel_r, add_zero_r]
    have hlt := add_lt_add_left_r hab_pos ((a - b) * (a - b))
    rwa [add_zero_r, hexp] at hlt
  · rw [hdet_mid]
    have hexp : (a + b) * (a + b) = (a * a + b * b) + (a * b + a * b) := by
      rw [right_distrib_r, left_distrib_r, left_distrib_r, mul_comm_r b a]
      let x := a * a; let y := a * b; let z := b * b
      change (x + y) + (y + z) = (x + z) + (y + y)
      calc (x + y) + (y + z)
          = x + (y + (y + z)) := add_assoc_r _ _ _
        _ = x + ((y + y) + z) := by rw [← add_assoc_r y y z]
        _ = x + (z + (y + y)) := by rw [add_comm_r (y + y) z]
        _ = (x + z) + (y + y) := (add_assoc_r _ _ _).symm
    rw [hexp]
    have hlt := add_lt_add_left_r hab_pos (a * a + b * b)
    rwa [add_zero_r] at hlt

end Reading3

-- ----------------------------------------------------------------------------
-- Reading 4: Young Alternating Antisymmetrizer & Parity of w_0
-- ----------------------------------------------------------------------------

section Reading4

/-- Unnormalized Young alternating sum `∑_{σ ∈ S_2} sgn(σ) σ(b)` on `R^2`. -/
def youngAltSum2 {R : Type u} [LinearOrderedCommRing R] (b : Fin 2 → R) : Fin 2 → R :=
  fun i => if i.1 = 0 then b ⟨0, by decide⟩ - b ⟨1, by decide⟩
           else b ⟨1, by decide⟩ - b ⟨0, by decide⟩

/-- Unnormalized Young alternating sum `∑_{σ ∈ S_3} sgn(σ) σ(b)` on `R^3`. -/
def youngAltSum3 {R : Type u} [LinearOrderedCommRing R] (b : Fin 3 → R) : Fin 3 → R :=
  let b0 := b ⟨0, by decide⟩
  let b1 := b ⟨1, by decide⟩
  let b2 := b ⟨2, by decide⟩
  fun i =>
    if i.1 = 0 then (b0 + b1 + b2) - (b0 + b1 + b2)
    else if i.1 = 1 then (b1 + b2 + b0) - (b2 + b0 + b1)
    else (b2 + b0 + b1) - (b1 + b2 + b0)

/-- Refutation of Reading 4:
    (1) On `n = 2`, `youngAltSum2 b` always has coordinate sum `0`, failing trace conservation
        whenever `b_0 + b_1 ≠ 0`;
    (2) On `n = 3`, `youngAltSum3 b = 0` identically for ALL `b`;
    (3) For all `k ∈ Nat`, at `n = 4*k + 4` and `n = 4*k + 5`, the order-reversing permutation
        `w_0` has `n*(n-1)/2` inversions with `(n*(n-1)/2) % 2 = 0` (even permutation!). -/
theorem refute_reading4_perm_antisymmetrization {R : Type u} [LinearOrderedCommRing R] :
    (∀ b : Fin 2 → R, finSum 2 (youngAltSum2 b) = 0) ∧
    (∀ b : Fin 3 → R, ∀ i : Fin 3, youngAltSum3 b i = 0) ∧
    (∀ k : Nat,
      let n1 := 4 * k + 4
      let n2 := 4 * k + 5
      ((n1 * (n1 - 1)) / 2) % 2 = 0 ∧ ((n2 * (n2 - 1)) / 2) % 2 = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b
    simp only [finSum, youngAltSum2]; dsimp
    rw [add_zero_r, sub_eq_add_neg_r, sub_eq_add_neg_r]
    let x := b ⟨0, by decide⟩; let y := b ⟨1, by decide⟩
    change (x + -y) + (y + -x) = 0
    calc (x + -y) + (y + -x)
        = x + (-y + (y + -x)) := add_assoc_r _ _ _
      _ = x + ((-y + y) + -x) := by rw [← add_assoc_r (-y)]
      _ = x + (0 + -x) := by rw [neg_add_cancel_r]
      _ = x + -x := by rw [zero_add_r]
      _ = 0 := add_neg_cancel_r x
  · intro b
    let b0 := b ⟨0, by decide⟩
    let b1 := b ⟨1, by decide⟩
    let b2 := b ⟨2, by decide⟩
    have hcyc : (b1 + b2) + b0 = (b2 + b0) + b1 := by
      rw [add_assoc_r b1 b2 b0, add_comm_r b1 (b2 + b0)]
    apply fin3_all
    · change (b0 + b1 + b2) - (b0 + b1 + b2) = 0; exact sub_self_r _
    · change ((b1 + b2) + b0) - ((b2 + b0) + b1) = 0
      rw [hcyc, sub_self_r]
    · change ((b2 + b0) + b1) - ((b1 + b2) + b0) = 0
      rw [← hcyc, sub_self_r]
  · intro k
    have h1 : (((4 * k + 4) * (4 * k + 3)) / 2) % 2 = 0 := by
      have h4 : 4 * k + 4 = 2 * (2 * (k + 1)) := by omega
      have eq1 : (4 * k + 4) * (4 * k + 3) = 2 * (2 * ((k + 1) * (4 * k + 3))) := by
        rw [h4, Nat.mul_assoc, Nat.mul_assoc]
      rw [eq1, Nat.mul_div_right _ (by decide), Nat.mul_mod_right]
    have h2 : (((4 * k + 5) * (4 * k + 4)) / 2) % 2 = 0 := by
      have h4 : 4 * k + 4 = 2 * (2 * (k + 1)) := by omega
      have eq2 : (4 * k + 5) * (4 * k + 4) = 2 * (2 * ((k + 1) * (4 * k + 5))) := by
        rw [Nat.mul_comm (4 * k + 5) (4 * k + 4), h4, Nat.mul_assoc, Nat.mul_assoc]
      rw [eq2, Nat.mul_div_right _ (by decide), Nat.mul_mod_right]
    exact ⟨h1, h2⟩

end Reading4

-- ----------------------------------------------------------------------------
-- Reading 5: Fiedler Algebraic Connectivity λ_2^↑(L_1 + L_2) on Laplacians
-- ----------------------------------------------------------------------------

section Reading5
variable {F : Type u} [LinearOrderedField F]

def lapK3 : RMat F 3 := fun i j =>
  if i = j then ofNatR F 2 else -(1 : F)

def skewCirc3 (t : F) : RMat F 3 := fun i j =>
  if (i.1 = 0 ∧ j.1 = 1) ∨ (i.1 = 1 ∧ j.1 = 2) ∨ (i.1 = 2 ∧ j.1 = 0) then t
  else if (i.1 = 1 ∧ j.1 = 0) ∨ (i.1 = 2 ∧ j.1 = 1) ∨ (i.1 = 0 ∧ j.1 = 2) then -t
  else 0

/-- Restriction of `2 * lapK3 + skewCirc3 t` to an orthogonal basis of `1^⊥` (`[[6, ...]]`)
    has characteristic polynomial `x^2 - 12 x + (36 + 3 t^2)`, with discriminant `-12 t^2 < 0`. -/
def directedLapSub2 (t : F) : RMat F 2 := fun i j =>
  if i = j then ofNatR F 6
  else if i.1 = 0 then ofNatR F 3 * t
  else -t

/-- Refutation of Reading 5 (Fiedler Algebraic Connectivity):
    (1) `lapK3` is purely symmetric (`skewPart lapK3 = 0`) with zero row sums and achieves exact
        Fiedler connectivity additivity `3 + 3 = 6` on `1^⊥` via `lapK3 + lapK3`;
    (2) Every skew-symmetric circulation `skewCirc3 t` (`t ≠ 0`) has zero row sums, contributes
        `0` to all real Rayleigh quotients, and gives `directedLapSub2 t` strictly negative
        characteristic discriminant `-12 t^2 < 0` (non-real eigenvalues). -/
theorem refute_reading5_laplacian_antisymmetrization {t : F} (ht : t ≠ 0) :
    IsSym (lapK3 : RMat F 3) ∧
    skewPart (lapK3 : RMat F 3) = zeroMat 3 ∧
    matVec (matAdd (lapK3 : RMat F 3) lapK3)
      (fun i => if i.1 = 0 then 1 else if i.1 = 1 then -1 else 0) =
      (fun i => if i.1 = 0 then ofNatR F 6 else if i.1 = 1 then -(ofNatR F 6) else 0) ∧
    IsSkewSym (skewCirc3 t) ∧
    charDisc2 (directedLapSub2 t) < 0 := by
  have hsym : IsSym (lapK3 : RMat F 3) := by
    funext i j; revert i j; apply fin3_all <;> apply fin3_all <;> rfl
  have hskew0 : skewPart (lapK3 : RMat F 3) = zeroMat 3 :=
    (skewPart_eq_zero_iff_isSym _).mpr hsym
  have heig6 : matVec (matAdd (lapK3 : RMat F 3) lapK3)
      (fun i => if i.1 = 0 then (1 : F) else if i.1 = 1 then -1 else 0) =
      (fun i => if i.1 = 0 then ofNatR F 6 else if i.1 = 1 then -(ofNatR F 6) else 0) := by
    funext i; revert i; apply fin3_all
    · unfold matVec matAdd lapK3; simp only [finSum]; dsimp
      simp only [ofNatR, zero_add_r]
      rw [mul_one_r, mul_neg_r, mul_one_r, neg_add_r, neg_neg_r, mul_zero_r, add_zero_r, add_zero_r]
      repeat rw [← add_assoc_r]
    · unfold matVec matAdd lapK3; simp only [finSum]; dsimp
      simp only [ofNatR, zero_add_r]
      rw [mul_one_r, mul_neg_r, mul_one_r, mul_zero_r, add_zero_r, add_zero_r]
      repeat rw [neg_add_r]
      repeat rw [← add_assoc_r]
    · unfold matVec matAdd lapK3; simp only [finSum]; dsimp
      rw [mul_one_r, mul_neg_r, mul_one_r, neg_add_r, neg_neg_r, mul_zero_r, add_zero_r,
          add_zero_r, ← neg_add_r 1 1, neg_add_cancel_r]
  have hskewC : IsSkewSym (skewCirc3 t) := by
    funext i j; revert i j; apply fin3_all <;> apply fin3_all <;> (
      dsimp [transpose, matNeg, skewCirc3]
      try (first | exact neg_zero_r.symm | exact (neg_neg_r t).symm))
  have hdisc : charDisc2 (directedLapSub2 t) < 0 := by
    unfold charDisc2 det2 directedLapSub2
    dsimp
    -- tr = 6 + 6, det = 6 * 6 - (3 * t) * (-t) = 6 * 6 + 3 * (t * t)
    -- (6 + 6)^2 - 4 * (6 * 6 + 3 * t^2) = 0 - 4 * 3 * t^2 < 0!
    have htr2 : (ofNatR F 6 + ofNatR F 6) * (ofNatR F 6 + ofNatR F 6) =
                ((1 + 1) * (1 + 1)) * (ofNatR F 6 * ofNatR F 6) := by
      have h26 : ofNatR F 6 + ofNatR F 6 = (1 + 1) * ofNatR F 6 := by
        rw [right_distrib_r, one_mul_r]
      rw [h26]
      calc ((1 + 1) * ofNatR F 6) * ((1 + 1) * ofNatR F 6)
          = (1 + 1) * (ofNatR F 6 * ((1 + 1) * ofNatR F 6)) := mul_assoc_r _ _ _
        _ = (1 + 1) * ((1 + 1) * (ofNatR F 6 * ofNatR F 6)) := by
              rw [← mul_assoc_r (ofNatR F 6), mul_comm_r (ofNatR F 6) (1 + 1), mul_assoc_r]
        _ = ((1 + 1) * (1 + 1)) * (ofNatR F 6 * ofNatR F 6) := (mul_assoc_r _ _ _).symm
    rw [htr2, mul_neg_r, sub_eq_add_neg_r (ofNatR F 6 * ofNatR F 6), neg_neg_r,
        left_distrib_r ((1 + 1) * (1 + 1)), sub_eq_add_neg_r, neg_add_r, ← add_assoc_r,
        add_neg_cancel_r, zero_add_r]
    -- Goal: -(((1+1)*(1+1)) * ((ofNatR F 3 * t) * t)) < 0
    have hpos4 : (0 : F) < (1 + 1) * (1 + 1) :=
      LinearOrderedCommRing.mul_pos _ _ two_pos_r two_pos_r
    have hpos3t2 : (0 : F) < (ofNatR F 3 * t) * t := by
      rw [mul_assoc_r]
      exact LinearOrderedCommRing.mul_pos _ _ (ofNatR_pos 2) (sq_pos_of_ne_zero_r ht)
    have hprod_pos := LinearOrderedCommRing.mul_pos _ _ hpos4 hpos3t2
    rw [lt_iff_le_not_le_r]
    refine ⟨?_, ?_⟩
    · have hle := le_of_lt_r hprod_pos
      have h' := add_le_add_right_r hle (-(((1 + 1) * (1 + 1)) * ((ofNatR F 3 * t) * t)))
      rwa [add_neg_cancel_r, zero_add_r] at h'
    · intro hge
      have h' := add_le_add_right_r hge (((1 + 1) * (1 + 1)) * ((ofNatR F 3 * t) * t))
      rw [neg_add_cancel_r, zero_add_r] at h'
      exact ((lt_iff_le_not_le_r _ _).mp hprod_pos).2 h'
  exact ⟨hsym, hskew0, heig6, hskewC, hdisc⟩

end Reading5
end AllFiveRefutations

-- ============================================================================
-- §8. Constructive Master Resolution Theorem over QField & Axiom Audit
-- ============================================================================

/-- Complete Formal Resolution of Conjecture `00000007169` over `QField`:
    1. Positive Ordering-Corrected Theorems HOLD:
       - Fiedler's (1971) permutation product bounds and strict uniqueness of `revPerm n`;
       - Full `n x n` Ky Fan additive majorization;
       - Complete `2 x 2` non-commuting Lidskii-Wielandt-Fiedler majorization & determinant bounds.
    2. Antisymmetrization Optimality Claim FAILS across all five canonical readings for `n ≥ 2`. -/
theorem conjecture_00000007169_complete_resolution :
    -- (I) Positive Fiedler permutation bounds & strict reverse-order uniqueness (all n)
    (∀ (n : Nat) (α β : Fin n → QField),
      StrictlyDecreasing α → StrictlyDecreasing β →
      (∀ i, 0 < α i) → (∀ i, 0 < β i) → ∀ p : Perm n,
      finProd n (fun i => α i + β i) ≤ finProd n (fun i => α i + β (p.toFun i)) ∧
      finProd n (fun i => α i + β (p.toFun i)) ≤ finProd n (fun i => α i + β ((revPerm n).toFun i)) ∧
      (finProd n (fun i => α i + β (p.toFun i)) = finProd n (fun i => α i + β ((revPerm n).toFun i)) ↔
        ∀ i, p.toFun i = (revPerm n).toFun i)) ∧
    -- (II) Positive all-n Ky Fan additive majorization
    (∀ (n k : Nat), k ≤ n → ∀ (A B QA QB QAB : RMat QField n) (α β γ : Fin n → QField),
      HasOrthoDiag A α QA → HasOrthoDiag B β QB → HasOrthoDiag (matAdd A B) γ QAB →
      finSum n (fun i => topKIndicator QField n k i * γ i) ≤
        finSum n (fun i => topKIndicator QField n k i * α i) +
        finSum n (fun i => topKIndicator QField n k i * β i) ∧
      finSum n γ = finSum n α + finSum n β) ∧
    -- (III) Refutation of Reading 1 (matrix antisymmetrization, all n = m + 2 ≥ 2)
    (∀ m : Nat,
      trace (skewPart (matAdd (posDiagA (m + 2) : RMat QField (m + 2)) (posDiagBRev (m + 2)))) = 0 ∧
      0 < trace (matAdd (posDiagA (m + 2) : RMat QField (m + 2)) (posDiagBRev (m + 2))) ∧
      det2 (matAdd (nonHermM1 0 : RMat QField 2) (nonHermM2 0)) < ofNatR QField 6 * ofNatR QField 6 ∧
      charDisc2 (hkComplex2 : RMat QField 2) < 0) ∧
    -- (IV) Refutation of Reading 2 (real skew-symmetric & complex skew-Hermitian conjugation)
    ((∀ K : RMat QField 3, IsSkewSym K → det3 K = 0) ∧
      (∀ K : RMat QField 2, IsSkewSym K → IsOrthogonal K →
        det2 (matAdd rotA2Q (matMul K (matMul rotB2Q (transpose K)))) <
          det2 (matAdd rotA2Q (matMul symReflectQ2 (matMul rotB2Q (transpose symReflectQ2))))) ∧
      (∀ U : CMat QField 3, IsSkewHermitian U → IsUnitary U →
        cMatAdd cycleA3 (cMatMul U (cMatMul cycleB3 (cAdj U))) ≠ cDiag (fun _ => ofNatR QField 4))) ∧
    -- (V) Refutation of Reading 3 (Lie commutator), Reading 4 (Young Alt & w_0 parity), Reading 5 (Laplacian)
    ((commutator (blochA (1 : QField)) (blochB 1 (-1) 0) = zeroMat 2 ∧
      0 < frobNormSq (commutator (blochA (1 : QField)) (blochB 1 0 1))) ∧
     ((∀ b : Fin 3 → QField, ∀ i : Fin 3, youngAltSum3 b i = 0) ∧
      (((4 * 4 - 4) / 2) % 2 = 0)) ∧
     (skewPart (lapK3 : RMat QField 3) = zeroMat 3 ∧
      charDisc2 (directedLapSub2 (1 : QField)) < 0)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n α β hα hβ hαp hβp p
    have hb := fiedler_perm_prod_bounds_all_n n α β
      (nonIncreasing_of_strictlyDecreasing hα) (nonIncreasing_of_strictlyDecreasing hβ)
      (fun i => le_of_lt_r (hαp i)) (fun i => le_of_lt_r (hβp i)) p
    exact ⟨hb.1, hb.2, fiedler_perm_prod_eq_max_iff_revPerm n α β hα hβ hαp hβp p⟩
  · intro n k hk A B QA QB QAB α β γ hA hB hAB
    exact ky_fan_additive_majorization_all_n n k hk hA hB hAB
  · intro m
    have r1 := refute_reading1_matrix_antisymmetrization (F := QField) m
    exact ⟨r1.2.1.2.1, r1.2.1.2.2, r1.2.2.2.2.2.1, r1.2.2.2.2.2.2⟩
  · refine ⟨fun _ hK => det3_eq_zero_of_isSkewSym hK,
            fun K hKs hKo => (refute_reading2_real_skew_conj_2x2.2.2.2 K hKs hKo).2,
            refute_reading2_complex_skewHermitian_3cycle.2.2⟩
  · have h1pos : (0 : QField) < 1 := LinearOrderedCommRing.zero_lt_one
    have r3 := refute_reading3_commutator_antisymmetrization h1pos h1pos
    have r4 := refute_reading4_perm_antisymmetrization (R := QField)
    have h1ne : (1 : QField) ≠ 0 := (ne_of_lt_r h1pos).symm
    have r5 := refute_reading5_laplacian_antisymmetrization h1ne
    exact ⟨⟨r3.2.1, r3.2.2.1⟩, ⟨r4.2.1, by decide⟩, ⟨r5.2.1, r5.2.2.2.2⟩⟩

end Conjecture00000007169

-- ============================================================================
-- Axiom Verification (Standard Lean 4 Core Foundations Only)
-- ============================================================================

#print axioms Conjecture00000007169.rearrangement_bounds_all_n
#print axioms Conjecture00000007169.fiedler_perm_prod_bounds_all_n
#print axioms Conjecture00000007169.fiedler_perm_prod_eq_max_iff_revPerm
#print axioms Conjecture00000007169.ky_fan_additive_majorization_all_n
#print axioms Conjecture00000007169.lidskii_wielandt_fiedler_2x2
#print axioms Conjecture00000007169.quadForm_eq_symPart
#print axioms Conjecture00000007169.refute_reading1_matrix_antisymmetrization
#print axioms Conjecture00000007169.refute_reading2_real_skew_conj_2x2
#print axioms Conjecture00000007169.refute_reading2_complex_skewHermitian_3cycle
#print axioms Conjecture00000007169.refute_reading3_commutator_antisymmetrization
#print axioms Conjecture00000007169.refute_reading4_perm_antisymmetrization
#print axioms Conjecture00000007169.refute_reading5_laplacian_antisymmetrization
#print axioms Conjecture00000007169.conjecture_00000007169_complete_resolution
