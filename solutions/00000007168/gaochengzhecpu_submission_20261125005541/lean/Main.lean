/-
Conjecture 00000007168 — Complete Formal Analysis and Refutation in Core Lean 4.19.0
====================================================================================

Source statement (`SOURCE.md`):
  English: "Definition: Schur's inequality with the spectral bounds of power sums.
            Conjecture: The upper bound of power sums is the sum of spectral-radius
            powers, and the realization of the bound is the normal matrix.
            (normal-realized Schur power-sum bound)"
  Chinese: "定义：Schur 不等式：幂和的谱界。猜想：Schur 幂和的极值：幂和的上界为谱半径幂的和
            且界的实现为正规矩阵。（Schur 正常谱半径幂和上界极值）"

Mathematical Summary of Formalized Results (zero external dependencies, zero sorry):
  1. Ordered Algebraic & Complex Matrix Foundations (§1–§4):
     - Polymorphic development over any `LinearOrderedCommRing R` (covering Z, Q, R)
       and `LinearOrderedField F` (covering Q, R), together with their Cayley-Dickson
       complexification `Complex R` (covering Z[i], Q(i), C), plus constructive
       verified instances `LinearOrderedCommRing Int` and `LinearOrderedField QField`
       (exact rational numbers Q built via Quotient, proving non-vacuity).
     - Full n x n matrix algebra `CMat R n` and `RMat R n` (`mul`, `matPow`, `adj`,
       `transpose`, `trace`, `frobNormSq`, `IsNormal`, `IsRealNormal`, `IsUnitary`,
       `IsUpperTriangular`, `IsDiagonal`, `HasSchurDecomp`), including equivalence
       `isRealNormal_iff_isNormal_toComplex` between M_n(R) and M_n(C).
  2. Positive Benchmark Theorems (§5–§6):
     - Classical n x n Schur's Inequality & Normality Characterization:
       For every Schur-triangularizable A = U T U* in M_n(Complex R),
         ∑_i |λ_i|^2 ≤ ‖A‖_F^2   and   (∑_i |λ_i|^2 = ‖A‖_F^2 ↔ IsNormal A).
     - True Eigenvalue & Trace Power-Sum Spectral-Radius Bounds (all n, all k ≥ 1):
         ∑_i r_i^k ≤ n ρ^k       with equality ↔ ∀ i, r_i = ρ (equal-modulus spectrum),
         |tr(A^k)|^2 ≤ n^2 (ρ^2)^k  (via n-variable complex Lagrange/Cauchy-Schwarz).
     - Normal-Matrix Frobenius Power Bound:
       If IsNormal A, then ‖A^k‖_F^2 ≤ n (ρ^2)^k, with equality (k ≥ 1) ↔ ∀ i, |λ_i|^2 = ρ^2.
  3. Complete Refutations Across All Readings for ALL n = m + 2 ≥ 2 and k ≥ 1 (§7–§8):
     - Reading 1 (Eigenvalue modulus power sums ∑_i |λ_i|^k ≤ n ρ(A)^k and trace power
       sums |tr(A^k)| ≤ n ρ(A)^k):
       * Necessity FAILS: J_n = I_n + E_{0,1} attains BOTH bounds (n = n ρ^k) for all
         k ≥ 1 (and all multi-exponent sums), yet ¬ IsNormal J_n (and ¬ IsRealNormal).
         Over QField, the dense non-triangular unitary conjugate U J_2 U* (with exact
         Pythagorean unitary U = (1/5)[[3,-4],[4,3]]) also attains the bound while non-normal.
       * Sufficiency FAILS: D_n = diag(1, 0, ..., 0) satisfies IsNormal D_n (and Schur
         equality 1 = 1), yet strictly fails equality (1 < n = n ρ^k) for all k ≥ 1.
     - Reading 2 (Frobenius / singular-value / Schatten power sums ‖A^k‖_F^2 ≤ n ρ(A)^{2k}
       or tr((A* A)^k) ≤ n ρ(A)^{2k}):
       * Upper bound ITSELF FAILS: N_{n,c} = c E_{0,1} (c ≠ 0) has ρ = 0 while
         ‖N_{n,c}‖_F^2 = |c|^2 > 0 and tr((N* N)^k) = |c|^{2k} > 0 for all k ≥ 1;
         moreover J_n has ρ = 1 while ‖J_n^k‖_F^2 = n + k^2 > n for all k ≥ 1.
     - Reading 3 (Multi-exponent and unscaled spectral-radius sums):
       * Scaled multi-exponent sums ∑_{k=1}^K P_k(A) ≤ ∑_{k=1}^K n ρ(A)^k: refuted in
         both directions of normality by J_n and D_n.
       * Unscaled sums ρ(A)^k or ∑_{k=1}^K ρ(A)^k (without factor n): upper bound fails
         immediately on the normal identity matrix I_n (n > 1, K n > K).
-/

universe u

namespace Conjecture00000007168

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
        rw [← Int.mul_assoc r.num p.den q.den, Int.mul_assoc r.num p.den q.den,
            ← Int.mul_assoc r.num p.den q.den]
        calc r.num * p.den * q.den
            = r.num * (p.den * q.den) := Int.mul_assoc _ _ _
          _ = r.num * (q.den * p.den) := by rw [Int.mul_comm p.den q.den]
          _ = (r.num * q.den) * p.den := (Int.mul_assoc _ _ _).symm
      have h2' : r.num * (p.den * q.den) = (r.num * q.den) * p.den := by
        rw [Int.mul_comm p.den q.den, ← Int.mul_assoc]
      rw [h1, h2', Int.add_assoc]
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
    mk n1 d1 hd1 = mk n2 d2 hd2 ↔ n1 * d2 = n2 * d1 := by
  constructor
  · intro h; exact Quotient.exact h
  · intro h; exact Quotient.sound h

theorem mk_add {n1 d1 n2 d2 : Int} (hd1 : 0 < d1) (hd2 : 0 < d2) :
    mk n1 d1 hd1 + mk n2 d2 hd2 = mk (n1 * d2 + n2 * d1) (d1 * d2) (Int.mul_pos hd1 hd2) := rfl

theorem mk_mul {n1 d1 n2 d2 : Int} (hd1 : 0 < d1) (hd2 : 0 < d2) :
    mk n1 d1 hd1 * mk n2 d2 hd2 = mk (n1 * n2) (d1 * d2) (Int.mul_pos hd1 hd2) := rfl

theorem mk_neg {n d : Int} (hd : 0 < d) :
    -mk n d hd = mk (-n) d hd := rfl

end QField

-- ============================================================================
-- §2. General Lemmas for LinearOrderedCommRing
-- ============================================================================

namespace RingLemmas

variable {R : Type u} [LinearOrderedCommRing R]

theorem add_assoc (a b c : R) : a + b + c = a + (b + c) := LinearOrderedCommRing.add_assoc a b c
theorem add_comm (a b : R) : a + b = b + a := LinearOrderedCommRing.add_comm a b
theorem zero_add (a : R) : 0 + a = a := LinearOrderedCommRing.zero_add a
theorem add_zero (a : R) : a + 0 = a := LinearOrderedCommRing.add_zero a
theorem neg_add_cancel (a : R) : -a + a = 0 := LinearOrderedCommRing.neg_add_cancel a
theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]
theorem sub_eq_add_neg (a b : R) : a - b = a + -b := LinearOrderedCommRing.sub_eq_add_neg a b
theorem mul_assoc (a b c : R) : a * b * c = a * (b * c) := LinearOrderedCommRing.mul_assoc a b c
theorem mul_comm (a b : R) : a * b = b * a := LinearOrderedCommRing.mul_comm a b
theorem one_mul (a : R) : 1 * a = a := LinearOrderedCommRing.one_mul a
theorem mul_one (a : R) : a * 1 = a := LinearOrderedCommRing.mul_one a
theorem left_distrib (a b c : R) : a * (b + c) = a * b + a * c := LinearOrderedCommRing.left_distrib a b c
theorem right_distrib (a b c : R) : (a + b) * c = a * c + b * c := LinearOrderedCommRing.right_distrib a b c
theorem le_refl (a : R) : a ≤ a := LinearOrderedCommRing.le_refl a
theorem le_trans {a b c : R} : a ≤ b → b ≤ c → a ≤ c := LinearOrderedCommRing.le_trans a b c
theorem le_antisymm {a b : R} : a ≤ b → b ≤ a → a = b := LinearOrderedCommRing.le_antisymm a b
theorem le_total (a b : R) : a ≤ b ∨ b ≤ a := LinearOrderedCommRing.le_total a b
theorem lt_iff_le_not_le {a b : R} : a < b ↔ a ≤ b ∧ ¬ b ≤ a := LinearOrderedCommRing.lt_iff_le_not_le a b

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  calc b = 0 + b := (zero_add b).symm
    _ = (-a + a) + b := by rw [neg_add_cancel]
    _ = -a + (a + b) := add_assoc _ _ _
    _ = -a + (a + c) := by rw [h]
    _ = (-a + a) + c := (add_assoc _ _ _).symm
    _ = 0 + c := by rw [neg_add_cancel]
    _ = c := zero_add c

theorem add_right_cancel {a b c : R} (h : b + a = c + a) : b = c := by
  apply add_left_cancel (a := a)
  rw [add_comm a b, h, add_comm c a]

theorem mul_zero (a : R) : a * 0 = 0 := by
  apply add_left_cancel (a := a * 0)
  rw [← left_distrib, add_zero, add_zero]

theorem zero_mul (a : R) : 0 * a = 0 := by rw [mul_comm, mul_zero]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  apply add_right_cancel (a := a)
  rw [neg_add_cancel, add_comm b a, h]

theorem neg_zero : -(0 : R) = 0 := neg_eq_of_add_eq_zero (add_zero 0)

theorem neg_neg (a : R) : -(-a) = a := neg_eq_of_add_eq_zero (neg_add_cancel a)

theorem neg_add (a b : R) : -(a + b) = -a + -b := by
  apply neg_eq_of_add_eq_zero
  calc (a + b) + (-a + -b)
      = a + (b + (-b + -a)) := by rw [add_comm (-a) (-b), add_assoc]
    _ = a + ((b + -b) + -a) := by rw [add_assoc b (-b) (-a)]
    _ = a + (0 + -a) := by rw [add_neg_cancel]
    _ = a + -a := by rw [zero_add]
    _ = 0 := add_neg_cancel a

theorem mul_neg (a b : R) : a * (-b) = -(a * b) := by
  symm; apply neg_eq_of_add_eq_zero
  rw [← left_distrib, add_neg_cancel, mul_zero]

theorem neg_mul (a b : R) : (-a) * b = -(a * b) := by
  rw [mul_comm, mul_neg, mul_comm]

theorem neg_mul_neg (a b : R) : (-a) * (-b) = a * b := by
  rw [neg_mul, mul_neg, neg_neg]

theorem mul_sub (a b c : R) : a * (b - c) = a * b - a * c := by
  rw [sub_eq_add_neg, left_distrib, mul_neg, ← sub_eq_add_neg]

theorem sub_mul (a b c : R) : (a - b) * c = a * c - b * c := by
  rw [sub_eq_add_neg, right_distrib, neg_mul, ← sub_eq_add_neg]

theorem sub_self (a : R) : a - a = 0 := by rw [sub_eq_add_neg, add_neg_cancel]
theorem sub_zero (a : R) : a - 0 = a := by rw [sub_eq_add_neg, neg_zero, add_zero]

theorem lt_irrefl (a : R) : ¬ (a < a) := by
  rw [lt_iff_le_not_le]; intro ⟨h1, h2⟩; exact h2 h1

theorem ne_of_lt {a b : R} (h : a < b) : a ≠ b := by
  intro heq; rw [heq] at h; exact lt_irrefl b h

theorem le_of_lt {a b : R} (h : a < b) : a ≤ b := (lt_iff_le_not_le.mp h).1

theorem lt_of_le_of_ne {a b : R} (hle : a ≤ b) (hne : a ≠ b) : a < b := by
  rw [lt_iff_le_not_le]; refine ⟨hle, fun hba => hne (le_antisymm hle hba)⟩

theorem lt_of_lt_of_le {a b c : R} (hab : a < b) (hbc : b ≤ c) : a < c := by
  rw [lt_iff_le_not_le] at hab ⊢
  refine ⟨le_trans hab.1 hbc, fun hca => hab.2 (le_trans hbc hca)⟩

theorem lt_of_le_of_lt {a b c : R} (hab : a ≤ b) (hbc : b < c) : a < c := by
  rw [lt_iff_le_not_le] at hbc ⊢
  refine ⟨le_trans hab hbc.1, fun hca => hbc.2 (le_trans hca hab)⟩

theorem lt_trans {a b c : R} (hab : a < b) (hbc : b < c) : a < c :=
  lt_of_lt_of_le hab (le_of_lt hbc)

theorem add_le_add_right {a b : R} (h : a ≤ b) (c : R) : a + c ≤ b + c := by
  rw [add_comm a c, add_comm b c]
  exact LinearOrderedCommRing.add_le_add_left a b h c

theorem add_le_add {a b c d : R} (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d :=
  le_trans (add_le_add_right hab c) (LinearOrderedCommRing.add_le_add_left c d hcd b)

theorem add_lt_add_left {a b : R} (h : a < b) (c : R) : c + a < c + b := by
  rw [lt_iff_le_not_le] at h ⊢
  refine ⟨LinearOrderedCommRing.add_le_add_left a b h.1 c, fun hle => h.2 ?_⟩
  have := LinearOrderedCommRing.add_le_add_left (c + b) (c + a) hle (-c)
  rw [← add_assoc, ← add_assoc, neg_add_cancel, zero_add, zero_add] at this
  exact this

theorem add_lt_add_of_le_of_lt {a b c d : R} (hab : a ≤ b) (hcd : c < d) : a + c < b + d :=
  lt_of_le_of_lt (add_le_add_right hab c) (add_lt_add_left hcd b)

theorem add_lt_add_of_lt_of_le {a b c d : R} (hab : a < b) (hcd : c ≤ d) : a + c < b + d := by
  rw [add_comm a c, add_comm b d]
  exact add_lt_add_of_le_of_lt hcd hab

theorem add_nonneg {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  have := add_le_add ha hb; rw [add_zero] at this; exact this

theorem add_pos {a b : R} (ha : 0 < a) (hb : 0 < b) : 0 < a + b := by
  have := add_lt_add_of_lt_of_le ha (le_of_lt hb); rw [add_zero] at this; exact this

theorem sub_nonneg {a b : R} : 0 ≤ b - a ↔ a ≤ b := by
  constructor
  · intro h
    have := add_le_add_right h a
    rw [ zero_add, sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero ] at this
    exact this
  · intro h
    have := add_le_add_right h (-a)
    rw [ add_neg_cancel, ← sub_eq_add_neg ] at this
    exact this

theorem sub_eq_zero {a b : R} : a - b = 0 ↔ a = b := by
  constructor
  · intro h
    apply le_antisymm
    · rw [← sub_nonneg]; have : b - a = -(a - b) := by
        rw [sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_neg, add_comm]
      rw [this, h, neg_zero]; exact le_refl 0
    · rw [← sub_nonneg, h]; exact le_refl 0
  · intro h; rw [h, sub_self]

theorem neg_nonneg_of_nonpos {a : R} (h : a ≤ 0) : 0 ≤ -a := by
  have := sub_nonneg.mpr h
  rw [sub_eq_add_neg, zero_add] at this
  exact this

theorem neg_pos_of_neg {a : R} (h : a < 0) : 0 < -a := by
  have := add_lt_add_left h (-a)
  rw [neg_add_cancel, add_zero] at this
  exact this

theorem sq_nonneg (a : R) : 0 ≤ a * a := by
  cases le_total 0 a with
  | inl ha => exact LinearOrderedCommRing.mul_nonneg a a ha ha
  | inr ha =>
    have hna := neg_nonneg_of_nonpos ha
    have := LinearOrderedCommRing.mul_nonneg (-a) (-a) hna hna
    rw [neg_mul_neg] at this
    exact this

theorem sq_pos_of_ne_zero {a : R} (ha : a ≠ 0) : 0 < a * a := by
  cases le_total 0 a with
  | inl hge =>
    have hpos : 0 < a := lt_of_le_of_ne hge ha.symm
    exact LinearOrderedCommRing.mul_pos a a hpos hpos
  | inr hle =>
    have hlt : a < 0 := lt_of_le_of_ne hle ha
    have hpos : 0 < -a := neg_pos_of_neg hlt
    have := LinearOrderedCommRing.mul_pos (-a) (-a) hpos hpos
    rw [neg_mul_neg] at this
    exact this

theorem sq_eq_zero_iff (a : R) : a * a = 0 ↔ a = 0 := by
  constructor
  · intro h
    by_cases ha : a = 0
    · exact ha
    · exfalso; exact ne_of_lt (sq_pos_of_ne_zero ha) h.symm
  · intro h; rw [h, zero_mul]

theorem add_eq_zero_iff_of_nonneg {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a + b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have ha0 : a ≤ 0 := by
      have := LinearOrderedCommRing.add_le_add_left 0 b hb a
      rw [add_zero, h] at this; exact this
    have eq_a : a = 0 := le_antisymm ha0 ha
    rw [eq_a, zero_add] at h
    exact ⟨eq_a, h⟩
  · rintro ⟨rfl, rfl⟩; exact add_zero 0

theorem two_pos : (0 : R) < 1 + 1 :=
  add_pos LinearOrderedCommRing.zero_lt_one LinearOrderedCommRing.zero_lt_one

theorem mul_two_nonneg_iff {x : R} : 0 ≤ (1 + 1 : R) * x ↔ 0 ≤ x := by
  constructor
  · intro h
    cases le_total 0 x with
    | inl hx => exact hx
    | inr hx =>
      by_cases hz : x = 0
      · rw [hz]; exact le_refl 0
      · exfalso
        have hnx : 0 < -x := neg_pos_of_neg (lt_of_le_of_ne hx hz)
        have hp : 0 < (1 + 1 : R) * (-x) := LinearOrderedCommRing.mul_pos _ _ two_pos hnx
        rw [mul_neg] at hp
        have hsum := add_lt_add_of_le_of_lt h hp
        rw [add_zero, add_neg_cancel] at hsum
        exact lt_irrefl 0 hsum
  · intro hx
    exact LinearOrderedCommRing.mul_nonneg _ _ (le_of_lt two_pos) hx

theorem mul_two_eq_zero_iff {x : R} : (1 + 1 : R) * x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply le_antisymm
    · have : 0 ≤ (1 + 1 : R) * (-x) := by rw [mul_neg, h, neg_zero]; exact le_refl 0
      have hnx := mul_two_nonneg_iff.mp this
      have := add_le_add_right hnx x
      rw [zero_add, neg_add_cancel] at this; exact this
    · have : 0 ≤ (1 + 1 : R) * x := by rw [h]; exact le_refl 0
      exact mul_two_nonneg_iff.mp this
  · intro h; rw [h, mul_zero]

/-- Natural-exponent power in `R`. -/
def rpow (a : R) : Nat → R
  | 0 => 1
  | k + 1 => rpow a k * a

theorem rpow_zero (a : R) : rpow a 0 = 1 := rfl
theorem rpow_succ (a : R) (k : Nat) : rpow a (k + 1) = rpow a k * a := rfl

theorem rpow_one_base : ∀ k : Nat, rpow (1 : R) k = 1
  | 0 => rfl
  | k + 1 => by rw [rpow_succ, rpow_one_base k, mul_one]

theorem rpow_zero_base : ∀ {k : Nat}, 1 ≤ k → rpow (0 : R) k = 0
  | 0, h => by omega
  | _ + 1, _ => by rw [rpow_succ, mul_zero]

theorem rpow_nonneg {a : R} (ha : 0 ≤ a) : ∀ k : Nat, 0 ≤ rpow a k
  | 0 => le_of_lt LinearOrderedCommRing.zero_lt_one
  | k + 1 => LinearOrderedCommRing.mul_nonneg _ _ (rpow_nonneg ha k) ha

theorem rpow_pos {a : R} (ha : 0 < a) : ∀ k : Nat, 0 < rpow a k
  | 0 => LinearOrderedCommRing.zero_lt_one
  | k + 1 => LinearOrderedCommRing.mul_pos _ _ (rpow_pos ha k) ha

theorem mul_le_mul_of_nonneg_right {a b c : R} (hab : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  rw [← sub_nonneg, ← sub_mul]
  exact LinearOrderedCommRing.mul_nonneg _ _ (sub_nonneg.mpr hab) hc

theorem mul_le_mul_of_nonneg_left {a b c : R} (hab : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by
  rw [mul_comm c a, mul_comm c b]
  exact mul_le_mul_of_nonneg_right hab hc

theorem mul_lt_mul_of_pos_right {a b c : R} (hab : a < b) (hc : 0 < c) : a * c < b * c := by
  have hpos : 0 < (b - a) * c := by
    have hba : 0 < b - a := by
      exact lt_of_le_of_ne (sub_nonneg.mpr (le_of_lt hab))
        (fun h0 => ne_of_lt hab (sub_eq_zero.mp h0.symm).symm)
    exact LinearOrderedCommRing.mul_pos _ _ hba hc
  rw [sub_mul] at hpos
  have := add_lt_add_left hpos (a * c)
  rw [add_zero, sub_eq_add_neg, add_comm (b * c), ← add_assoc, add_neg_cancel, zero_add] at this
  exact this

theorem rpow_le_rpow {a b : R} (ha : 0 ≤ a) (hab : a ≤ b) : ∀ k : Nat, rpow a k ≤ rpow b k
  | 0 => le_refl 1
  | k + 1 =>
    have hb : 0 ≤ b := le_trans ha hab
    le_trans (mul_le_mul_of_nonneg_right (rpow_le_rpow ha hab k) ha)
             (mul_le_mul_of_nonneg_left hab (rpow_nonneg hb k))

theorem rpow_lt_rpow {a b : R} (ha : 0 ≤ a) (hab : a < b) :
    ∀ {k : Nat}, 1 ≤ k → rpow a k < rpow b k
  | 0, hk => by omega
  | 1, _ => by rw [rpow_succ, rpow_zero, one_mul, rpow_succ, rpow_zero, one_mul]; exact hab
  | k + 2, _ => by
    have hb_pos : 0 < b := lt_of_le_of_lt ha hab
    have ih : rpow a (k + 1) < rpow b (k + 1) := rpow_lt_rpow ha hab (by omega)
    rw [rpow_succ a (k + 1), rpow_succ b (k + 1)]
    have step1 : rpow a (k + 1) * a ≤ rpow a (k + 1) * b :=
      mul_le_mul_of_nonneg_left (le_of_lt hab) (rpow_nonneg ha (k + 1))
    have step2 : rpow a (k + 1) * b < rpow b (k + 1) * b :=
      mul_lt_mul_of_pos_right ih hb_pos
    exact lt_of_le_of_lt step1 step2

theorem rpow_eq_iff {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) {k : Nat} (hk : 1 ≤ k) :
    rpow a k = rpow b k ↔ a = b := by
  constructor
  · intro heq
    cases le_total a b with
    | inl hab =>
      by_cases h : a = b
      · exact h
      · exfalso; exact ne_of_lt (rpow_lt_rpow ha (lt_of_le_of_ne hab h) hk) heq
    | inr hba =>
      by_cases h : b = a
      · exact h.symm
      · exfalso; exact ne_of_lt (rpow_lt_rpow hb (lt_of_le_of_ne hba h) hk) heq.symm
  · intro h; rw [h]

/-- Embed `Nat` into `R` by repeated addition of `1`. -/
def natCast (R : Type u) [LinearOrderedCommRing R] : Nat → R
  | 0 => 0
  | n + 1 => natCast R n + 1

theorem natCast_nonneg : ∀ n : Nat, 0 ≤ natCast R n
  | 0 => le_refl 0
  | n + 1 => add_nonneg (natCast_nonneg n) (le_of_lt LinearOrderedCommRing.zero_lt_one)

theorem natCast_pos {n : Nat} (hn : 1 ≤ n) : 0 < natCast R n := by
  cases n with
  | zero => omega
  | succ m =>
    have h := add_lt_add_of_le_of_lt (natCast_nonneg (R := R) m) LinearOrderedCommRing.zero_lt_one
    rw [add_zero] at h
    exact h

theorem one_lt_natCast_succ_succ (m : Nat) : (1 : R) < natCast R (m + 2) := by
  unfold natCast
  have hpos : (0 : R) < natCast R m + 1 :=
    let h := add_lt_add_of_le_of_lt (natCast_nonneg (R := R) m) LinearOrderedCommRing.zero_lt_one
    by rw [add_zero] at h; exact h
  have := add_lt_add_of_lt_of_le hpos (le_refl (1 : R))
  rw [zero_add] at this
  exact this

end RingLemmas

-- ============================================================================
-- §3. Complex Extension `Complex R` (R[i], covering C = Complex R and Q(i))
-- ============================================================================

structure Complex (R : Type u) where
  re : R
  im : R
  deriving DecidableEq

namespace Complex

open RingLemmas

theorem ext {R : Type u} {z w : Complex R} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z; cases w; simp at hre him; subst hre; subst him; rfl

section RingOps
variable {R : Type u} [LinearOrderedCommRing R]

instance : OfNat (Complex R) (nat_lit 0) where ofNat := ⟨0, 0⟩
instance : OfNat (Complex R) (nat_lit 1) where ofNat := ⟨1, 0⟩
instance : Add (Complex R) where add z w := ⟨z.re + w.re, z.im + w.im⟩
instance : Neg (Complex R) where neg z := ⟨-z.re, -z.im⟩
instance : Sub (Complex R) where sub z w := ⟨z.re - w.re, z.im - w.im⟩
instance : Mul (Complex R) where
  mul z w := ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

def ofReal (x : R) : Complex R := ⟨x, 0⟩
def I : Complex R := ⟨0, 1⟩
def conj (z : Complex R) : Complex R := ⟨z.re, -z.im⟩
def normSq (z : Complex R) : R := z.re * z.re + z.im * z.im

def cpow (z : Complex R) : Nat → Complex R
  | 0 => 1
  | k + 1 => cpow z k * z

@[simp] theorem zero_re : (0 : Complex R).re = 0 := rfl
@[simp] theorem zero_im : (0 : Complex R).im = 0 := rfl
@[simp] theorem one_re  : (1 : Complex R).re = 1 := rfl
@[simp] theorem one_im  : (1 : Complex R).im = 0 := rfl
@[simp] theorem add_re (z w : Complex R) : (z + w).re = z.re + w.re := rfl
@[simp] theorem add_im (z w : Complex R) : (z + w).im = z.im + w.im := rfl
@[simp] theorem neg_re (z : Complex R) : (-z).re = -z.re := rfl
@[simp] theorem neg_im (z : Complex R) : (-z).im = -z.im := rfl
@[simp] theorem sub_re (z w : Complex R) : (z - w).re = z.re - w.re := rfl
@[simp] theorem sub_im (z w : Complex R) : (z - w).im = z.im - w.im := rfl
@[simp] theorem mul_re (z w : Complex R) : (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] theorem mul_im (z w : Complex R) : (z * w).im = z.re * w.im + z.im * w.re := rfl
@[simp] theorem ofReal_re (x : R) : (ofReal x).re = x := rfl
@[simp] theorem ofReal_im (x : R) : (ofReal x).im = 0 := rfl
@[simp] theorem conj_re (z : Complex R) : (conj z).re = z.re := rfl
@[simp] theorem conj_im (z : Complex R) : (conj z).im = -z.im := rfl

theorem cadd_assoc (a b c : Complex R) : a + b + c = a + (b + c) :=
  ext (add_assoc _ _ _) (add_assoc _ _ _)
theorem cadd_comm (a b : Complex R) : a + b = b + a :=
  ext (add_comm _ _) (add_comm _ _)
theorem czero_add (a : Complex R) : 0 + a = a :=
  ext (zero_add _) (zero_add _)
theorem cadd_zero (a : Complex R) : a + 0 = a :=
  ext (add_zero _) (add_zero _)
theorem cone_mul (a : Complex R) : 1 * a = a := by
  apply ext
  · dsimp; rw [one_mul, zero_mul, sub_zero]
  · dsimp; rw [one_mul, zero_mul, add_zero]
theorem cmul_one (a : Complex R) : a * 1 = a := by
  apply ext
  · dsimp; rw [mul_one, mul_zero, sub_zero]
  · dsimp; rw [mul_zero, mul_one, zero_add]
theorem czero_mul (a : Complex R) : 0 * a = 0 := by
  apply ext <;> (dsimp; rw [zero_mul, zero_mul])
  · exact sub_self 0
  · exact add_zero 0
theorem cmul_zero (a : Complex R) : a * 0 = 0 := by
  apply ext <;> (dsimp; rw [mul_zero, mul_zero])
  · exact sub_self 0
  · exact add_zero 0
theorem cmul_comm (a b : Complex R) : a * b = b * a := by
  apply ext
  · dsimp; rw [mul_comm a.re, mul_comm a.im]
  · dsimp; rw [mul_comm a.re, mul_comm a.im, add_comm]

theorem cleft_distrib (a b c : Complex R) : a * (b + c) = a * b + a * c := by
  apply ext
  · dsimp
    rw [left_distrib, left_distrib, sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add]
    calc a.re * b.re + a.re * c.re + (-(a.im * b.im) + -(a.im * c.im))
        = a.re * b.re + (a.re * c.re + (-(a.im * b.im) + -(a.im * c.im))) := add_assoc _ _ _
      _ = a.re * b.re + (-(a.im * b.im) + (a.re * c.re + -(a.im * c.im))) := by
            rw [← add_assoc (a.re * c.re), add_comm (a.re * c.re) (-(a.im * b.im)), add_assoc]
      _ = (a.re * b.re + -(a.im * b.im)) + (a.re * c.re + -(a.im * c.im)) := (add_assoc _ _ _).symm
  · dsimp
    rw [left_distrib, left_distrib]
    calc a.re * b.im + a.re * c.im + (a.im * b.re + a.im * c.re)
        = a.re * b.im + (a.re * c.im + (a.im * b.re + a.im * c.re)) := add_assoc _ _ _
      _ = a.re * b.im + (a.im * b.re + (a.re * c.im + a.im * c.re)) := by
            rw [← add_assoc (a.re * c.im), add_comm (a.re * c.im) (a.im * b.re), add_assoc]
      _ = (a.re * b.im + a.im * b.re) + (a.re * c.im + a.im * c.re) := (add_assoc _ _ _).symm

theorem cright_distrib (a b c : Complex R) : (a + b) * c = a * c + b * c := by
  rw [cmul_comm (a + b) c, cleft_distrib, cmul_comm c a, cmul_comm c b]

theorem cmul_assoc (a b c : Complex R) : a * b * c = a * (b * c) := by
  apply ext
  · dsimp
    rw [sub_mul, right_distrib, mul_sub, left_distrib,
        mul_assoc, mul_assoc, mul_assoc, mul_assoc,
        sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg,
        neg_add, neg_add]
    calc a.re * (b.re * c.re) + -(a.im * (b.im * c.re)) +
            (-(a.re * (b.im * c.im)) + -(a.im * (b.re * c.im)))
        = a.re * (b.re * c.re) + (-(a.im * (b.im * c.re)) +
            (-(a.re * (b.im * c.im)) + -(a.im * (b.re * c.im)))) := add_assoc _ _ _
      _ = a.re * (b.re * c.re) + (-(a.re * (b.im * c.im)) +
            (-(a.im * (b.im * c.re)) + -(a.im * (b.re * c.im)))) := by
            rw [← add_assoc (-(a.im * (b.im * c.re))),
                add_comm (-(a.im * (b.im * c.re))) (-(a.re * (b.im * c.im))), add_assoc]
      _ = a.re * (b.re * c.re) + -(a.re * (b.im * c.im)) +
            (-(a.im * (b.re * c.im)) + -(a.im * (b.im * c.re))) := by
            rw [add_comm (-(a.im * (b.im * c.re))) (-(a.im * (b.re * c.im))), ← add_assoc]
  · dsimp
    rw [sub_mul, right_distrib, left_distrib, mul_sub,
        mul_assoc, mul_assoc, mul_assoc, mul_assoc,
        sub_eq_add_neg, sub_eq_add_neg]
    calc a.re * (b.re * c.im) + -(a.im * (b.im * c.im)) +
            (a.re * (b.im * c.re) + a.im * (b.re * c.re))
        = a.re * (b.re * c.im) + (-(a.im * (b.im * c.im)) +
            (a.re * (b.im * c.re) + a.im * (b.re * c.re))) := add_assoc _ _ _
      _ = a.re * (b.re * c.im) + (a.re * (b.im * c.re) +
            (-(a.im * (b.im * c.im)) + a.im * (b.re * c.re))) := by
            rw [← add_assoc (-(a.im * (b.im * c.im))),
                add_comm (-(a.im * (b.im * c.im))) (a.re * (b.im * c.re)), add_assoc]
      _ = a.re * (b.re * c.im) + a.re * (b.im * c.re) +
            (a.im * (b.re * c.re) + -(a.im * (b.im * c.im))) := by
            rw [add_comm (-(a.im * (b.im * c.im))), ← add_assoc]

theorem ofReal_zero : ofReal (0 : R) = 0 := rfl
theorem ofReal_one  : ofReal (1 : R) = 1 := rfl
theorem ofReal_add (x y : R) : ofReal (x + y) = ofReal x + ofReal y :=
  ext rfl (add_zero 0).symm
theorem ofReal_mul (x y : R) : ofReal (x * y) = ofReal x * ofReal y := by
  apply ext
  · dsimp; rw [mul_zero, sub_zero]
  · dsimp; rw [mul_zero, zero_mul, add_zero]
theorem ofReal_rpow (x : R) : ∀ k : Nat, ofReal (rpow x k) = cpow (ofReal x) k
  | 0 => rfl
  | k + 1 => by rw [rpow_succ, ofReal_mul, ofReal_rpow x k, cpow]
theorem ofReal_inj {x y : R} (h : ofReal x = ofReal y) : x = y :=
  congrArg Complex.re h

theorem conj_zero : conj (0 : Complex R) = 0 := ext rfl neg_zero
theorem conj_one  : conj (1 : Complex R) = 1 := ext rfl neg_zero
theorem conj_conj (z : Complex R) : conj (conj z) = z := ext rfl (neg_neg z.im)
theorem conj_ofReal (x : R) : conj (ofReal x) = ofReal x := ext rfl neg_zero
theorem conj_add (z w : Complex R) : conj (z + w) = conj z + conj w :=
  ext rfl (neg_add z.im w.im)
theorem conj_mul (z w : Complex R) : conj (z * w) = conj z * conj w := by
  apply ext
  · dsimp; rw [neg_mul_neg]
  · dsimp; rw [mul_neg, neg_mul, neg_add]

theorem conj_mul_self (z : Complex R) : conj z * z = ofReal (normSq z) := by
  apply ext
  · dsimp [normSq]; rw [neg_mul, sub_eq_add_neg, neg_neg]
  · dsimp; rw [neg_mul, mul_comm z.im z.re, add_neg_cancel]

theorem mul_conj_self (z : Complex R) : z * conj z = ofReal (normSq z) := by
  rw [cmul_comm, conj_mul_self]

theorem normSq_zero : normSq (0 : Complex R) = 0 := by
  unfold normSq; dsimp; rw [zero_mul, add_zero]

theorem normSq_one : normSq (1 : Complex R) = 1 := by
  unfold normSq; dsimp; rw [one_mul, zero_mul, add_zero]

theorem normSq_ofReal (x : R) : normSq (ofReal x) = x * x := by
  unfold normSq; dsimp; rw [zero_mul, add_zero]

theorem normSq_conj (z : Complex R) : normSq (conj z) = normSq z := by
  unfold normSq; dsimp; rw [neg_mul_neg]

theorem normSq_nonneg (z : Complex R) : 0 ≤ normSq z :=
  add_nonneg (sq_nonneg z.re) (sq_nonneg z.im)

theorem normSq_eq_zero_iff (z : Complex R) : normSq z = 0 ↔ z = 0 := by
  unfold normSq
  rw [add_eq_zero_iff_of_nonneg (sq_nonneg z.re) (sq_nonneg z.im), sq_eq_zero_iff, sq_eq_zero_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ext h1 h2
  · intro h; subst h; exact ⟨rfl, rfl⟩

theorem normSq_pos_of_ne_zero {z : Complex R} (hz : z ≠ 0) : 0 < normSq z :=
  lt_of_le_of_ne (normSq_nonneg z) (fun h => hz ((normSq_eq_zero_iff z).mp h.symm))

theorem normSq_mul (z w : Complex R) : normSq (z * w) = normSq z * normSq w := by
  apply ofReal_inj
  calc ofReal (normSq (z * w))
      = conj (z * w) * (z * w) := (conj_mul_self (z * w)).symm
    _ = (conj z * conj w) * (z * w) := by rw [conj_mul]
    _ = conj z * (conj w * (z * w)) := cmul_assoc _ _ _
    _ = conj z * (z * (conj w * w)) := by
          rw [← cmul_assoc (conj w) z w, cmul_comm (conj w) z, cmul_assoc z (conj w) w]
    _ = (conj z * z) * (conj w * w) := (cmul_assoc _ _ _).symm
    _ = ofReal (normSq z) * ofReal (normSq w) := by rw [conj_mul_self, conj_mul_self]
    _ = ofReal (normSq z * normSq w) := (ofReal_mul _ _).symm

theorem normSq_cpow (z : Complex R) : ∀ k : Nat, normSq (cpow z k) = rpow (normSq z) k
  | 0 => normSq_one
  | k + 1 => by rw [cpow, normSq_mul, normSq_cpow z k, rpow_succ]

end RingOps
end Complex

-- ============================================================================
-- §4. Finite Sums `finSum` over `Fin n`, Monotonicity, and Complex Lagrange
-- ============================================================================

def finSum {α : Type u} [Add α] [OfNat α (nat_lit 0)] : {n : Nat} → (Fin n → α) → α
  | 0, _ => 0
  | _ + 1, f => f ⟨0, Nat.zero_lt_succ _⟩ + finSum (fun i => f i.succ)

namespace SumLemmas

open RingLemmas Complex

section RealSums
variable {R : Type u} [LinearOrderedCommRing R]

theorem rfinSum_zero : ∀ {n : Nat}, finSum (fun _ : Fin n => (0 : R)) = 0
  | 0 => rfl
  | _ + 1 => by unfold finSum; rw [rfinSum_zero, add_zero]

theorem rfinSum_add : ∀ {n : Nat} (f g : Fin n → R),
    finSum (fun i => f i + g i) = finSum f + finSum g
  | 0, _, _ => (add_zero 0).symm
  | _ + 1, f, g => by
    unfold finSum
    rw [rfinSum_add]
    calc f ⟨0, _⟩ + g ⟨0, _⟩ + (finSum (fun i => f i.succ) + finSum (fun i => g i.succ))
        = f ⟨0, _⟩ + (g ⟨0, _⟩ + (finSum (fun i => f i.succ) + finSum (fun i => g i.succ))) :=
            add_assoc _ _ _
      _ = f ⟨0, _⟩ + (finSum (fun i => f i.succ) + (g ⟨0, _⟩ + finSum (fun i => g i.succ))) := by
            rw [← add_assoc (g ⟨0, _⟩), add_comm (g ⟨0, _⟩) (finSum _), add_assoc]
      _ = (f ⟨0, _⟩ + finSum (fun i => f i.succ)) + (g ⟨0, _⟩ + finSum (fun i => g i.succ)) :=
            (add_assoc _ _ _).symm

theorem rfinSum_sub : ∀ {n : Nat} (f g : Fin n → R),
    finSum (fun i => f i - g i) = finSum f - finSum g
  | 0, _, _ => (sub_zero 0).symm
  | _ + 1, f, g => by
    unfold finSum; dsimp
    rw [rfinSum_sub, sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add]
    calc f ⟨0, _⟩ + -(g ⟨0, _⟩) + (finSum (fun i => f i.succ) + -(finSum (fun i => g i.succ)))
        = f ⟨0, _⟩ + (-(g ⟨0, _⟩) + (finSum (fun i => f i.succ) + -(finSum (fun i => g i.succ)))) :=
            add_assoc _ _ _
      _ = f ⟨0, _⟩ + (finSum (fun i => f i.succ) + (-(g ⟨0, _⟩) + -(finSum (fun i => g i.succ)))) := by
            rw [← add_assoc (-(g ⟨0, _⟩)), add_comm (-(g ⟨0, _⟩)) (finSum _), add_assoc]
      _ = (f ⟨0, _⟩ + finSum (fun i => f i.succ)) + (-(g ⟨0, _⟩) + -(finSum (fun i => g i.succ))) :=
            (add_assoc _ _ _).symm

theorem rfinSum_mul_left (c : R) : ∀ {n : Nat} (f : Fin n → R),
    c * finSum f = finSum (fun i => c * f i)
  | 0, _ => mul_zero c
  | _ + 1, f => by unfold finSum; rw [left_distrib, rfinSum_mul_left]

theorem rfinSum_mul_right (c : R) : ∀ {n : Nat} (f : Fin n → R),
    finSum f * c = finSum (fun i => f i * c)
  | 0, _ => zero_mul c
  | _ + 1, f => by unfold finSum; rw [right_distrib, rfinSum_mul_right]

theorem rfinSum_const (c : R) : ∀ n : Nat, finSum (fun _ : Fin n => c) = natCast R n * c
  | 0 => (zero_mul c).symm
  | n + 1 => by
    unfold finSum natCast
    rw [rfinSum_const c n, right_distrib, one_mul, add_comm]

theorem rfinSum_single : ∀ {n : Nat} (i₀ : Fin n) (v : R),
    finSum (fun i : Fin n => if i = i₀ then v else 0) = v
  | 0, i₀, _ => Fin.elim0 i₀
  | m + 1, i₀, v => by
    unfold finSum; dsimp
    by_cases h0 : i₀.val = 0
    · have hi0 : (0 : Fin (m + 1)) = i₀ := Fin.ext h0.symm
      have htail : (fun i : Fin m => if i.succ = i₀ then v else (0 : R)) = (fun _ => 0) := by
        funext i
        have hne : i.succ ≠ i₀ := fun heq => by
          have := congrArg Fin.val heq; dsimp [Fin.succ] at this; omega
        simp [hne]
      rw [if_pos hi0, htail, rfinSum_zero, add_zero]
    · have hi0 : (0 : Fin (m + 1)) ≠ i₀ := fun heq =>
        h0 (congrArg Fin.val heq).symm
      let j₀ : Fin m := ⟨i₀.val - 1, by omega⟩
      have htail : (fun i : Fin m => if i.succ = i₀ then v else (0 : R)) =
                   (fun i : Fin m => if i = j₀ then v else 0) := by
        funext i
        have hiff : i.succ = i₀ ↔ i = j₀ := by
          constructor
          · intro h; apply Fin.ext; have := congrArg Fin.val h; dsimp [Fin.succ, j₀] at *; omega
          · intro h; apply Fin.ext; have := congrArg Fin.val h; dsimp [Fin.succ, j₀] at *; omega
        by_cases hij : i = j₀
        · rw [if_pos (hiff.mpr hij), if_pos hij]
        · rw [if_neg (fun hs => hij (hiff.mp hs)), if_neg hij]
      rw [if_neg hi0, htail, rfinSum_single j₀ v, zero_add]

theorem rfinSum_nonneg : ∀ {n : Nat} {f : Fin n → R}, (∀ i, 0 ≤ f i) → 0 ≤ finSum f
  | 0, _, _ => le_refl 0
  | _ + 1, _, hf => add_nonneg (hf _) (rfinSum_nonneg (fun i => hf i.succ))

theorem rfinSum_eq_zero_iff : ∀ {n : Nat} {f : Fin n → R},
    (∀ i, 0 ≤ f i) → (finSum f = 0 ↔ ∀ i, f i = 0)
  | 0, _, _ => ⟨fun _ i => Fin.elim0 i, fun _ => rfl⟩
  | m + 1, f, hf => by
    unfold finSum
    rw [add_eq_zero_iff_of_nonneg (hf _) (rfinSum_nonneg (fun i => hf i.succ)),
        rfinSum_eq_zero_iff (fun i => hf i.succ)]
    constructor
    · rintro ⟨h0, hs⟩ i
      by_cases hi : i.val = 0
      · have : i = ⟨0, Nat.zero_lt_succ m⟩ := Fin.ext hi
        rw [this]; exact h0
      · let j : Fin m := ⟨i.val - 1, by omega⟩
        have hij : i = j.succ := Fin.ext (by dsimp [Fin.succ, j]; omega)
        rw [hij]; exact hs j
    · intro hall; exact ⟨hall _, fun j => hall j.succ⟩

theorem rfinSum_le_rfinSum {n : Nat} {f g : Fin n → R} (h : ∀ i, f i ≤ g i) :
    finSum f ≤ finSum g := by
  rw [← sub_nonneg, ← rfinSum_sub]
  exact rfinSum_nonneg (fun i => sub_nonneg.mpr (h i))

theorem rfinSum_eq_rfinSum_iff {n : Nat} {f g : Fin n → R} (h : ∀ i, f i ≤ g i) :
    finSum f = finSum g ↔ ∀ i, f i = g i := by
  constructor
  · intro heq
    have hsub : finSum (fun i => g i - f i) = 0 := by
      rw [rfinSum_sub, heq, sub_self]
    have hall := (rfinSum_eq_zero_iff (fun i => sub_nonneg.mpr (h i))).mp hsub
    intro i; exact (sub_eq_zero.mp (hall i)).symm
  · intro hall
    have : f = g := funext hall
    rw [this]

theorem rfinSum_comm : ∀ {n m : Nat} (h : Fin n → Fin m → R),
    finSum (fun i => finSum (fun j => h i j)) = finSum (fun j => finSum (fun i => h i j))
  | 0, m, _ => by
    change (0 : R) = finSum (fun _ : Fin m => (0 : R))
    exact rfinSum_zero.symm
  | k + 1, m, h => by
    change finSum (fun j : Fin m => h ⟨0, Nat.zero_lt_succ k⟩ j) +
             finSum (fun i : Fin k => finSum (fun j : Fin m => h i.succ j)) =
           finSum (fun j : Fin m => h ⟨0, Nat.zero_lt_succ k⟩ j +
             finSum (fun i : Fin k => h i.succ j))
    rw [rfinSum_comm (fun i j => h i.succ j), ← rfinSum_add]

end RealSums

section ComplexSums
variable {R : Type u} [LinearOrderedCommRing R]

theorem cfinSum_zero : ∀ {n : Nat}, finSum (fun _ : Fin n => (0 : Complex R)) = 0
  | 0 => rfl
  | _ + 1 => by unfold finSum; rw [cfinSum_zero, cadd_zero]

theorem cfinSum_add : ∀ {n : Nat} (f g : Fin n → Complex R),
    finSum (fun i => f i + g i) = finSum f + finSum g
  | 0, _, _ => (cadd_zero 0).symm
  | _ + 1, f, g => by
    unfold finSum
    rw [cfinSum_add]
    calc f ⟨0, _⟩ + g ⟨0, _⟩ + (finSum (fun i => f i.succ) + finSum (fun i => g i.succ))
        = f ⟨0, _⟩ + (g ⟨0, _⟩ + (finSum (fun i => f i.succ) + finSum (fun i => g i.succ))) :=
            cadd_assoc _ _ _
      _ = f ⟨0, _⟩ + (finSum (fun i => f i.succ) + (g ⟨0, _⟩ + finSum (fun i => g i.succ))) := by
            rw [← cadd_assoc (g ⟨0, _⟩), cadd_comm (g ⟨0, _⟩) (finSum _), cadd_assoc]
      _ = (f ⟨0, _⟩ + finSum (fun i => f i.succ)) + (g ⟨0, _⟩ + finSum (fun i => g i.succ)) :=
            (cadd_assoc _ _ _).symm

theorem cfinSum_mul_left (c : Complex R) : ∀ {n : Nat} (f : Fin n → Complex R),
    c * finSum f = finSum (fun i => c * f i)
  | 0, _ => cmul_zero c
  | _ + 1, f => by unfold finSum; rw [cleft_distrib, cfinSum_mul_left]

theorem cfinSum_mul_right (c : Complex R) : ∀ {n : Nat} (f : Fin n → Complex R),
    finSum f * c = finSum (fun i => f i * c)
  | 0, _ => czero_mul c
  | _ + 1, f => by unfold finSum; rw [cright_distrib, cfinSum_mul_right]

theorem cfinSum_comm : ∀ {n m : Nat} (h : Fin n → Fin m → Complex R),
    finSum (fun i => finSum (fun j => h i j)) = finSum (fun j => finSum (fun i => h i j))
  | 0, m, _ => by
    change (0 : Complex R) = finSum (fun _ : Fin m => (0 : Complex R))
    exact cfinSum_zero.symm
  | k + 1, m, h => by
    change finSum (fun j : Fin m => h ⟨0, Nat.zero_lt_succ k⟩ j) +
             finSum (fun i : Fin k => finSum (fun j : Fin m => h i.succ j)) =
           finSum (fun j : Fin m => h ⟨0, Nat.zero_lt_succ k⟩ j +
             finSum (fun i : Fin k => h i.succ j))
    rw [cfinSum_comm (fun i j => h i.succ j), ← cfinSum_add]

theorem ofReal_finSum : ∀ {n : Nat} (f : Fin n → R),
    ofReal (finSum f) = finSum (fun i => ofReal (f i))
  | 0, _ => rfl
  | _ + 1, f => by unfold finSum; rw [ofReal_add, ofReal_finSum]

theorem re_finSum : ∀ {n : Nat} (f : Fin n → Complex R),
    (finSum f).re = finSum (fun i => (f i).re)
  | 0, _ => rfl
  | _ + 1, f => by unfold finSum; rw [add_re, re_finSum]

theorem im_finSum : ∀ {n : Nat} (f : Fin n → Complex R),
    (finSum f).im = finSum (fun i => (f i).im)
  | 0, _ => rfl
  | _ + 1, f => by unfold finSum; rw [add_im, im_finSum]

theorem conj_finSum : ∀ {n : Nat} (f : Fin n → Complex R),
    conj (finSum f) = finSum (fun i => conj (f i))
  | 0, _ => conj_zero
  | _ + 1, f => by unfold finSum; rw [conj_add, conj_finSum]

theorem cfinSum_single : ∀ {n : Nat} (i₀ : Fin n) (v : Complex R),
    finSum (fun i : Fin n => if i = i₀ then v else 0) = v
  | 0, i₀, _ => Fin.elim0 i₀
  | m + 1, i₀, v => by
    unfold finSum; dsimp
    by_cases h0 : i₀.val = 0
    · have hi0 : (0 : Fin (m + 1)) = i₀ := Fin.ext h0.symm
      have htail : (fun i : Fin m => if i.succ = i₀ then v else (0 : Complex R)) = (fun _ => 0) := by
        funext i
        have hne : i.succ ≠ i₀ := fun heq => by
          have := congrArg Fin.val heq; dsimp [Fin.succ] at this; omega
        simp [hne]
      rw [if_pos hi0, htail, cfinSum_zero, cadd_zero]
    · have hi0 : (0 : Fin (m + 1)) ≠ i₀ := fun heq =>
        h0 (congrArg Fin.val heq).symm
      let j₀ : Fin m := ⟨i₀.val - 1, by omega⟩
      have htail : (fun i : Fin m => if i.succ = i₀ then v else (0 : Complex R)) =
                   (fun i : Fin m => if i = j₀ then v else 0) := by
        funext i
        have hiff : i.succ = i₀ ↔ i = j₀ := by
          constructor
          · intro h; apply Fin.ext; have := congrArg Fin.val h; dsimp [Fin.succ, j₀] at *; omega
          · intro h; apply Fin.ext; have := congrArg Fin.val h; dsimp [Fin.succ, j₀] at *; omega
        by_cases hij : i = j₀
        · rw [if_pos (hiff.mpr hij), if_pos hij]
        · rw [if_neg (fun hs => hij (hiff.mp hs)), if_neg hij]
      rw [if_neg hi0, htail, cfinSum_single j₀ v, czero_add]

/-- Real-variable Lagrange identity: `∑_i ∑_j (x_i - x_j)^2 = 2 (n ∑_i x_i^2 - (∑_i x_i)^2)`. -/
theorem real_lagrange {n : Nat} (x : Fin n → R) :
    finSum (fun i => finSum (fun j => (x i - x j) * (x i - x j))) =
    (1 + 1 : R) * (natCast R n * finSum (fun i => x i * x i) - finSum x * finSum x) := by
  have expand_sq : ∀ a b : R,
      (a - b) * (a - b) = (a * a + b * b) - (1 + 1 : R) * (a * b) := by
    intro a b
    rw [sub_mul, mul_sub, mul_sub, right_distrib, one_mul,
        sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg,
        neg_add, neg_neg, mul_comm b a]
    calc a * a + -(a * b) + (-(a * b) + b * b)
        = a * a + (-(a * b) + (-(a * b) + b * b)) := add_assoc _ _ _
      _ = a * a + (-(a * b) + -(a * b) + b * b) := by rw [← add_assoc (-(a * b))]
      _ = a * a + (b * b + (-(a * b) + -(a * b))) := by rw [add_comm (-(a * b) + -(a * b)) (b * b)]
      _ = (a * a + b * b) + (-(a * b) + -(a * b)) := (add_assoc _ _ _).symm
      _ = (a * a + b * b) + -(a * b + a * b) := by rw [← neg_add]
  have hrow : ∀ i : Fin n,
      finSum (fun j => (x i - x j) * (x i - x j)) =
      (natCast R n * (x i * x i) + finSum (fun j => x j * x j)) -
      (1 + 1 : R) * (x i * finSum x) := by
    intro i
    have hfun : (fun j : Fin n => (x i - x j) * (x i - x j)) =
                (fun j : Fin n => (x i * x i + x j * x j) - (1 + 1 : R) * (x i * x j)) :=
      funext (fun j => expand_sq (x i) (x j))
    rw [hfun, rfinSum_sub, rfinSum_add, rfinSum_const (x i * x i) n,
        ← rfinSum_mul_left (1 + 1 : R), ← rfinSum_mul_left (x i)]
  have houter : (fun i : Fin n => finSum (fun j => (x i - x j) * (x i - x j))) =
                (fun i : Fin n =>
                  (natCast R n * (x i * x i) + finSum (fun j => x j * x j)) -
                  (1 + 1 : R) * (x i * finSum x)) := funext hrow
  rw [houter, rfinSum_sub, rfinSum_add, ← rfinSum_mul_left (natCast R n),
      rfinSum_const (finSum (fun j => x j * x j)) n,
      ← rfinSum_mul_left (1 + 1 : R), ← rfinSum_mul_right (finSum x),
      mul_sub, right_distrib (1 : R) 1, right_distrib (1 : R) 1, one_mul, one_mul]

/-- Complex Lagrange identity: `∑_i ∑_j |z_i - z_j|^2 = 2 (n ∑_i |z_i|^2 - |∑_i z_i|^2)`. -/
theorem complex_lagrange {n : Nat} (z : Fin n → Complex R) :
    finSum (fun i => finSum (fun j => normSq (z i - z j))) =
    (1 + 1 : R) * (natCast R n * finSum (fun i => normSq (z i)) - normSq (finSum z)) := by
  have hsplit : (fun i : Fin n => finSum (fun j => normSq (z i - z j))) =
                (fun i : Fin n =>
                  finSum (fun j => ((z i).re - (z j).re) * ((z i).re - (z j).re)) +
                  finSum (fun j => ((z i).im - (z j).im) * ((z i).im - (z j).im))) := by
    funext i
    exact rfinSum_add _ _
  rw [hsplit, rfinSum_add, real_lagrange (fun i => (z i).re), real_lagrange (fun i => (z i).im),
      ← left_distrib (1 + 1 : R)]
  congr 1
  unfold normSq
  rw [re_finSum, im_finSum, rfinSum_add, left_distrib (natCast R n)]
  have rearrange : ∀ a b c d : R, (a - c) + (b - d) = (a + b) - (c + d) := by
    intro a b c d
    rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add]
    calc a + -c + (b + -d)
        = a + (-c + (b + -d)) := add_assoc _ _ _
      _ = a + (b + (-c + -d)) := by rw [← add_assoc (-c), add_comm (-c) b, add_assoc]
      _ = (a + b) + (-c + -d) := (add_assoc _ _ _).symm
  exact rearrange _ _ _ _

/-- Complex Cauchy-Schwarz on `Fin n`: `|∑_i z_i|^2 ≤ n ∑_i |z_i|^2`. -/
theorem normSq_finSum_le {n : Nat} (z : Fin n → Complex R) :
    normSq (finSum z) ≤ natCast R n * finSum (fun i => normSq (z i)) := by
  rw [← sub_nonneg, ← mul_two_nonneg_iff, ← complex_lagrange z]
  exact rfinSum_nonneg (fun i => rfinSum_nonneg (fun j => normSq_nonneg (z i - z j)))

/-- Equality in complex Cauchy-Schwarz holds iff all `z_i` are pairwise equal. -/
theorem normSq_finSum_eq_iff {n : Nat} (z : Fin n → Complex R) :
    normSq (finSum z) = natCast R n * finSum (fun i => normSq (z i)) ↔
    ∀ i j : Fin n, z i = z j := by
  have hlag := complex_lagrange z
  have hnonneg : ∀ i, 0 ≤ finSum (fun j => normSq (z i - z j)) :=
    fun i => rfinSum_nonneg (fun j => normSq_nonneg (z i - z j))
  constructor
  · intro heq
    have hzero : finSum (fun i => finSum (fun j => normSq (z i - z j))) = 0 := by
      rw [hlag, heq, sub_self, mul_zero]
    have hall1 := (rfinSum_eq_zero_iff hnonneg).mp hzero
    intro i j
    have hall2 := (rfinSum_eq_zero_iff (fun k => normSq_nonneg (z i - z k))).mp (hall1 i)
    have hns := (normSq_eq_zero_iff (z i - z j)).mp (hall2 j)
    exact ext (sub_eq_zero.mp (congrArg Complex.re hns))
              (sub_eq_zero.mp (congrArg Complex.im hns))
  · intro hall
    have hzero : finSum (fun i => finSum (fun j => normSq (z i - z j))) = 0 := by
      apply (rfinSum_eq_zero_iff hnonneg).mpr
      intro i
      apply (rfinSum_eq_zero_iff (fun j => normSq_nonneg (z i - z j))).mpr
      intro j
      have hsub : z i - z j = 0 := by
        rw [hall i j]; exact ext (sub_self _) (sub_self _)
      rw [hsub, normSq_zero]
    rw [hzero] at hlag
    have hdiff := (mul_two_eq_zero_iff.mp hlag.symm)
    exact (sub_eq_zero.mp hdiff).symm

end ComplexSums
end SumLemmas

-- ============================================================================
-- §5. Matrix Algebra (`CMat R n`, `RMat R n`), Unitary Invariance,
--     and Classical n x n Schur's Inequality & Normality Characterization
-- ============================================================================

abbrev CMat (R : Type u) (n : Nat) := Fin n → Fin n → Complex R
abbrev RMat (R : Type u) (n : Nat) := Fin n → Fin n → R

section MatrixTheory

open RingLemmas Complex SumLemmas

variable {R : Type u} [LinearOrderedCommRing R]

def zeroMat (n : Nat) : CMat R n := fun _ _ => 0
def eye (n : Nat) : CMat R n := fun i j => if i = j then 1 else 0
def addMat {n : Nat} (A B : CMat R n) : CMat R n := fun i j => A i j + B i j
def mul {n : Nat} (A B : CMat R n) : CMat R n :=
  fun i j => finSum (fun k : Fin n => A i k * B k j)
def adj {n : Nat} (A : CMat R n) : CMat R n := fun i j => conj (A j i)
def trace {n : Nat} (A : CMat R n) : Complex R := finSum (fun i : Fin n => A i i)
def frobNormSq {n : Nat} (A : CMat R n) : R :=
  finSum (fun i : Fin n => finSum (fun j : Fin n => normSq (A i j)))
def singleMat (n : Nat) (a b : Fin n) (v : Complex R) : CMat R n :=
  fun i j => if i = a ∧ j = b then v else 0

def matPow {n : Nat} (A : CMat R n) : Nat → CMat R n
  | 0 => eye n
  | k + 1 => mul (matPow A k) A

def IsNormal {n : Nat} (A : CMat R n) : Prop := mul A (adj A) = mul (adj A) A
def IsUnitary {n : Nat} (U : CMat R n) : Prop := mul (adj U) U = eye n ∧ mul U (adj U) = eye n
def IsUpperTriangular {n : Nat} (T : CMat R n) : Prop :=
  ∀ i j : Fin n, j.val < i.val → T i j = 0
def IsDiagonal {n : Nat} (T : CMat R n) : Prop :=
  ∀ i j : Fin n, i ≠ j → T i j = 0

/-- `A` admits unitary Schur triangularization `A = U T U*` with upper-triangular `T`. -/
def HasSchurDecomp {n : Nat} (A T U : CMat R n) : Prop :=
  IsUnitary U ∧ IsUpperTriangular T ∧ A = mul (mul U T) (adj U)

/-- Real matrix operations and exact normality bridge `M_n(R) ↔ M_n(Complex R)`. -/
def realMul {n : Nat} (A B : RMat R n) : RMat R n :=
  fun i j => finSum (fun k : Fin n => A i k * B k j)
def realTranspose {n : Nat} (A : RMat R n) : RMat R n := fun i j => A j i
def IsRealNormal {n : Nat} (A : RMat R n) : Prop :=
  realMul A (realTranspose A) = realMul (realTranspose A) A
def toComplexMat {n : Nat} (A : RMat R n) : CMat R n := fun i j => ofReal (A i j)

theorem toComplexMat_mul {n : Nat} (A B : RMat R n) :
    toComplexMat (realMul A B) = mul (toComplexMat A) (toComplexMat B) := by
  funext i j
  unfold toComplexMat realMul mul
  rw [ofReal_finSum]
  congr 1; funext k; exact ofReal_mul _ _

theorem toComplexMat_adj {n : Nat} (A : RMat R n) :
    adj (toComplexMat A) = toComplexMat (realTranspose A) := by
  funext i j
  exact conj_ofReal (A j i)

theorem isRealNormal_iff_isNormal_toComplex {n : Nat} (A : RMat R n) :
    IsRealNormal A ↔ IsNormal (toComplexMat A) := by
  unfold IsRealNormal IsNormal
  rw [toComplexMat_adj, ← toComplexMat_mul, ← toComplexMat_mul]
  constructor
  · intro h; rw [h]
  · intro h; funext i j; exact ofReal_inj (congrFun (congrFun h i) j)

theorem mat_mul_assoc {n : Nat} (A B C : CMat R n) :
    mul (mul A B) C = mul A (mul B C) := by
  funext i j
  unfold mul
  have h1 : (fun k : Fin n => finSum (fun p => A i p * B p k) * C k j) =
            (fun k : Fin n => finSum (fun p => (A i p * B p k) * C k j)) :=
    funext (fun k => cfinSum_mul_right (C k j) _)
  have h2 : (fun p : Fin n => A i p * finSum (fun k => B p k * C k j)) =
            (fun p : Fin n => finSum (fun k => A i p * (B p k * C k j))) :=
    funext (fun p => cfinSum_mul_left (A i p) _)
  rw [h1, h2, cfinSum_comm]
  congr 1; funext p; congr 1; funext k; exact cmul_assoc _ _ _

theorem eye_mul {n : Nat} (A : CMat R n) : mul (eye n) A = A := by
  funext i j
  unfold mul eye
  have h : (fun k : Fin n => (if i = k then (1 : Complex R) else 0) * A k j) =
           (fun k : Fin n => if k = i then A i j else 0) := by
    funext k
    by_cases hik : k = i
    · subst hik; simp [cone_mul]
    · have hne : i ≠ k := fun h => hik h.symm
      simp [hik, hne, czero_mul]
  rw [h, cfinSum_single i (A i j)]

theorem mul_eye {n : Nat} (A : CMat R n) : mul A (eye n) = A := by
  funext i j
  unfold mul eye
  have h : (fun k : Fin n => A i k * (if k = j then (1 : Complex R) else 0)) =
           (fun k : Fin n => if k = j then A i j else 0) := by
    funext k
    by_cases hkj : k = j
    · subst hkj; simp [cmul_one]
    · simp [hkj, cmul_zero]
  rw [h, cfinSum_single j (A i j)]

theorem mul_addMat {n : Nat} (A B C : CMat R n) :
    mul A (addMat B C) = addMat (mul A B) (mul A C) := by
  funext i j
  unfold mul addMat
  have h : (fun k : Fin n => A i k * (B k j + C k j)) =
           (fun k : Fin n => A i k * B k j + A i k * C k j) :=
    funext (fun k => cleft_distrib _ _ _)
  rw [h, cfinSum_add]

theorem addMat_mul {n : Nat} (A B C : CMat R n) :
    mul (addMat A B) C = addMat (mul A C) (mul B C) := by
  funext i j
  unfold mul addMat
  have h : (fun k : Fin n => (A i k + B i k) * C k j) =
           (fun k : Fin n => A i k * C k j + B i k * C k j) :=
    funext (fun k => cright_distrib _ _ _)
  rw [h, cfinSum_add]

theorem mul_zeroMat {n : Nat} (A : CMat R n) : mul A (zeroMat n) = zeroMat n := by
  funext i j; unfold mul zeroMat
  have : (fun k : Fin n => A i k * (0 : Complex R)) = (fun _ => 0) :=
    funext (fun k => cmul_zero _)
  rw [this, cfinSum_zero]

theorem addMat_zeroMat {n : Nat} (A : CMat R n) : addMat A (zeroMat n) = A := by
  funext i j; exact cadd_zero _

theorem adj_eye (n : Nat) : adj (eye (R := R) n) = eye n := by
  funext i j; unfold adj eye
  by_cases hij : i = j
  · subst hij; simp [conj_one]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [hij, hji, conj_zero]

theorem adj_adj {n : Nat} (A : CMat R n) : adj (adj A) = A := by
  funext i j; exact conj_conj (A i j)

theorem adj_mul {n : Nat} (A B : CMat R n) : adj (mul A B) = mul (adj B) (adj A) := by
  funext i j
  unfold adj mul
  rw [conj_finSum]
  congr 1; funext k
  rw [conj_mul, cmul_comm]

theorem trace_mul_comm {n : Nat} (A B : CMat R n) : trace (mul A B) = trace (mul B A) := by
  unfold trace mul
  rw [cfinSum_comm]
  congr 1; funext j; congr 1; funext i; exact cmul_comm _ _

theorem trace_adj_mul_eq_frobNormSq {n : Nat} (A : CMat R n) :
    trace (mul (adj A) A) = ofReal (frobNormSq A) := by
  unfold trace mul adj frobNormSq
  have h : (fun i : Fin n => finSum (fun k => conj (A k i) * A k i)) =
           (fun i : Fin n => ofReal (finSum (fun k => normSq (A k i)))) := by
    funext i
    rw [ofReal_finSum]
    congr 1; funext k; exact conj_mul_self (A k i)
  rw [h, ← ofReal_finSum, rfinSum_comm]

theorem trace_mul_adj_eq_frobNormSq {n : Nat} (A : CMat R n) :
    trace (mul A (adj A)) = ofReal (frobNormSq A) := by
  rw [trace_mul_comm, trace_adj_mul_eq_frobNormSq]

theorem eye_isUnitary (n : Nat) : IsUnitary (eye (R := R) n) := by
  unfold IsUnitary; rw [adj_eye, eye_mul]; exact ⟨rfl, rfl⟩

theorem eye_isNormal (n : Nat) : IsNormal (eye (R := R) n) := by
  unfold IsNormal; rw [adj_eye]

theorem eye_isDiagonal (n : Nat) : IsDiagonal (eye (R := R) n) := by
  intro i j hij; unfold eye; simp [hij]

theorem isUpperTriangular_of_isDiagonal {n : Nat} {T : CMat R n} (hd : IsDiagonal T) :
    IsUpperTriangular T := by
  intro i j hji
  exact hd i j (fun heq => by subst heq; omega)

theorem adj_unitary_conj {n : Nat} (U X : CMat R n) :
    adj (mul (mul U X) (adj U)) = mul (mul U (adj X)) (adj U) := by
  rw [adj_mul, adj_mul, adj_adj, mat_mul_assoc]

theorem unitary_conj_mul {n : Nat} {U X Y : CMat R n} (hu1 : mul (adj U) U = eye n) :
    mul (mul (mul U X) (adj U)) (mul (mul U Y) (adj U)) = mul (mul U (mul X Y)) (adj U) := by
  calc mul (mul (mul U X) (adj U)) (mul (mul U Y) (adj U))
      = mul (mul U X) (mul (adj U) (mul (mul U Y) (adj U))) := mat_mul_assoc _ _ _
    _ = mul (mul U X) (mul (mul (adj U) (mul U Y)) (adj U)) := by rw [← mat_mul_assoc (adj U)]
    _ = mul (mul U X) (mul (mul (mul (adj U) U) Y) (adj U)) := by rw [← mat_mul_assoc (adj U) U Y]
    _ = mul (mul U X) (mul Y (adj U)) := by rw [hu1, eye_mul]
    _ = mul (mul (mul U X) Y) (adj U) := (mat_mul_assoc _ _ _).symm
    _ = mul (mul U (mul X Y)) (adj U) := by rw [mat_mul_assoc U X Y]

theorem trace_unitary_conj {n : Nat} {U X : CMat R n} (hu1 : mul (adj U) U = eye n) :
    trace (mul (mul U X) (adj U)) = trace X := by
  rw [trace_mul_comm, ← mat_mul_assoc, hu1, eye_mul]

theorem unitary_conj_inj {n : Nat} {U X Y : CMat R n} (hu1 : mul (adj U) U = eye n)
    (h : mul (mul U X) (adj U) = mul (mul U Y) (adj U)) : X = Y := by
  have simp_side : ∀ Z : CMat R n, mul (adj U) (mul (mul (mul U Z) (adj U)) U) = Z := by
    intro Z
    rw [mat_mul_assoc (mul U Z) (adj U) U, hu1, mul_eye, ← mat_mul_assoc (adj U) U Z, hu1, eye_mul]
  have h1 : mul (adj U) (mul (mul (mul U X) (adj U)) U) =
            mul (adj U) (mul (mul (mul U Y) (adj U)) U) := by rw [h]
  rw [simp_side X, simp_side Y] at h1
  exact h1

theorem schur_frobNormSq_eq {n : Nat} {A T U : CMat R n} (hS : HasSchurDecomp A T U) :
    frobNormSq A = frobNormSq T := by
  rcases hS with ⟨⟨hu1, _⟩, _, rfl⟩
  apply ofReal_inj
  rw [← trace_adj_mul_eq_frobNormSq, ← trace_adj_mul_eq_frobNormSq,
      adj_unitary_conj, unitary_conj_mul hu1, trace_unitary_conj hu1]

theorem schur_isNormal_iff {n : Nat} {A T U : CMat R n} (hS : HasSchurDecomp A T U) :
    IsNormal A ↔ IsNormal T := by
  rcases hS with ⟨⟨hu1, _⟩, _, rfl⟩
  unfold IsNormal
  rw [adj_unitary_conj, unitary_conj_mul hu1, unitary_conj_mul hu1]
  exact ⟨unitary_conj_inj hu1, fun h => by rw [h]⟩

theorem schur_matPow_eq {n : Nat} {A T U : CMat R n} (hS : HasSchurDecomp A T U) :
    ∀ k : Nat, matPow A k = mul (mul U (matPow T k)) (adj U)
  | 0 => by
    rcases hS with ⟨⟨_, hu2⟩, _, _⟩
    unfold matPow
    rw [mul_eye, hu2]
  | k + 1 => by
    have ih := schur_matPow_eq hS k
    rcases hS with ⟨⟨hu1, _⟩, _, hA⟩
    unfold matPow
    rw [ih, hA, unitary_conj_mul hu1]

theorem upperTriangular_mul {n : Nat} {S T : CMat R n}
    (hS : IsUpperTriangular S) (hT : IsUpperTriangular T) :
    IsUpperTriangular (mul S T) ∧ ∀ i : Fin n, mul S T i i = S i i * T i i := by
  constructor
  · intro i j hji
    unfold mul
    have hzero : (fun k : Fin n => S i k * T k j) = (fun _ => 0) := by
      funext k
      by_cases hki : k.val < i.val
      · rw [hS i k hki, czero_mul]
      · have hjk : j.val < k.val := by omega
        rw [hT k j hjk, cmul_zero]
    rw [hzero, cfinSum_zero]
  · intro i
    unfold mul
    have hdiag : (fun k : Fin n => S i k * T k i) =
                 (fun k : Fin n => if k = i then S i i * T i i else 0) := by
      funext k
      by_cases hki : k = i
      · subst hki; simp
      · have hne : k.val ≠ i.val := fun h => hki (Fin.ext h)
        by_cases hlt : k.val < i.val
        · rw [if_neg hki, hS i k hlt, czero_mul]
        · have hgt : i.val < k.val := by omega
          rw [if_neg hki, hT k i hgt, cmul_zero]
    rw [hdiag, cfinSum_single i]

theorem upperTriangular_matPow {n : Nat} {T : CMat R n} (hT : IsUpperTriangular T) :
    ∀ k : Nat, IsUpperTriangular (matPow T k) ∧ ∀ i : Fin n, matPow T k i i = cpow (T i i) k
  | 0 => ⟨isUpperTriangular_of_isDiagonal (eye_isDiagonal n), fun i => by unfold matPow eye cpow; simp⟩
  | k + 1 => by
    rcases upperTriangular_matPow hT k with ⟨ihT, ihD⟩
    rcases upperTriangular_mul ihT hT with ⟨hmulT, hmulD⟩
    refine ⟨hmulT, fun i => ?_⟩
    unfold matPow cpow
    rw [hmulD i, ihD i]

theorem schur_trace_matPow_eq {n : Nat} {A T U : CMat R n} (hS : HasSchurDecomp A T U) (k : Nat) :
    trace (matPow A k) = finSum (fun i : Fin n => cpow (T i i) k) := by
  have hpow := schur_matPow_eq hS k
  rcases hS with ⟨⟨hu1, _⟩, hT, _⟩
  rw [hpow, trace_unitary_conj hu1]
  unfold trace
  congr 1; funext i
  exact (upperTriangular_matPow hT k).2 i

/-- Pointwise row decomposition of squared moduli for an upper-triangular matrix `T`. -/
theorem upperTriangular_row_normSq {n : Nat} {T : CMat R n} (hT : IsUpperTriangular T) (i : Fin n) :
    finSum (fun j : Fin n => normSq (T i j)) =
    normSq (T i i) + finSum (fun j : Fin n => if i.val < j.val then normSq (T i j) else 0) := by
  have hpt : (fun j : Fin n => normSq (T i j)) =
             (fun j : Fin n =>
               (if j = i then normSq (T i i) else 0) +
               (if i.val < j.val then normSq (T i j) else 0)) := by
    funext j
    by_cases hji : j = i
    · subst hji
      have hnot : ¬ (j.val < j.val) := by omega
      simp [hnot, add_zero]
    · by_cases hij : i.val < j.val
      · simp [hji, hij, zero_add]
      · have hlt : j.val < i.val := by
          have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
          omega
        rw [if_neg hji, if_neg hij, add_zero, hT i j hlt, normSq_zero]
  rw [hpt, rfinSum_add, rfinSum_single i (normSq (T i i))]

/-- Exact Schur Frobenius decomposition for upper-triangular `T`:
    `‖T‖_F^2 = ∑_i |T_{ii}|^2 + ∑_i ∑_{j > i} |T_{ij}|^2`. -/
theorem upperTriangular_frobNormSq_decomp {n : Nat} {T : CMat R n} (hT : IsUpperTriangular T) :
    frobNormSq T =
    finSum (fun i : Fin n => normSq (T i i)) +
    finSum (fun i : Fin n => finSum (fun j : Fin n => if i.val < j.val then normSq (T i j) else 0)) := by
  unfold frobNormSq
  have hrows : (fun i : Fin n => finSum (fun j => normSq (T i j))) =
               (fun i : Fin n =>
                 normSq (T i i) + finSum (fun j => if i.val < j.val then normSq (T i j) else 0)) :=
    funext (upperTriangular_row_normSq hT)
  rw [hrows, rfinSum_add]

theorem isNormal_of_isDiagonal {n : Nat} {D : CMat R n} (hd : IsDiagonal D) : IsNormal D := by
  funext i j
  unfold mul adj
  by_cases hij : i = j
  · subst hij
    congr 1; funext k
    by_cases hik : i = k
    · subst hik; exact cmul_comm (D i i) (conj (D i i))
    · have hki : k ≠ i := fun h => hik h.symm
      rw [hd i k hik, hd k i hki, conj_zero, czero_mul]
  · have lhs : (fun k : Fin n => D i k * conj (D j k)) = (fun _ => 0) := by
      funext k
      by_cases hik : i = k
      · subst hik
        have hjk : j ≠ i := fun h => hij h.symm
        rw [hd j i hjk, conj_zero, cmul_zero]
      · rw [hd i k hik, czero_mul]
    have rhs : (fun k : Fin n => conj (D k i) * D k j) = (fun _ => 0) := by
      funext k
      by_cases hki : k = i
      · subst hki
        rw [hd k j hij, cmul_zero]
      · rw [hd k i hki, conj_zero, czero_mul]
    rw [lhs, rhs]

/-- Core lemma of Schur (1909): an upper-triangular matrix is normal iff it is diagonal. -/
theorem upperTriangular_isNormal_iff_isDiagonal {n : Nat} {T : CMat R n}
    (hT : IsUpperTriangular T) : IsNormal T ↔ IsDiagonal T := by
  constructor
  · intro hN
    suffices hbound : ∀ b : Nat, ∀ i j : Fin n, i.val < b → i ≠ j → T i j = 0 by
      intro i j hij
      exact hbound n i j i.isLt hij
    intro b
    induction b with
    | zero => intro i _ hi _; omega
    | succ m ih =>
      intro i j hi hij
      by_cases hlt : i.val < m
      · exact ih i j hlt hij
      · have him : i.val = m := by omega
        by_cases hjlt : j.val < i.val
        · exact hT i j hjlt
        · have hij_lt : i.val < j.val := by
            have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
            omega
          -- Compare the `(i, i)` real diagonal entries of `T T*` and `T* T`.
          have hdiag_eq : ((mul T (adj T)) i i).re = ((mul (adj T) T) i i).re :=
            congrArg Complex.re (congrFun (congrFun hN i) i)
          have hlhs : ((mul T (adj T)) i i).re =
              normSq (T i i) + finSum (fun q : Fin n => if i.val < q.val then normSq (T i q) else 0) := by
            unfold mul adj
            have h1 : (fun q : Fin n => T i q * conj (T i q)) =
                      (fun q : Fin n => ofReal (normSq (T i q))) :=
              funext (fun q => mul_conj_self (T i q))
            rw [h1, ← ofReal_finSum, ofReal_re, upperTriangular_row_normSq hT i]
          have hrhs : ((mul (adj T) T) i i).re = normSq (T i i) := by
            unfold mul adj
            have h1 : (fun p : Fin n => conj (T p i) * T p i) =
                      (fun p : Fin n => ofReal (normSq (T p i))) :=
              funext (fun p => conj_mul_self (T p i))
            rw [h1, ← ofReal_finSum, ofReal_re]
            have hcol : (fun p : Fin n => normSq (T p i)) =
                        (fun p : Fin n => if p = i then normSq (T i i) else 0) := by
              funext p
              by_cases hpi : p = i
              · subst hpi; simp
              · rw [if_neg hpi]
                have hpne : p.val ≠ i.val := fun h => hpi (Fin.ext h)
                by_cases hplt : p.val < i.val
                · have hpm : p.val < m := by omega
                  rw [ih p i hpm hpi, normSq_zero]
                · have higt : i.val < p.val := by omega
                  rw [hT p i higt, normSq_zero]
            rw [hcol, rfinSum_single i (normSq (T i i))]
          rw [hlhs, hrhs] at hdiag_eq
          have hsum_zero : finSum (fun q : Fin n => if i.val < q.val then normSq (T i q) else 0) = 0 := by
            apply add_left_cancel (a := normSq (T i i))
            rw [hdiag_eq, add_zero]
          have hnonneg : ∀ q : Fin n, 0 ≤ (if i.val < q.val then normSq (T i q) else 0) := by
            intro q; by_cases hq : i.val < q.val <;> simp [hq, normSq_nonneg, le_refl]
          have hq := (rfinSum_eq_zero_iff hnonneg).mp hsum_zero j
          rw [if_pos hij_lt] at hq
          exact (normSq_eq_zero_iff (T i j)).mp hq
  · exact isNormal_of_isDiagonal

/-- **Positive Theorem 1A (Schur's Inequality for all n x n matrices):**
    For any `A = U T U*`, `∑_i |λ_i|^2 ≤ ‖A‖_F^2`. -/
theorem schur_inequality {n : Nat} {A T U : CMat R n} (hS : HasSchurDecomp A T U) :
    finSum (fun i : Fin n => normSq (T i i)) ≤ frobNormSq A := by
  rw [schur_frobNormSq_eq hS, upperTriangular_frobNormSq_decomp hS.2.1]
  have hoff : 0 ≤ finSum (fun i : Fin n =>
      finSum (fun j : Fin n => if i.val < j.val then normSq (T i j) else 0)) := by
    apply rfinSum_nonneg; intro i; apply rfinSum_nonneg; intro j
    by_cases h : i.val < j.val <;> simp [h, normSq_nonneg, le_refl]
  have := LinearOrderedCommRing.add_le_add_left 0 _ hoff (finSum (fun i : Fin n => normSq (T i i)))
  rw [add_zero] at this
  exact this

/-- **Positive Theorem 1B (Schur's Normality Characterization for all n x n matrices):**
    Equality `∑_i |λ_i|^2 = ‖A‖_F^2` holds **if and only if** `A` is normal (`A A* = A* A`). -/
theorem schur_eq_iff_isNormal {n : Nat} {A T U : CMat R n} (hS : HasSchurDecomp A T U) :
    finSum (fun i : Fin n => normSq (T i i)) = frobNormSq A ↔ IsNormal A := by
  have hT := hS.2.1
  rw [schur_frobNormSq_eq hS, schur_isNormal_iff hS,
      upperTriangular_isNormal_iff_isDiagonal hT, upperTriangular_frobNormSq_decomp hT]
  have hrow_nn : ∀ i : Fin n,
      0 ≤ finSum (fun j : Fin n => if i.val < j.val then normSq (T i j) else 0) := by
    intro i; apply rfinSum_nonneg; intro j
    by_cases h : i.val < j.val <;> simp [h, normSq_nonneg, le_refl]
  constructor
  · intro heq
    have hzero : finSum (fun i : Fin n =>
        finSum (fun j : Fin n => if i.val < j.val then normSq (T i j) else 0)) = 0 := by
      apply add_left_cancel (a := finSum (fun i : Fin n => normSq (T i i)))
      rw [← heq, add_zero]
    have hall1 := (rfinSum_eq_zero_iff hrow_nn).mp hzero
    intro i j hij
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    by_cases hlt : i.val < j.val
    · have hinner_nn : ∀ q : Fin n, 0 ≤ (if i.val < q.val then normSq (T i q) else 0) := by
        intro q; by_cases hq : i.val < q.val <;> simp [hq, normSq_nonneg, le_refl]
      have hq := (rfinSum_eq_zero_iff hinner_nn).mp (hall1 i) j
      rw [if_pos hlt] at hq
      exact (normSq_eq_zero_iff (T i j)).mp hq
    · exact hT i j (by omega)
  · intro hd
    have hzero : finSum (fun i : Fin n =>
        finSum (fun j : Fin n => if i.val < j.val then normSq (T i j) else 0)) = 0 := by
      apply (rfinSum_eq_zero_iff hrow_nn).mpr; intro i
      have hinner_nn : ∀ q : Fin n, 0 ≤ (if i.val < q.val then normSq (T i q) else 0) := by
        intro q; by_cases hq : i.val < q.val <;> simp [hq, normSq_nonneg, le_refl]
      apply (rfinSum_eq_zero_iff hinner_nn).mpr; intro j
      by_cases hlt : i.val < j.val
      · have hij : i ≠ j := fun h => by subst h; omega
        rw [if_pos hlt, hd i j hij, normSq_zero]
      · rw [if_neg hlt]
    rw [hzero, add_zero]

-- ============================================================================
-- §6. True Spectral-Radius Power-Sum Bounds & Equal-Modulus Characterization
-- ============================================================================

/-- `ρ` is the spectral radius of the nonnegative eigenvalue-modulus tuple `r`. -/
def IsSpectralRadius {n : Nat} (r : Fin n → R) (ρ : R) : Prop :=
  0 ≤ ρ ∧ (∀ i : Fin n, 0 ≤ r i ∧ r i ≤ ρ) ∧ (0 < n → ∃ i : Fin n, r i = ρ)

/-- Eigenvalue modulus `k`-th power sum `∑_{i=1}^n r_i^k`. -/
def eigModPowSum {n : Nat} (r : Fin n → R) (k : Nat) : R :=
  finSum (fun i : Fin n => rpow (r i) k)

/-- Spectral-radius power sum upper bound `∑_{i=1}^n ρ^k = n ρ^k`. -/
def spectralPowerBound (R : Type u) [LinearOrderedCommRing R] (n : Nat) (ρ : R) (k : Nat) : R :=
  natCast R n * rpow ρ k

/-- **Positive Theorem 2A:** `∑_{i=1}^n r_i^k ≤ n ρ^k` holds for all `n` and `k`. -/
theorem eigModPowSum_le_spectralPowerBound {n : Nat} {r : Fin n → R} {ρ : R}
    (hρ : IsSpectralRadius r ρ) (k : Nat) :
    eigModPowSum r k ≤ spectralPowerBound R n ρ k := by
  unfold eigModPowSum spectralPowerBound
  rw [← rfinSum_const (rpow ρ k) n]
  exact rfinSum_le_rfinSum (fun i => rpow_le_rpow (hρ.2.1 i).1 (hρ.2.1 i).2 k)

/-- **Positive Theorem 2B (True Equality Characterization):**
    For every `k ≥ 1`, `∑_{i=1}^n r_i^k = n ρ^k` holds **if and only if** `∀ i, r_i = ρ`
    (all eigenvalues have equal modulus — a purely spectral condition, NOT normality!). -/
theorem eigModPowSum_eq_iff_equal_moduli {n : Nat} {r : Fin n → R} {ρ : R}
    (hρ : IsSpectralRadius r ρ) {k : Nat} (hk : 1 ≤ k) :
    eigModPowSum r k = spectralPowerBound R n ρ k ↔ ∀ i : Fin n, r i = ρ := by
  unfold eigModPowSum spectralPowerBound
  rw [← rfinSum_const (rpow ρ k) n]
  have hle : ∀ i : Fin n, rpow (r i) k ≤ rpow ρ k :=
    fun i => rpow_le_rpow (hρ.2.1 i).1 (hρ.2.1 i).2 k
  rw [rfinSum_eq_rfinSum_iff hle]
  constructor
  · intro hall i
    exact (rpow_eq_iff (hρ.2.1 i).1 hρ.1 hk).mp (hall i)
  · intro hall i; rw [hall i]

/-- **Positive Theorem 2C (Complex Trace Power-Sum Bound):**
    For any `A = U T U*` and `ρSq` bounding `|T_{ii}|^2`,
    `|tr(A^k)|^2 ≤ n ∑_i (|λ_i|^2)^k ≤ n^2 (ρSq)^k`. -/
theorem trace_normSq_le_spectralPowerBound {n : Nat} {A T U : CMat R n} {ρSq : R}
    (hS : HasSchurDecomp A T U)
    (hρ : IsSpectralRadius (fun i => normSq (T i i)) ρSq) (k : Nat) :
    normSq (trace (matPow A k)) ≤ natCast R n * spectralPowerBound R n ρSq k := by
  rw [schur_trace_matPow_eq hS k]
  have hcs := normSq_finSum_le (fun i : Fin n => cpow (T i i) k)
  have hpow : (fun i : Fin n => normSq (cpow (T i i) k)) =
              (fun i : Fin n => rpow (normSq (T i i)) k) :=
    funext (fun i => normSq_cpow (T i i) k)
  rw [hpow] at hcs
  exact le_trans hcs
    (mul_le_mul_of_nonneg_left (eigModPowSum_le_spectralPowerBound hρ k) (natCast_nonneg n))

/-- **Positive Theorem 3 (Normal Matrices DO Satisfy the Frobenius Power Bound):**
    If `A` is normal (`A = U T U*` with `IsNormal A`), then `‖A^k‖_F^2 = ∑_i (|λ_i|^2)^k ≤ n (ρSq)^k`,
    with equality (for `k ≥ 1`) iff all eigenvalues have equal squared modulus `|λ_i|^2 = ρSq`. -/
theorem normal_frobNormSq_matPow_le {n : Nat} {A T U : CMat R n} {ρSq : R}
    (hS : HasSchurDecomp A T U) (hN : IsNormal A)
    (hρ : IsSpectralRadius (fun i => normSq (T i i)) ρSq) (k : Nat) :
    frobNormSq (matPow A k) = eigModPowSum (fun i => normSq (T i i)) k ∧
    frobNormSq (matPow A k) ≤ spectralPowerBound R n ρSq k := by
  have hd : IsDiagonal T :=
    (upperTriangular_isNormal_iff_isDiagonal hS.2.1).mp ((schur_isNormal_iff hS).mp hN)
  have hdPow : IsDiagonal (matPow T k) := by
    induction k with
    | zero => exact eye_isDiagonal n
    | succ m ih =>
      intro i j hij
      unfold matPow mul
      have h0 : (fun p : Fin n => matPow T m i p * T p j) = (fun _ => 0) := by
        funext p
        by_cases hip : i = p
        · subst hip; rw [hd i j hij, cmul_zero]
        · rw [ih i p hip, czero_mul]
      rw [h0, cfinSum_zero]
  have hSk : HasSchurDecomp (matPow A k) (matPow T k) U :=
    ⟨hS.1, isUpperTriangular_of_isDiagonal hdPow, schur_matPow_eq hS k⟩
  have hEq : finSum (fun i : Fin n => normSq (matPow T k i i)) = frobNormSq (matPow A k) :=
    (schur_eq_iff_isNormal hSk).mpr ((schur_isNormal_iff hSk).mpr (isNormal_of_isDiagonal hdPow))
  have hdiag : (fun i : Fin n => normSq (matPow T k i i)) =
               (fun i : Fin n => rpow (normSq (T i i)) k) := by
    funext i
    rw [(upperTriangular_matPow hS.2.1 k).2 i, normSq_cpow]
  rw [hdiag] at hEq
  refine ⟨hEq.symm, ?_⟩
  rw [← hEq]
  exact eigModPowSum_le_spectralPowerBound hρ k

-- ============================================================================
-- §7. Explicit Counterexample Families for ALL n = m + 2 ≥ 2 and k ≥ 1
-- ============================================================================

theorem mul_singleMat_singleMat {n : Nat} (a b c d : Fin n) (u v : Complex R) :
    mul (singleMat n a b u) (singleMat n c d v) =
    if b = c then singleMat n a d (u * v) else zeroMat n := by
  funext i j
  unfold mul singleMat zeroMat
  by_cases hbc : b = c
  · subst hbc
    rw [if_pos rfl]
    have h : (fun p : Fin n => (if i = a ∧ p = b then u else 0) * (if p = b ∧ j = d then v else 0)) =
             (fun p : Fin n => if p = b then (if i = a ∧ j = d then u * v else 0) else 0) := by
      funext p
      by_cases hpb : p = b
      · subst hpb
        by_cases hia : i = a <;> by_cases hjd : j = d <;> simp [hia, hjd, czero_mul, cmul_zero]
      · simp [hpb, czero_mul]
    rw [h, cfinSum_single b]
  · rw [if_neg hbc]
    have h : (fun p : Fin n => (if i = a ∧ p = b then u else 0) * (if p = c ∧ j = d then v else 0)) =
             (fun _ => 0) := by
      funext p
      by_cases hpb : p = b
      · subst hpb; simp [hbc, cmul_zero]
      · simp [hpb, czero_mul]
    rw [h, cfinSum_zero]

theorem adj_singleMat {n : Nat} (a b : Fin n) (v : Complex R) :
    adj (singleMat n a b v) = singleMat n b a (conj v) := by
  funext i j
  unfold adj singleMat
  by_cases h : j = a ∧ i = b
  · rcases h with ⟨hja, hib⟩
    simp [hja, hib]
  · have h' : ¬ (i = b ∧ j = a) := fun ⟨hib, hja⟩ => h ⟨hja, hib⟩
    rw [if_neg h, if_neg h', conj_zero]

theorem trace_singleMat {n : Nat} (a b : Fin n) (v : Complex R) :
    trace (singleMat n a b v) = if a = b then v else 0 := by
  unfold trace singleMat
  by_cases hab : a = b
  · subst hab
    have h : (fun i : Fin n => if i = a ∧ i = a then v else 0) =
             (fun i : Fin n => if i = a then v else 0) := by
      funext i; by_cases hia : i = a <;> simp [hia]
    rw [if_pos rfl, h, cfinSum_single a v]
  · rw [if_neg hab]
    have h : (fun i : Fin n => if i = a ∧ i = b then v else 0) = (fun _ => 0) := by
      funext i
      have : ¬ (i = a ∧ i = b) := fun ⟨h1, h2⟩ => hab (h1.symm.trans h2)
      simp [this]
    rw [h, cfinSum_zero]

theorem frobNormSq_singleMat {n : Nat} (a b : Fin n) (v : Complex R) :
    frobNormSq (singleMat n a b v) = normSq v := by
  unfold frobNormSq singleMat
  have h : (fun i : Fin n => finSum (fun j : Fin n => normSq (if i = a ∧ j = b then v else 0))) =
           (fun i : Fin n => if i = a then normSq v else 0) := by
    funext i
    by_cases hia : i = a
    · have hj : (fun j : Fin n => normSq (if i = a ∧ j = b then v else 0)) =
                (fun j : Fin n => if j = b then normSq v else 0) := by
        funext j; by_cases hjb : j = b <;> simp [hia, hjb, normSq_zero]
      rw [if_pos hia, hj, rfinSum_single b (normSq v)]
    · have hj : (fun j : Fin n => normSq (if i = a ∧ j = b then v else 0)) = (fun _ => 0) := by
        funext j; simp [hia, normSq_zero]
      rw [if_neg hia, hj, rfinSum_zero]
  rw [h, rfinSum_single a (normSq v)]

def idx0 (m : Nat) : Fin (m + 2) := ⟨0, by omega⟩
def idx1 (m : Nat) : Fin (m + 2) := ⟨1, by omega⟩

theorem idx0_ne_idx1 (m : Nat) : idx0 m ≠ idx1 m := by
  intro h; have := congrArg Fin.val h; dsimp [idx0, idx1] at this; omega

/-- **Counterexample Family 1 (`J_n = I_n + E_{0,1}`, `n = m + 2 ≥ 2`):**
    Real `{0,1}` upper-triangular shear / Jordan block. -/
def realJordanBlock (R : Type u) [LinearOrderedCommRing R] (m : Nat) : RMat R (m + 2) :=
  fun i j => (if i = j then 1 else 0) + (if i = idx0 m ∧ j = idx1 m then 1 else 0)

def jordanBlock (R : Type u) [LinearOrderedCommRing R] (m : Nat) : CMat R (m + 2) :=
  addMat (eye (m + 2)) (singleMat (m + 2) (idx0 m) (idx1 m) 1)

theorem toComplex_realJordanBlock (m : Nat) :
    toComplexMat (realJordanBlock R m) = jordanBlock R m := by
  funext i j
  unfold toComplexMat realJordanBlock jordanBlock addMat eye singleMat
  rw [ofReal_add]
  congr 1
  · by_cases h : i = j <;> simp [h, ofReal_one, ofReal_zero]
  · by_cases h : i = idx0 m ∧ j = idx1 m <;> simp [h, ofReal_one, ofReal_zero]

theorem jordanBlock_upperTriangular (m : Nat) : IsUpperTriangular (jordanBlock R m) := by
  intro i j hji
  unfold jordanBlock addMat eye singleMat
  have hij : i ≠ j := fun h => by subst h; omega
  have hnot : ¬ (i = idx0 m ∧ j = idx1 m) := by
    rintro ⟨hi, hj⟩
    have hv1 := congrArg Fin.val hi
    have hv2 := congrArg Fin.val hj
    dsimp [idx0, idx1] at hv1 hv2
    omega
  rw [if_neg hij, if_neg hnot, cadd_zero]

theorem jordanBlock_hasSchurDecomp (m : Nat) :
    HasSchurDecomp (jordanBlock R m) (jordanBlock R m) (eye (m + 2)) := by
  refine ⟨eye_isUnitary _, jordanBlock_upperTriangular m, ?_⟩
  rw [adj_eye, eye_mul, mul_eye]

theorem jordanBlock_diag (m : Nat) (i : Fin (m + 2)) : jordanBlock R m i i = 1 := by
  unfold jordanBlock addMat eye singleMat
  have hnot : ¬ (i = idx0 m ∧ i = idx1 m) := fun ⟨h1, h2⟩ => idx0_ne_idx1 m (h1.symm.trans h2)
  rw [if_pos rfl, if_neg hnot, cadd_zero]

theorem jordanBlock_not_isNormal (m : Nat) : ¬ IsNormal (jordanBlock R m) := by
  intro hN
  have hd := (upperTriangular_isNormal_iff_isDiagonal (jordanBlock_upperTriangular (R := R) m)).mp hN
  have h01 := hd (idx0 m) (idx1 m) (idx0_ne_idx1 m)
  unfold jordanBlock addMat eye singleMat at h01
  rw [if_neg (idx0_ne_idx1 m), if_pos ⟨rfl, rfl⟩, czero_add] at h01
  have hre : (1 : R) = 0 := congrArg Complex.re h01
  exact ne_of_lt LinearOrderedCommRing.zero_lt_one hre.symm

theorem realJordanBlock_not_isRealNormal (m : Nat) : ¬ IsRealNormal (realJordanBlock R m) := by
  rw [isRealNormal_iff_isNormal_toComplex, toComplex_realJordanBlock]
  exact jordanBlock_not_isNormal m

theorem jordanBlock_matPow (m : Nat) : ∀ k : Nat,
    matPow (jordanBlock R m) k =
    addMat (eye (m + 2)) (singleMat (m + 2) (idx0 m) (idx1 m) (ofReal (natCast R k)))
  | 0 => by
    unfold matPow natCast
    have hz : singleMat (m + 2) (idx0 m) (idx1 m) (ofReal (0 : R)) = zeroMat (m + 2) := by
      funext i j; unfold singleMat zeroMat ofReal; by_cases h : i = idx0 m ∧ j = idx1 m <;> simp [h]; rfl
    rw [hz, addMat_zeroMat]
  | k + 1 => by
    unfold matPow
    rw [jordanBlock_matPow m k]
    unfold jordanBlock
    rw [addMat_mul, mul_addMat, mul_addMat, eye_mul, eye_mul, mul_eye,
        mul_singleMat_singleMat, if_neg (idx0_ne_idx1 m).symm, addMat_zeroMat]
    funext i j
    unfold addMat singleMat
    have hnc : ofReal (natCast R (k + 1)) = ofReal (natCast R k) + 1 := by
      change ofReal (natCast R k + 1) = ofReal (natCast R k) + 1
      rw [ofReal_add, ofReal_one]
    rw [hnc]
    by_cases h : i = idx0 m ∧ j = idx1 m
    · rw [if_pos h, if_pos h, if_pos h, cadd_assoc, cadd_comm 1 (ofReal (natCast R k))]
    · rw [if_neg h, if_neg h, if_neg h, cadd_zero]

theorem jordanBlock_frobNormSq_matPow (m : Nat) (k : Nat) :
    frobNormSq (matPow (jordanBlock R m) k) =
    natCast R (m + 2) + natCast R k * natCast R k := by
  rw [jordanBlock_matPow m k]
  have hU : IsUpperTriangular
      (addMat (eye (m + 2)) (singleMat (m + 2) (idx0 m) (idx1 m) (ofReal (natCast R k)))) := by
    intro i j hji
    unfold addMat eye singleMat
    have hij : i ≠ j := fun h => by subst h; omega
    have hnot : ¬ (i = idx0 m ∧ j = idx1 m) := by
      rintro ⟨hi, hj⟩
      have hv1 := congrArg Fin.val hi
      have hv2 := congrArg Fin.val hj
      dsimp [idx0, idx1] at hv1 hv2; omega
    rw [if_neg hij, if_neg hnot, cadd_zero]
  rw [upperTriangular_frobNormSq_decomp hU]
  have hdiag : (fun i : Fin (m + 2) =>
      normSq (addMat (eye (m + 2)) (singleMat (m + 2) (idx0 m) (idx1 m) (ofReal (natCast R k))) i i)) =
      (fun _ => (1 : R)) := by
    funext i
    unfold addMat eye singleMat
    have hnot : ¬ (i = idx0 m ∧ i = idx1 m) := fun ⟨h1, h2⟩ => idx0_ne_idx1 m (h1.symm.trans h2)
    rw [if_pos rfl, if_neg hnot, cadd_zero, normSq_one]
  have hoff : (fun i : Fin (m + 2) => finSum (fun j : Fin (m + 2) =>
      if i.val < j.val then
        normSq (addMat (eye (m + 2)) (singleMat (m + 2) (idx0 m) (idx1 m) (ofReal (natCast R k))) i j)
      else 0)) =
      (fun i : Fin (m + 2) => if i = idx0 m then natCast R k * natCast R k else 0) := by
    funext i
    by_cases hi0 : i = idx0 m
    · subst hi0
      rw [if_pos rfl]
      have hj : (fun j : Fin (m + 2) =>
          if (idx0 m).val < j.val then
            normSq (addMat (eye (m + 2))
              (singleMat (m + 2) (idx0 m) (idx1 m) (ofReal (natCast R k))) (idx0 m) j)
          else 0) =
          (fun j : Fin (m + 2) => if j = idx1 m then natCast R k * natCast R k else 0) := by
        funext j
        by_cases hj1 : j = idx1 m
        · subst hj1
          have hlt : (idx0 m).val < (idx1 m).val := by dsimp [idx0, idx1]; omega
          unfold addMat eye singleMat
          rw [if_pos hlt, if_pos rfl, if_neg (idx0_ne_idx1 m), if_pos ⟨rfl, rfl⟩,
              czero_add, normSq_ofReal]
        · rw [if_neg hj1]
          by_cases hlt : (idx0 m).val < j.val
          · unfold addMat eye singleMat
            have hij : idx0 m ≠ j := fun h => by subst h; omega
            have hnot : ¬ (idx0 m = idx0 m ∧ j = idx1 m) := fun ⟨_, h2⟩ => hj1 h2
            rw [if_pos hlt, if_neg hij, if_neg hnot, cadd_zero, normSq_zero]
          · rw [if_neg hlt]
      rw [hj, rfinSum_single (idx1 m)]
    · rw [if_neg hi0]
      have hj : (fun j : Fin (m + 2) =>
          if i.val < j.val then
            normSq (addMat (eye (m + 2))
              (singleMat (m + 2) (idx0 m) (idx1 m) (ofReal (natCast R k))) i j)
          else 0) = (fun _ => 0) := by
        funext j
        by_cases hlt : i.val < j.val
        · unfold addMat eye singleMat
          have hij : i ≠ j := fun h => by subst h; omega
          have hnot : ¬ (i = idx0 m ∧ j = idx1 m) := fun ⟨h1, _⟩ => hi0 h1
          rw [if_pos hlt, if_neg hij, if_neg hnot, cadd_zero, normSq_zero]
        · rw [if_neg hlt]
      rw [hj, rfinSum_zero]
  rw [hdiag, rfinSum_const 1 (m + 2), mul_one, hoff, rfinSum_single (idx0 m)]

theorem jordanBlock_spectralRadius (m : Nat) :
    IsSpectralRadius (fun _ : Fin (m + 2) => (1 : R)) 1 :=
  ⟨le_of_lt LinearOrderedCommRing.zero_lt_one,
   fun _ => ⟨le_of_lt LinearOrderedCommRing.zero_lt_one, le_refl 1⟩,
   fun _ => ⟨idx0 m, rfl⟩⟩

theorem jordanBlock_attains_eigModPowSum (m : Nat) (k : Nat) :
    eigModPowSum (fun _ : Fin (m + 2) => (1 : R)) k = spectralPowerBound R (m + 2) 1 k := by
  unfold eigModPowSum spectralPowerBound
  have h1 : (fun _ : Fin (m + 2) => rpow (1 : R) k) = (fun _ => (1 : R)) :=
    funext (fun _ => rpow_one_base k)
  rw [h1, rpow_one_base, rfinSum_const 1 (m + 2)]

theorem jordanBlock_attains_trace (m : Nat) (k : Nat) :
    trace (matPow (jordanBlock R m) k) = ofReal (natCast R (m + 2)) ∧
    normSq (trace (matPow (jordanBlock R m) k)) =
      natCast R (m + 2) * spectralPowerBound R (m + 2) 1 k := by
  rw [schur_trace_matPow_eq (jordanBlock_hasSchurDecomp (R := R) m) k]
  have h1 : (fun i : Fin (m + 2) => cpow (jordanBlock R m i i) k) =
            (fun _ : Fin (m + 2) => ofReal (1 : R)) := by
    funext i
    rw [jordanBlock_diag, ← ofReal_one, ← ofReal_rpow, rpow_one_base]
  rw [h1, ← ofReal_finSum, rfinSum_const 1 (m + 2), mul_one]
  refine ⟨rfl, ?_⟩
  rw [normSq_ofReal]
  unfold spectralPowerBound
  rw [rpow_one_base, mul_one]

theorem jordanBlock_exceeds_frobPowerBound (m : Nat) {k : Nat} (hk : 1 ≤ k) :
    spectralPowerBound R (m + 2) 1 (2 * k) < frobNormSq (matPow (jordanBlock R m) k) := by
  rw [jordanBlock_frobNormSq_matPow]
  unfold spectralPowerBound
  rw [rpow_one_base, mul_one]
  have hk_pos : (0 : R) < natCast R k := natCast_pos hk
  have hk2_pos : (0 : R) < natCast R k * natCast R k :=
    LinearOrderedCommRing.mul_pos _ _ hk_pos hk_pos
  have h := add_lt_add_left hk2_pos (natCast R (m + 2))
  rw [add_zero] at h
  exact h

/-- **Counterexample Family 2 (`D_n = E_{0,0} = diag(1, 0, ..., 0)`, `n = m + 2 ≥ 2`):**
    Normal rank-1 projection satisfying Schur equality yet failing `n ρ(A)^k` for all `k ≥ 1`. -/
def realDiagProj (R : Type u) [LinearOrderedCommRing R] (m : Nat) : RMat R (m + 2) :=
  fun i j => if i = idx0 m ∧ j = idx0 m then 1 else 0

def diagProj (R : Type u) [LinearOrderedCommRing R] (m : Nat) : CMat R (m + 2) :=
  singleMat (m + 2) (idx0 m) (idx0 m) 1

theorem toComplex_realDiagProj (m : Nat) :
    toComplexMat (realDiagProj R m) = diagProj R m := by
  funext i j
  unfold toComplexMat realDiagProj diagProj singleMat
  by_cases h : i = idx0 m ∧ j = idx0 m <;> simp [h, ofReal_one, ofReal_zero]

theorem diagProj_isDiagonal (m : Nat) : IsDiagonal (diagProj R m) := by
  intro i j hij
  unfold diagProj singleMat
  have hnot : ¬ (i = idx0 m ∧ j = idx0 m) := fun ⟨h1, h2⟩ => hij (h1.trans h2.symm)
  rw [if_neg hnot]

theorem diagProj_isNormal (m : Nat) : IsNormal (diagProj R m) :=
  isNormal_of_isDiagonal (diagProj_isDiagonal m)

theorem realDiagProj_isRealNormal (m : Nat) : IsRealNormal (realDiagProj R m) := by
  rw [isRealNormal_iff_isNormal_toComplex, toComplex_realDiagProj]
  exact diagProj_isNormal m

theorem diagProj_hasSchurDecomp (m : Nat) :
    HasSchurDecomp (diagProj R m) (diagProj R m) (eye (m + 2)) := by
  refine ⟨eye_isUnitary _, isUpperTriangular_of_isDiagonal (diagProj_isDiagonal m), ?_⟩
  rw [adj_eye, eye_mul, mul_eye]

theorem diagProj_schur_eq (m : Nat) :
    finSum (fun i : Fin (m + 2) => normSq (diagProj R m i i)) = frobNormSq (diagProj R m) :=
  (schur_eq_iff_isNormal (diagProj_hasSchurDecomp m)).mpr (diagProj_isNormal m)

def diagProjModuli (R : Type u) [LinearOrderedCommRing R] (m : Nat) : Fin (m + 2) → R :=
  fun i => if i = idx0 m then 1 else 0

theorem diagProj_normSq_diag (m : Nat) (i : Fin (m + 2)) :
    normSq (diagProj R m i i) = diagProjModuli R m i := by
  unfold diagProj singleMat diagProjModuli
  by_cases h : i = idx0 m
  · subst h; simp [normSq_one]
  · simp [h, normSq_zero]

theorem diagProj_spectralRadius (m : Nat) :
    IsSpectralRadius (diagProjModuli R m) 1 := by
  refine ⟨le_of_lt LinearOrderedCommRing.zero_lt_one, fun i => ?_, fun _ => ⟨idx0 m, if_pos rfl⟩⟩
  unfold diagProjModuli
  by_cases h : i = idx0 m
  · rw [if_pos h]; exact ⟨le_of_lt LinearOrderedCommRing.zero_lt_one, le_refl 1⟩
  · rw [if_neg h]; exact ⟨le_refl 0, le_of_lt LinearOrderedCommRing.zero_lt_one⟩

theorem diagProj_eigModPowSum_eq_one (m : Nat) {k : Nat} (hk : 1 ≤ k) :
    eigModPowSum (diagProjModuli R m) k = 1 := by
  unfold eigModPowSum diagProjModuli
  have h : (fun i : Fin (m + 2) => rpow (if i = idx0 m then (1 : R) else 0) k) =
           (fun i : Fin (m + 2) => if i = idx0 m then (1 : R) else 0) := by
    funext i
    by_cases hi : i = idx0 m <;> simp [hi, rpow_one_base, rpow_zero_base hk]
  rw [h, rfinSum_single (idx0 m) 1]

theorem diagProj_fails_eigModPowSum (m : Nat) {k : Nat} (hk : 1 ≤ k) :
    eigModPowSum (diagProjModuli R m) k < spectralPowerBound R (m + 2) 1 k := by
  rw [diagProj_eigModPowSum_eq_one m hk]
  unfold spectralPowerBound
  rw [rpow_one_base, mul_one]
  exact one_lt_natCast_succ_succ m

theorem diagProj_matPow (m : Nat) : ∀ {k : Nat}, 1 ≤ k → matPow (diagProj R m) k = diagProj R m
  | 0, hk => by omega
  | 1, _ => by change mul (eye (m + 2)) (diagProj R m) = diagProj R m; exact eye_mul _
  | k + 2, _ => by
    unfold matPow
    rw [diagProj_matPow m (k := k + 1) (by omega)]
    unfold diagProj
    rw [mul_singleMat_singleMat, if_pos rfl, cmul_one]

theorem diagProj_fails_trace (m : Nat) {k : Nat} (hk : 1 ≤ k) :
    normSq (trace (matPow (diagProj R m) k)) <
      natCast R (m + 2) * spectralPowerBound R (m + 2) 1 k := by
  rw [diagProj_matPow m hk]
  unfold diagProj
  rw [trace_singleMat, if_pos rfl, normSq_one]
  unfold spectralPowerBound
  rw [rpow_one_base, mul_one]
  have h1lt : (1 : R) < natCast R (m + 2) := one_lt_natCast_succ_succ m
  have hpos : (0 : R) < natCast R (m + 2) :=
    lt_trans LinearOrderedCommRing.zero_lt_one h1lt
  have hstep : (1 : R) * natCast R (m + 2) < natCast R (m + 2) * natCast R (m + 2) :=
    mul_lt_mul_of_pos_right h1lt hpos
  rw [one_mul] at hstep
  exact lt_trans h1lt hstep

theorem diagProj_fails_frobPowerBound (m : Nat) {k : Nat} (hk : 1 ≤ k) :
    frobNormSq (matPow (diagProj R m) k) < spectralPowerBound R (m + 2) 1 (2 * k) := by
  rw [diagProj_matPow m hk]
  unfold diagProj
  rw [frobNormSq_singleMat, normSq_one]
  unfold spectralPowerBound
  rw [rpow_one_base, mul_one]
  exact one_lt_natCast_succ_succ m

/-- **Counterexample Family 3 (`N_{n,c} = c E_{0,1}`, `n = m + 2 ≥ 2`, `c ≠ 0`):**
    Non-normal nilpotent matrix with `ρ = 0` violating Frobenius and ALL Schatten bounds! -/
def nilpotentBlock {R : Type u} [LinearOrderedCommRing R] (m : Nat) (c : Complex R) :
    CMat R (m + 2) :=
  singleMat (m + 2) (idx0 m) (idx1 m) c

theorem nilpotentBlock_upperTriangular (m : Nat) (c : Complex R) :
    IsUpperTriangular (nilpotentBlock m c) := by
  intro i j hji
  unfold nilpotentBlock singleMat
  have hnot : ¬ (i = idx0 m ∧ j = idx1 m) := by
    rintro ⟨hi, hj⟩
    have hv1 := congrArg Fin.val hi
    have hv2 := congrArg Fin.val hj
    dsimp [idx0, idx1] at hv1 hv2; omega
  rw [if_neg hnot]

theorem nilpotentBlock_hasSchurDecomp (m : Nat) (c : Complex R) :
    HasSchurDecomp (nilpotentBlock m c) (nilpotentBlock m c) (eye (m + 2)) := by
  refine ⟨eye_isUnitary _, nilpotentBlock_upperTriangular m c, ?_⟩
  rw [adj_eye, eye_mul, mul_eye]

theorem nilpotentBlock_diag_zero (m : Nat) (c : Complex R) (i : Fin (m + 2)) :
    nilpotentBlock m c i i = 0 := by
  unfold nilpotentBlock singleMat
  have hnot : ¬ (i = idx0 m ∧ i = idx1 m) := fun ⟨h1, h2⟩ => idx0_ne_idx1 m (h1.symm.trans h2)
  rw [if_neg hnot]

theorem nilpotentBlock_not_isNormal (m : Nat) {c : Complex R} (hc : c ≠ 0) :
    ¬ IsNormal (nilpotentBlock m c) := by
  intro hN
  have hd := (upperTriangular_isNormal_iff_isDiagonal (nilpotentBlock_upperTriangular m c)).mp hN
  have h01 := hd (idx0 m) (idx1 m) (idx0_ne_idx1 m)
  unfold nilpotentBlock singleMat at h01
  rw [if_pos ⟨rfl, rfl⟩] at h01
  exact hc h01

theorem nilpotentBlock_spectralRadius (m : Nat) :
    IsSpectralRadius (fun _ : Fin (m + 2) => (0 : R)) 0 :=
  ⟨le_refl 0, fun _ => ⟨le_refl 0, le_refl 0⟩, fun _ => ⟨idx0 m, rfl⟩⟩

theorem nilpotentBlock_exceeds_frobBound (m : Nat) {c : Complex R} (hc : c ≠ 0) :
    spectralPowerBound R (m + 2) 0 2 < frobNormSq (nilpotentBlock m c) := by
  unfold nilpotentBlock spectralPowerBound
  rw [frobNormSq_singleMat, rpow_zero_base (by decide), mul_zero]
  exact normSq_pos_of_ne_zero hc

theorem nilpotentBlock_gram_pow (m : Nat) (c : Complex R) : ∀ {k : Nat}, 1 ≤ k →
    matPow (mul (adj (nilpotentBlock m c)) (nilpotentBlock m c)) k =
    singleMat (m + 2) (idx1 m) (idx1 m) (ofReal (rpow (normSq c) k))
  | 0, hk => by omega
  | 1, _ => by
    change mul (eye (m + 2)) (mul (adj (nilpotentBlock m c)) (nilpotentBlock m c)) = _
    unfold nilpotentBlock
    rw [eye_mul, adj_singleMat, mul_singleMat_singleMat, if_pos rfl,
        conj_mul_self, rpow_succ, rpow_zero, one_mul]
  | k + 2, _ => by
    unfold matPow
    rw [nilpotentBlock_gram_pow m c (k := k + 1) (by omega)]
    unfold nilpotentBlock
    rw [adj_singleMat, mul_singleMat_singleMat, if_pos rfl, conj_mul_self,
        mul_singleMat_singleMat, if_pos rfl, ← ofReal_mul, ← rpow_succ]

/-- For ANY `k ≥ 1` and `c ≠ 0`, the singular-value `2k`-th power sum `tr((N* N)^k)` equals
    `|c|^{2k} > 0 = n ρ(N)^{2k}`! -/
theorem nilpotentBlock_exceeds_schattenBound (m : Nat) {c : Complex R} (hc : c ≠ 0)
    {k : Nat} (hk : 1 ≤ k) :
    spectralPowerBound R (m + 2) 0 (2 * k) <
      (trace (matPow (mul (adj (nilpotentBlock m c)) (nilpotentBlock m c)) k)).re := by
  rw [nilpotentBlock_gram_pow m c hk, trace_singleMat, if_pos rfl, ofReal_re]
  unfold spectralPowerBound
  rw [rpow_zero_base (by omega), mul_zero]
  exact rpow_pos (normSq_pos_of_ne_zero hc) k

theorem nilpotentBlock_attains_eigModPowSum (m : Nat) {k : Nat} (hk : 1 ≤ k) :
    eigModPowSum (fun _ : Fin (m + 2) => (0 : R)) k = spectralPowerBound R (m + 2) 0 k := by
  unfold eigModPowSum spectralPowerBound
  have h0 : (fun _ : Fin (m + 2) => rpow (0 : R) k) = (fun _ => (0 : R)) :=
    funext (fun _ => rpow_zero_base hk)
  rw [h0, rpow_zero_base hk, rfinSum_const 0 (m + 2), mul_zero]

/-- **Counterexample Family 4 (`I_n`, `n = m + 2 ≥ 2`):**
    Normal identity matrix refuting the unscaled bound `ρ(A)^k` (and `∑_{j=1}^K ρ(A)^j`)
    without the multiplicity factor `n`. -/
theorem eye_exceeds_unscaled_bound (m : Nat) (k : Nat) :
    rpow (1 : R) k < eigModPowSum (fun _ : Fin (m + 2) => (1 : R)) k := by
  unfold eigModPowSum
  have h1 : (fun _ : Fin (m + 2) => rpow (1 : R) k) = (fun _ => (1 : R)) :=
    funext (fun _ => rpow_one_base k)
  rw [h1, rpow_one_base, rfinSum_const 1 (m + 2), mul_one]
  exact one_lt_natCast_succ_succ m

end MatrixTheory

-- ============================================================================
-- §7.5. Dense Non-Triangular Unitary Conjugate Witness over Exact Rationals Q
-- ============================================================================

section DenseQFieldWitness

open RingLemmas Complex SumLemmas

/-- Exact Pythagorean unitary matrix `U = (1/5) * [[3, -4], [4, 3]]` over `Complex QField`. -/
def pythagUnitary : CMat QField 2 :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then ofReal (QField.mk 3 5 (by decide))
    else if i.val = 0 ∧ j.val = 1 then ofReal (QField.mk (-4) 5 (by decide))
    else if i.val = 1 ∧ j.val = 0 then ofReal (QField.mk 4 5 (by decide))
    else ofReal (QField.mk 3 5 (by decide))

theorem fin2_cases {P : Fin 2 → Prop} (h0 : P ⟨0, by decide⟩) (h1 : P ⟨1, by decide⟩) :
    ∀ i : Fin 2, P i := by
  intro ⟨v, hv⟩
  match v with
  | 0 => exact h0
  | 1 => exact h1

private theorem sum2_q (f : Fin 2 → Complex QField) :
    finSum f = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ := by
  unfold finSum; unfold finSum; unfold finSum; dsimp [Fin.succ]
  rw [cadd_zero]

private theorem q_add_mul_check :
    IsUnitary pythagUnitary := by
  constructor
  · funext i j
    revert j; refine fin2_cases ?_ ?_ <;> revert i <;> refine fin2_cases ?_ ?_
    all_goals
      unfold mul adj pythagUnitary eye
      rw [sum2_q]
      dsimp
      rw [conj_ofReal, conj_ofReal, ← ofReal_mul, ← ofReal_mul, ← ofReal_add,
          QField.mk_mul, QField.mk_mul, QField.mk_add]
    · change ofReal (QField.mk _ _ _) = ofReal (QField.mk 1 1 (by decide))
      congr 1; rw [QField.mk_eq_iff]; decide
    · change ofReal (QField.mk _ _ _) = ofReal (QField.mk 0 1 (by decide))
      congr 1; rw [QField.mk_eq_iff]; decide
    · change ofReal (QField.mk _ _ _) = ofReal (QField.mk 0 1 (by decide))
      congr 1; rw [QField.mk_eq_iff]; decide
    · change ofReal (QField.mk _ _ _) = ofReal (QField.mk 1 1 (by decide))
      congr 1; rw [QField.mk_eq_iff]; decide
  · funext i j
    revert j; refine fin2_cases ?_ ?_ <;> revert i <;> refine fin2_cases ?_ ?_
    all_goals
      unfold mul adj pythagUnitary eye
      rw [sum2_q]
      dsimp
      rw [conj_ofReal, conj_ofReal, ← ofReal_mul, ← ofReal_mul, ← ofReal_add,
          QField.mk_mul, QField.mk_mul, QField.mk_add]
    · change ofReal (QField.mk _ _ _) = ofReal (QField.mk 1 1 (by decide))
      congr 1; rw [QField.mk_eq_iff]; decide
    · change ofReal (QField.mk _ _ _) = ofReal (QField.mk 0 1 (by decide))
      congr 1; rw [QField.mk_eq_iff]; decide
    · change ofReal (QField.mk _ _ _) = ofReal (QField.mk 0 1 (by decide))
      congr 1; rw [QField.mk_eq_iff]; decide
    · change ofReal (QField.mk _ _ _) = ofReal (QField.mk 1 1 (by decide))
      congr 1; rw [QField.mk_eq_iff]; decide

/-- Dense non-triangular matrix `A = U J_2 U* = (1/25)[[13, 9], [-16, 37]]` over `Complex QField`. -/
def denseJordanQ : CMat QField 2 :=
  mul (mul pythagUnitary (jordanBlock QField 0)) (adj pythagUnitary)

theorem denseJordanQ_hasSchurDecomp :
    HasSchurDecomp denseJordanQ (jordanBlock QField 0) pythagUnitary :=
  ⟨q_add_mul_check, jordanBlock_upperTriangular 0, rfl⟩

theorem denseJordanQ_not_upperTriangular : ¬ IsUpperTriangular denseJordanQ := by
  intro hU
  have h10 := hU ⟨1, by decide⟩ ⟨0, by decide⟩ (by decide)
  unfold denseJordanQ mul adj pythagUnitary jordanBlock addMat eye singleMat idx0 idx1 at h10
  rw [sum2_q] at h10
  dsimp at h10
  rw [sum2_q, sum2_q] at h10
  dsimp at h10
  simp only [cadd_zero, czero_add, cmul_one, cmul_zero, conj_ofReal,
             ← ofReal_add, ← ofReal_mul, QField.mk_add, QField.mk_mul] at h10
  have hq : QField.mk _ _ _ = QField.mk 0 1 (by decide) := ofReal_inj h10
  have hint := (QField.mk_eq_iff _ _).mp hq
  omega

theorem denseJordanQ_not_isNormal_yet_attains_bounds (k : Nat) :
    HasSchurDecomp denseJordanQ (jordanBlock QField 0) pythagUnitary ∧
    ¬ IsUpperTriangular denseJordanQ ∧
    ¬ IsNormal denseJordanQ ∧
    trace (matPow denseJordanQ k) = ofReal (natCast QField 2) ∧
    normSq (trace (matPow denseJordanQ k)) =
      natCast QField 2 * spectralPowerBound QField 2 1 k := by
  have hS := denseJordanQ_hasSchurDecomp
  refine ⟨hS, denseJordanQ_not_upperTriangular, ?_, ?_, ?_⟩
  · rw [schur_isNormal_iff hS]
    exact jordanBlock_not_isNormal 0
  · rw [schur_trace_matPow_eq hS k,
        ← schur_trace_matPow_eq (jordanBlock_hasSchurDecomp (R := QField) 0) k]
    exact (jordanBlock_attains_trace (R := QField) 0 k).1
  · rw [schur_trace_matPow_eq hS k,
        ← schur_trace_matPow_eq (jordanBlock_hasSchurDecomp (R := QField) 0) k]
    exact (jordanBlock_attains_trace (R := QField) 0 k).2

end DenseQFieldWitness

-- ============================================================================
-- §8. Master Refutation Theorems Across ALL Readings & Axiom Audit
-- ============================================================================

section MasterRefutations

open RingLemmas Complex SumLemmas

/-- **Refutation of Reading 1A (Eigenvalue Modulus Power-Sum Biconditional / Both Directions):**
    For EVERY `LinearOrderedCommRing R`, EVERY dimension `n = m + 2 ≥ 2`, and EVERY power `k ≥ 1`,
    BOTH directions of `(∑_i |λ_i|^k = n ρ(A)^k ↔ IsNormal A)` are FALSE! -/
theorem refute_reading1_eigenvalue_power_sum
    {R : Type u} [LinearOrderedCommRing R] (m : Nat) {k : Nat} (hk : 1 ≤ k) :
    -- (1) Necessity fails: non-normal matrix attains the spectral-radius power-sum bound
    (∃ A T U : CMat R (m + 2), ∃ r : Fin (m + 2) → R, ∃ ρ : R,
      HasSchurDecomp A T U ∧
      (∀ i, normSq (T i i) = r i * r i) ∧
      IsSpectralRadius r ρ ∧
      eigModPowSum r k = spectralPowerBound R (m + 2) ρ k ∧
      ¬ IsNormal A) ∧
    -- (2) Sufficiency fails: normal matrix strictly fails to attain the bound
    (∃ A T U : CMat R (m + 2), ∃ r : Fin (m + 2) → R, ∃ ρ : R,
      HasSchurDecomp A T U ∧
      (∀ i, normSq (T i i) = r i * r i) ∧
      IsSpectralRadius r ρ ∧
      IsNormal A ∧
      eigModPowSum r k ≠ spectralPowerBound R (m + 2) ρ k) ∧
    -- (3) Consequently, the conjectured biconditional characterization is FALSE
    ¬ (∀ (A T U : CMat R (m + 2)) (r : Fin (m + 2) → R) (ρ : R),
        HasSchurDecomp A T U →
        (∀ i, normSq (T i i) = r i * r i) →
        IsSpectralRadius r ρ →
        (eigModPowSum r k = spectralPowerBound R (m + 2) ρ k ↔ IsNormal A)) := by
  have h1 : ∃ A T U : CMat R (m + 2), ∃ r : Fin (m + 2) → R, ∃ ρ : R,
      HasSchurDecomp A T U ∧
      (∀ i, normSq (T i i) = r i * r i) ∧
      IsSpectralRadius r ρ ∧
      eigModPowSum r k = spectralPowerBound R (m + 2) ρ k ∧
      ¬ IsNormal A := by
    refine ⟨jordanBlock R m, jordanBlock R m, eye (m + 2), (fun _ => 1), 1,
            jordanBlock_hasSchurDecomp m, ?_, jordanBlock_spectralRadius m,
            jordanBlock_attains_eigModPowSum m k, jordanBlock_not_isNormal m⟩
    intro i; rw [jordanBlock_diag, normSq_one, one_mul]
  have h2 : ∃ A T U : CMat R (m + 2), ∃ r : Fin (m + 2) → R, ∃ ρ : R,
      HasSchurDecomp A T U ∧
      (∀ i, normSq (T i i) = r i * r i) ∧
      IsSpectralRadius r ρ ∧
      IsNormal A ∧
      eigModPowSum r k ≠ spectralPowerBound R (m + 2) ρ k := by
    refine ⟨diagProj R m, diagProj R m, eye (m + 2), diagProjModuli R m, 1,
            diagProj_hasSchurDecomp m, ?_, diagProj_spectralRadius m,
            diagProj_isNormal m, ne_of_lt (diagProj_fails_eigModPowSum m hk)⟩
    intro i
    rw [diagProj_normSq_diag]
    unfold diagProjModuli
    by_cases hi : i = idx0 m
    · rw [if_pos hi, mul_one]
    · rw [if_neg hi, mul_zero]
  refine ⟨h1, h2, ?_⟩
  intro hconj
  rcases h1 with ⟨A, T, U, r, ρ, hS, hmod, hρ, heq, hnotN⟩
  exact hnotN ((hconj A T U r ρ hS hmod hρ).mp heq)

/-- **Refutation of Reading 1B (Trace Power-Sum Bound `|tr(A^k)|^2 ≤ n^2 (ρ^2)^k`):**
    Both directions of normality characterization fail for ALL `n = m + 2 ≥ 2` and `k ≥ 1`. -/
theorem refute_reading1_trace_power_sum
    {R : Type u} [LinearOrderedCommRing R] (m : Nat) {k : Nat} (hk : 1 ≤ k) :
    -- Both necessity (`→ IsNormal`) and sufficiency (`IsNormal →`) fail, hence `↔` fails:
    ¬ (∀ (A T U : CMat R (m + 2)) (ρSq : R),
        HasSchurDecomp A T U →
        IsSpectralRadius (fun i => normSq (T i i)) ρSq →
        IsNormal A →
        normSq (trace (matPow A k)) = natCast R (m + 2) * spectralPowerBound R (m + 2) ρSq k) ∧
    ¬ (∀ (A T U : CMat R (m + 2)) (ρSq : R),
        HasSchurDecomp A T U →
        IsSpectralRadius (fun i => normSq (T i i)) ρSq →
        (normSq (trace (matPow A k)) = natCast R (m + 2) * spectralPowerBound R (m + 2) ρSq k ↔
         IsNormal A)) := by
  constructor
  · intro hsuff
    have hS := diagProj_hasSchurDecomp (R := R) m
    have hdiag : (fun i : Fin (m + 2) => normSq (diagProj R m i i)) = diagProjModuli R m :=
      funext (diagProj_normSq_diag m)
    have hρ : IsSpectralRadius (fun i => normSq (diagProj R m i i)) 1 := by
      rw [hdiag]; exact diagProj_spectralRadius m
    have heq := hsuff (diagProj R m) (diagProj R m) (eye (m + 2)) 1 hS hρ (diagProj_isNormal m)
    exact ne_of_lt (diagProj_fails_trace m hk) heq
  · intro hconj
    have hS := jordanBlock_hasSchurDecomp (R := R) m
    have hdiag : (fun i : Fin (m + 2) => normSq (jordanBlock R m i i)) = (fun _ => (1 : R)) := by
      funext i; rw [jordanBlock_diag, normSq_one]
    have hρ : IsSpectralRadius (fun i => normSq (jordanBlock R m i i)) 1 := by
      rw [hdiag]; exact jordanBlock_spectralRadius m
    have hN := (hconj (jordanBlock R m) (jordanBlock R m) (eye (m + 2)) 1 hS hρ).mp
                 (jordanBlock_attains_trace m k).2
    exact jordanBlock_not_isNormal m hN

/-- **Refutation of Reading 2 (Frobenius & Singular-Value / Schatten Power-Sum Bounds):**
    Bounding `‖A^k‖_F^2` or `tr((A* A)^k)` above by `n ρ(A)^{2k}` is FALSE for ALL `n = m + 2 ≥ 2`
    and ALL `k ≥ 1` (violated both by Jordan blocks with `ρ = 1` and by nilpotent matrices with `ρ = 0`). -/
theorem refute_reading2_frobenius_and_schatten
    {R : Type u} [LinearOrderedCommRing R] (m : Nat) {k : Nat} (hk : 1 ≤ k) :
    -- (1) Frobenius matrix-power bound `‖A^k‖_F^2 ≤ n (ρ^2)^k` is FALSE
    ¬ (∀ (A T U : CMat R (m + 2)) (ρSq : R),
        HasSchurDecomp A T U →
        IsSpectralRadius (fun i => normSq (T i i)) ρSq →
        frobNormSq (matPow A k) ≤ spectralPowerBound R (m + 2) ρSq k) ∧
    -- (2) Singular-value / Schatten `2k`-th power bound `tr((A* A)^k) ≤ n (ρ^2)^k` is FALSE
    ¬ (∀ (A T U : CMat R (m + 2)) (ρSq : R),
        HasSchurDecomp A T U →
        IsSpectralRadius (fun i => normSq (T i i)) ρSq →
        (trace (matPow (mul (adj A) A) k)).re ≤ spectralPowerBound R (m + 2) ρSq k) := by
  constructor
  · intro hfrob
    have hS := jordanBlock_hasSchurDecomp (R := R) m
    have hdiag : (fun i : Fin (m + 2) => normSq (jordanBlock R m i i)) = (fun _ => (1 : R)) := by
      funext i; rw [jordanBlock_diag, normSq_one]
    have hρ : IsSpectralRadius (fun i => normSq (jordanBlock R m i i)) 1 := by
      rw [hdiag]; exact jordanBlock_spectralRadius m
    have hle := hfrob (jordanBlock R m) (jordanBlock R m) (eye (m + 2)) 1 hS hρ
    have hgt : spectralPowerBound R (m + 2) 1 k < frobNormSq (matPow (jordanBlock R m) k) := by
      have := jordanBlock_exceeds_frobPowerBound (R := R) m hk
      unfold spectralPowerBound at this ⊢
      rw [rpow_one_base] at this ⊢
      exact this
    exact (lt_iff_le_not_le.mp hgt).2 hle
  · intro hsch
    have hc : (1 : Complex R) ≠ 0 := by
      intro h0
      exact ne_of_lt LinearOrderedCommRing.zero_lt_one (congrArg Complex.re h0).symm
    have hS := nilpotentBlock_hasSchurDecomp (R := R) m 1
    have hdiag : (fun i : Fin (m + 2) => normSq (nilpotentBlock (R := R) m 1 i i)) =
                 (fun _ => (0 : R)) := by
      funext i; rw [nilpotentBlock_diag_zero, normSq_zero]
    have hρ : IsSpectralRadius (fun i => normSq (nilpotentBlock (R := R) m 1 i i)) 0 := by
      rw [hdiag]; exact nilpotentBlock_spectralRadius m
    have hle := hsch (nilpotentBlock m 1) (nilpotentBlock m 1) (eye (m + 2)) 0 hS hρ
    have hgt : spectralPowerBound R (m + 2) 0 k <
        (trace (matPow (mul (adj (nilpotentBlock (R := R) m 1)) (nilpotentBlock m 1)) k)).re := by
      have := nilpotentBlock_exceeds_schattenBound (R := R) m hc hk
      unfold spectralPowerBound at this ⊢
      rw [rpow_zero_base (k := 2 * k) (by omega)] at this
      rw [rpow_zero_base hk]
      exact this
    exact (lt_iff_le_not_le.mp hgt).2 hle

/-- **Refutation of Reading 3 (Multi-Exponent Sums & Unscaled Spectral-Radius Sums):**
    For ALL `n = m + 2 ≥ 2` and `K ≥ 1`:
    (1) Scaled multi-exponent sums `∑_{j=1}^K ∑_i r_i^j = ∑_{j=1}^K n ρ^j` fail normality characterization;
    (2) Unscaled sums `∑_{j=1}^K ∑_i r_i^j ≤ ∑_{j=1}^K ρ^j` fail as an upper bound on `I_n`. -/
theorem refute_reading3_multi_exponent_and_unscaled
    {R : Type u} [LinearOrderedCommRing R] (m K : Nat) :
    -- (1) Scaled multi-exponent sum over `j = 1..K+1` is attained by non-normal `J_n`
    (finSum (fun j : Fin (K + 1) => eigModPowSum (fun _ : Fin (m + 2) => (1 : R)) (j.val + 1)) =
       finSum (fun j : Fin (K + 1) => spectralPowerBound R (m + 2) 1 (j.val + 1)) ∧
     ¬ IsNormal (jordanBlock R m)) ∧
    -- (2) Unscaled multi-exponent bound `≤ ∑_{j=1}^{K+1} ρ^j` is strictly exceeded by normal `I_n`
    (finSum (fun j : Fin (K + 1) => rpow (1 : R) (j.val + 1)) <
       finSum (fun j : Fin (K + 1) => eigModPowSum (fun _ : Fin (m + 2) => (1 : R)) (j.val + 1)) ∧
     IsNormal (eye (R := R) (m + 2))) := by
  refine ⟨⟨?_, jordanBlock_not_isNormal m⟩, ⟨?_, eye_isNormal (m + 2)⟩⟩
  · congr 1; funext j; exact jordanBlock_attains_eigModPowSum m (j.val + 1)
  · have hlhs : (fun j : Fin (K + 1) => rpow (1 : R) (j.val + 1)) = (fun _ => (1 : R)) :=
      funext (fun j => rpow_one_base _)
    have hrhs : (fun j : Fin (K + 1) => eigModPowSum (fun _ : Fin (m + 2) => (1 : R)) (j.val + 1)) =
                (fun _ => natCast R (m + 2)) := by
      funext j
      unfold eigModPowSum
      have h1 : (fun _ : Fin (m + 2) => rpow (1 : R) (j.val + 1)) = (fun _ => (1 : R)) :=
        funext (fun _ => rpow_one_base _)
      rw [h1, rfinSum_const 1 (m + 2), mul_one]
    rw [hlhs, hrhs, rfinSum_const 1 (K + 1), rfinSum_const (natCast R (m + 2)) (K + 1), mul_one]
    have hK_pos : (0 : R) < natCast R (K + 1) := natCast_pos (by omega)
    have h1lt : (1 : R) < natCast R (m + 2) := one_lt_natCast_succ_succ m
    have hmul := mul_lt_mul_of_pos_right h1lt hK_pos
    rw [one_mul, mul_comm (natCast R (m + 2))] at hmul
    exact hmul

/-- **Headline Concrete Theorem over Exact Rationals `QField` (`Q` and `Q(i)`):**
    Simultaneously packages the positive `n x n` Schur normality theorem and the complete
    refutation of Conjecture 00000007168 across every natural reading over `LinearOrderedField`. -/
theorem conjecture_00000007168_complete_resolution :
    -- Positive benchmark: Classical Schur's inequality & normality characterization (all n)
    (∀ (n : Nat) (A T U : CMat QField n),
      HasSchurDecomp A T U →
        finSum (fun i : Fin n => normSq (T i i)) ≤ frobNormSq A ∧
        (finSum (fun i : Fin n => normSq (T i i)) = frobNormSq A ↔ IsNormal A)) ∧
    -- Refutation of Reading 1A (eigenvalue power sums vs normality, all n ≥ 2, k ≥ 1)
    (∀ (m k : Nat), 1 ≤ k →
      ¬ (∀ (A T U : CMat QField (m + 2)) (r : Fin (m + 2) → QField) (ρ : QField),
          HasSchurDecomp A T U →
          (∀ i, normSq (T i i) = r i * r i) →
          IsSpectralRadius r ρ →
          (eigModPowSum r k = spectralPowerBound QField (m + 2) ρ k ↔ IsNormal A))) ∧
    -- Refutation of Reading 1B (trace power sums vs normality, all n ≥ 2, k ≥ 1)
    (∀ (m k : Nat), 1 ≤ k →
      ¬ (∀ (A T U : CMat QField (m + 2)) (ρSq : QField),
          HasSchurDecomp A T U →
          IsSpectralRadius (fun i => normSq (T i i)) ρSq →
          (normSq (trace (matPow A k)) =
            natCast QField (m + 2) * spectralPowerBound QField (m + 2) ρSq k ↔ IsNormal A))) ∧
    -- Refutation of Reading 2 (Frobenius & Schatten spectral-radius bounds, all n ≥ 2, k ≥ 1)
    (∀ (m k : Nat), 1 ≤ k →
      ¬ (∀ (A T U : CMat QField (m + 2)) (ρSq : QField),
          HasSchurDecomp A T U →
          IsSpectralRadius (fun i => normSq (T i i)) ρSq →
          frobNormSq (matPow A k) ≤ spectralPowerBound QField (m + 2) ρSq k) ∧
      ¬ (∀ (A T U : CMat QField (m + 2)) (ρSq : QField),
          HasSchurDecomp A T U →
          IsSpectralRadius (fun i => normSq (T i i)) ρSq →
          (trace (matPow (mul (adj A) A) k)).re ≤ spectralPowerBound QField (m + 2) ρSq k)) ∧
    -- Dense non-triangular unitary-conjugate witness over Q(i)
    (∀ k : Nat,
      HasSchurDecomp denseJordanQ (jordanBlock QField 0) pythagUnitary ∧
      ¬ IsUpperTriangular denseJordanQ ∧
      ¬ IsNormal denseJordanQ ∧
      trace (matPow denseJordanQ k) = ofReal (natCast QField 2) ∧
      normSq (trace (matPow denseJordanQ k)) =
        natCast QField 2 * spectralPowerBound QField 2 1 k) :=
  ⟨fun _ _ _ _ hS => ⟨schur_inequality hS, schur_eq_iff_isNormal hS⟩,
   fun m _ hk => (refute_reading1_eigenvalue_power_sum (R := QField) m hk).2.2,
   fun m _ hk => (refute_reading1_trace_power_sum (R := QField) m hk).2,
   fun m _ hk => refute_reading2_frobenius_and_schatten (R := QField) m hk,
   denseJordanQ_not_isNormal_yet_attains_bounds⟩

end MasterRefutations

end Conjecture00000007168

-- ============================================================================
-- Axiom Verification (Standard Lean 4 Core Foundations Only)
-- ============================================================================

#print axioms Conjecture00000007168.schur_inequality
#print axioms Conjecture00000007168.schur_eq_iff_isNormal
#print axioms Conjecture00000007168.eigModPowSum_eq_iff_equal_moduli
#print axioms Conjecture00000007168.normal_frobNormSq_matPow_le
#print axioms Conjecture00000007168.refute_reading1_eigenvalue_power_sum
#print axioms Conjecture00000007168.refute_reading1_trace_power_sum
#print axioms Conjecture00000007168.refute_reading2_frobenius_and_schatten
#print axioms Conjecture00000007168.refute_reading3_multi_exponent_and_unscaled
#print axioms Conjecture00000007168.conjecture_00000007168_complete_resolution


