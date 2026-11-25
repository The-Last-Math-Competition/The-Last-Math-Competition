/-
Conjecture 00000007172 — Complete Formal Analysis and Disproof in Core Lean 4.19.0
==================================================================================

Source statement (`SOURCE.md`):
  English: "Definition: Akemann-Weaver with the product bounds of singular values.
            Conjecture: The quantum version of the product inequality holds, and the
            saturation of the version is maximal entanglement.
            (maximally-entangled AW quantum saturation)"
  Chinese: "定义：Akemann–Weaver：奇异值的乘积界。猜想：AW 的量子化：乘积不等式的量子版本
            且本的饱和为最大纠缠。（Akemann-Weaver 最大纠缠量子乘积饱和）"

Summary of Formalized Results (Core Lean 4.19.0, zero external dependencies, zero sorry):
  1. Ordered Algebraic & Exact Rational Foundations (§1):
     - Polymorphic `LinearOrderedCommRing R` and `LinearOrderedField F`, together with
       constructive verified instances `LinearOrderedCommRing Int` and exact rationals
       `LinearOrderedField QField` (proving non-vacuity of all field-level theorems),
       plus the canonical ordered-ring homomorphism `ofInt : Int → R`.
  2. Finite Sums, Products, and General-N Lagrange / Cauchy-Schwarz (§2):
     - Exact inductive Lagrange identity over any `LinearOrderedCommRing R`, yielding
       both `cauchy_schwarz_sq : sq (dot u v) ≤ normSq u * normSq v` and the collinearity
       equality characterization `cauchy_schwarz_eq_iff_collinear`.
  3. Matrix Algebra, Operator Singular-Value Bounds, & Orthogonal Invariance (§3):
     - General-N operator-norm (top singular value squared) submultiplicativity
       `opNormSqBound_matMul` (`σ₁(XY)² ≤ σ₁(X)² σ₁(Y)²`) and Frobenius bound
       `opNormSqBound_frobSq` (`σ₁(X)² ≤ ‖X‖_F²`).
     - Exact rank-1 pure-state projection product theorem `rankOneProj_prod_singValSq`
       and exact coincidence characterization `rankOneProj_prod_saturated_iff_eq`:
       `σ₁(P_ψ P_φ)² = ⟨ψ, φ⟩² ≤ 1 = σ₁(P_ψ)² σ₁(P_φ)²`, with equality iff `P_ψ = P_φ`
       (state coincidence, completely independent of entanglement).
     - Global orthogonal conjugation invariance `conjBy_hasTopSingValSq_iff`, preserving
       products, arbitrary POVM subset sums, and exact singular-value bounds.
  4. Bipartite Entanglement & Complete Resolution of Schmidt Partial Products (§4):
     - Constructive general-d AM-GM inequality and equality characterization (`am_gm`,
       `am_gm_eq_iff`) proved from scratch over any `LinearOrderedField F`.
     - Positive Theorem (`schmidt_full_product_max_iff_maximally_entangled`): for every
       `d ≥ 1`, the full d-fold squared Schmidt singular-value product satisfies
       `∏_{i=0}^{d-1} w_i ≤ (1/d)^d`, with equality iff `∀ i, w_i = 1/d` (maximal entanglement).
     - Complete Refutation for Proper Partial Products (`schmidt_proper_partial_product_refutation`):
       for all `d ≥ 2` and `1 ≤ k < d`, `∏_{j=0}^{k-1} w_j ≤ (1/k)^k` holds universally,
       is saturated by the non-maximally-entangled Schmidt-rank-k state `w^(k)`, and
       strictly fails on the maximally entangled state (`(1/d)^k < (1/k)^k`), which at
       `k = 1` achieves the global minimum `1/d < 1` rather than the maximum `1`.
  5. Exact Rational Counterexamples Across Operator, Akemann-Weaver POVM, & Marginal Models (§5–§6):
     - Rational orthogonal entangler `qEnt F ∈ O_4(F)` mapping the unentangled product
       basis bijectively onto an orthonormal basis of maximally entangled states, refuting
       maximal-entanglement saturation for Akemann-Weaver POVM subset-sum bounds.
     - Explicit unentangled product state `P00` and invertible diagonal product operator
       `Y_prod = diag(2,1) ⊗ diag(4,1)` saturating singular-value product bounds.
     - Explicit rational maximally entangled witnesses strictly failing saturation:
       * Orthogonal ME projections `P_β0, P_β1` (`0 < 1`);
       * Non-orthogonal, non-commuting ME projections `P_ψ1, P_ψ2` (`9/25 < 1`);
       * Full-rank invertible ME-eigenbasis operators `X1_me, X2_me` failing top and
         partial singular-value product bounds (`64 < 4096`);
       * Non-commuting invertible ME-principal-eigenvector pair `Xt1_me, Xt2_me`
         (`‖Xt1_me Xt2_me‖_op² ≤ ‖Xt1_me Xt2_me‖_F² = 115 < 256 = σ₁(Xt1_me)² σ₁(Xt2_me)²`);
       * Kronecker tensor-product upper-bound failure (`64 > 16` at `d = 2, k = 2`) and
         quantum marginal spectrum incomparability (`1 > 1/16` at `k = 1`).
-/

universe u

namespace Conjecture00000007172

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

instance {R : Type u} [LinearOrderedCommRing R] :
    Trans (α := R) (· ≤ ·) (· ≤ ·) (· ≤ ·) :=
  ⟨LinearOrderedCommRing.le_trans _ _ _⟩

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

abbrev QField := Quotient RawRat.setoid

namespace QField

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
    refine Quotient.inductionOn a fun p hne => Quotient.sound ?_
    change RawRat.rel (RawRat.mul p (RawRat.inv p)) RawRat.one
    by_cases hpos : 0 < p.num
    · unfold RawRat.inv RawRat.mul RawRat.rel RawRat.one
      simp [hpos, Int.mul_comm]
    · by_cases hneg : p.num < 0
      · unfold RawRat.inv RawRat.mul RawRat.rel RawRat.one
        simp [hpos, hneg]
        rw [Int.mul_neg, Int.mul_neg, Int.mul_comm]
      · exfalso; apply hne; apply Quotient.sound
        change RawRat.rel p RawRat.zero
        unfold RawRat.rel RawRat.zero; dsimp; omega

end QField

-- ============================================================================
-- §1b. Ring & Field Arithmetic Helpers and Canonical Int Homomorphism
-- ============================================================================

section RingLemmas
variable {R : Type u} [LinearOrderedCommRing R]

theorem add_assoc (a b c : R) : a + b + c = a + (b + c) := LinearOrderedCommRing.add_assoc a b c
theorem add_comm (a b : R) : a + b = b + a := LinearOrderedCommRing.add_comm a b
theorem zero_add (a : R) : 0 + a = a := LinearOrderedCommRing.zero_add a
theorem add_zero (a : R) : a + 0 = a := LinearOrderedCommRing.add_zero a
theorem neg_add_cancel (a : R) : -a + a = 0 := LinearOrderedCommRing.neg_add_cancel a
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
theorem add_le_add_left {a b : R} (h : a ≤ b) (c : R) : c + a ≤ c + b := LinearOrderedCommRing.add_le_add_left a b h c
theorem mul_nonneg {a b : R} : 0 ≤ a → 0 ≤ b → 0 ≤ a * b := LinearOrderedCommRing.mul_nonneg a b
theorem mul_pos {a b : R} : 0 < a → 0 < b → 0 < a * b := LinearOrderedCommRing.mul_pos a b
theorem zero_lt_one : (0 : R) < 1 := LinearOrderedCommRing.zero_lt_one

theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  calc b = 0 + b := (zero_add b).symm
    _ = (-a + a) + b := by rw [neg_add_cancel]
    _ = -a + (a + b) := add_assoc _ _ _
    _ = -a + (a + c) := by rw [h]
    _ = (-a + a) + c := (add_assoc _ _ _).symm
    _ = 0 + c := by rw [neg_add_cancel]
    _ = c := zero_add c

theorem add_right_cancel {a b c : R} (h : a + c = b + c) : a = b := by
  apply add_left_cancel (a := c)
  rw [add_comm c a, add_comm c b, h]

theorem mul_zero (a : R) : a * 0 = 0 := by
  apply add_left_cancel (a := a * 0)
  rw [← left_distrib, add_zero, add_zero]

theorem zero_mul (a : R) : 0 * a = 0 := by rw [mul_comm, mul_zero]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  apply add_left_cancel (a := a)
  rw [add_neg_cancel, h]

theorem neg_zero : -(0 : R) = 0 := neg_eq_of_add_eq_zero (add_zero 0)

theorem neg_neg (a : R) : -(-a) = a := neg_eq_of_add_eq_zero (neg_add_cancel a)

theorem neg_add (a b : R) : -(a + b) = -a + -b := by
  apply neg_eq_of_add_eq_zero
  calc (a + b) + (-a + -b)
      = a + (b + (-b + -a)) := by rw [add_comm (-a) (-b), add_assoc]
    _ = a + (0 + -a) := by rw [← add_assoc b (-b) (-a), add_neg_cancel]
    _ = a + -a := by rw [zero_add]
    _ = 0 := add_neg_cancel a

theorem mul_neg (a b : R) : a * -b = -(a * b) := by
  apply (neg_eq_of_add_eq_zero ?_).symm
  rw [← left_distrib, add_neg_cancel, mul_zero]

theorem neg_mul (a b : R) : -a * b = -(a * b) := by
  rw [mul_comm, mul_neg, mul_comm]

theorem neg_mul_neg (a b : R) : -a * -b = a * b := by
  rw [neg_mul, mul_neg, neg_neg]

theorem mul_sub (a b c : R) : a * (b - c) = a * b - a * c := by
  rw [sub_eq_add_neg, left_distrib, mul_neg, ← sub_eq_add_neg]

theorem sub_mul (a b c : R) : (a - b) * c = a * c - b * c := by
  rw [sub_eq_add_neg, right_distrib, neg_mul, ← sub_eq_add_neg]

theorem sub_self (a : R) : a - a = 0 := by rw [sub_eq_add_neg, add_neg_cancel]

theorem sub_zero (a : R) : a - 0 = a := by rw [sub_eq_add_neg, neg_zero, add_zero]

theorem add_sub_cancel (a b : R) : a + b - b = a := by
  rw [sub_eq_add_neg, add_assoc, add_neg_cancel, add_zero]

theorem sub_add_cancel (a b : R) : a - b + b = a := by
  rw [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero]

theorem add_le_add_right {a b : R} (h : a ≤ b) (c : R) : a + c ≤ b + c := by
  rw [add_comm a c, add_comm b c]; exact add_le_add_left h c

theorem add_le_add {a b c d : R} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  le_trans (add_le_add_right h1 c) (add_le_add_left h2 b)

theorem sub_nonneg_of_le {a b : R} (h : a ≤ b) : 0 ≤ b - a := by
  have h1 := add_le_add_right h (-a)
  rw [add_neg_cancel, ← sub_eq_add_neg] at h1
  exact h1

theorem le_of_sub_nonneg {a b : R} (h : 0 ≤ b - a) : a ≤ b := by
  have h1 := add_le_add_right h a
  rw [zero_add, sub_add_cancel] at h1
  exact h1

theorem lt_irrefl (a : R) : ¬ a < a := fun h => (lt_iff_le_not_le.mp h).2 (le_refl a)

theorem ne_of_lt {a b : R} (h : a < b) : a ≠ b := fun heq => by rw [heq] at h; exact lt_irrefl b h

theorem ne_of_gt {a b : R} (h : b < a) : a ≠ b := fun heq => by rw [heq] at h; exact lt_irrefl b h

theorem le_of_lt {a b : R} (h : a < b) : a ≤ b := (lt_iff_le_not_le.mp h).1

theorem lt_of_le_of_ne {a b : R} (hle : a ≤ b) (hne : a ≠ b) : a < b :=
  lt_iff_le_not_le.mpr ⟨hle, fun hba => hne (le_antisymm hle hba)⟩

theorem lt_of_lt_of_le {a b c : R} (hab : a < b) (hbc : b ≤ c) : a < c := by
  rcases lt_iff_le_not_le.mp hab with ⟨h1, h2⟩
  exact lt_iff_le_not_le.mpr ⟨le_trans h1 hbc, fun hca => h2 (le_trans hbc hca)⟩

theorem lt_of_le_of_lt {a b c : R} (hab : a ≤ b) (hbc : b < c) : a < c := by
  rcases lt_iff_le_not_le.mp hbc with ⟨h1, h2⟩
  exact lt_iff_le_not_le.mpr ⟨le_trans hab h1, fun hca => h2 (le_trans hca hab)⟩

theorem lt_trans {a b c : R} (hab : a < b) (hbc : b < c) : a < c :=
  lt_of_lt_of_le hab (le_of_lt hbc)

theorem zero_le_one : (0 : R) ≤ 1 := le_of_lt zero_lt_one

theorem one_ne_zero : (1 : R) ≠ 0 := ne_of_gt zero_lt_one

theorem neg_nonneg_of_nonpos {a : R} (h : a ≤ 0) : 0 ≤ -a := by
  have h1 := sub_nonneg_of_le h
  rw [sub_eq_add_neg, zero_add] at h1
  exact h1

theorem neg_pos_of_neg {a : R} (h : a < 0) : 0 < -a := by
  rcases lt_iff_le_not_le.mp h with ⟨hle, hnot⟩
  refine lt_iff_le_not_le.mpr ⟨neg_nonneg_of_nonpos hle, fun hle0 => hnot ?_⟩
  have h2 := add_le_add_right hle0 a
  rw [neg_add_cancel, zero_add] at h2
  exact h2

def sq (a : R) : R := a * a

theorem sq_nonneg (a : R) : 0 ≤ sq a := by
  unfold sq
  cases le_total 0 a with
  | inl ha => exact mul_nonneg ha ha
  | inr ha =>
    have hna := neg_nonneg_of_nonpos ha
    rw [← neg_mul_neg a a]
    exact mul_nonneg hna hna

theorem sq_pos_of_ne_zero {a : R} (ha : a ≠ 0) : 0 < sq a := by
  unfold sq
  cases le_total 0 a with
  | inl hge =>
    have hgt : 0 < a := lt_of_le_of_ne hge ha.symm
    exact mul_pos hgt hgt
  | inr hle =>
    have hlt : a < 0 := lt_of_le_of_ne hle ha
    have hpos := neg_pos_of_neg hlt
    rw [← neg_mul_neg a a]
    exact mul_pos hpos hpos

theorem sq_eq_zero_iff {a : R} : sq a = 0 ↔ a = 0 := by
  constructor
  · intro h
    by_cases ha : a = 0
    · exact ha
    · exfalso; exact ne_of_gt (sq_pos_of_ne_zero ha) h
  · intro h; rw [h]; unfold sq; exact mul_zero 0

theorem mul_le_mul_of_nonneg_left {a b c : R} (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by
  apply le_of_sub_nonneg
  rw [← mul_sub]
  exact mul_nonneg hc (sub_nonneg_of_le h)

theorem mul_le_mul_of_nonneg_right {a b c : R} (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  rw [mul_comm a c, mul_comm b c]; exact mul_le_mul_of_nonneg_left h hc

theorem mul_le_mul_nonneg {a b c d : R} (h1 : a ≤ b) (h2 : c ≤ d) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    a * c ≤ b * d :=
  le_trans (mul_le_mul_of_nonneg_left h2 ha) (mul_le_mul_of_nonneg_right h1 hd)

def rpow (a : R) : Nat → R
  | 0 => 1
  | n + 1 => rpow a n * a

theorem rpow_zero (a : R) : rpow a 0 = 1 := rfl
theorem rpow_one (a : R) : rpow a 1 = a := one_mul a
theorem rpow_succ (a : R) (n : Nat) : rpow a (n + 1) = rpow a n * a := rfl

theorem rpow_nonneg {a : R} (ha : 0 ≤ a) : ∀ n : Nat, 0 ≤ rpow a n
  | 0 => zero_le_one
  | n + 1 => mul_nonneg (rpow_nonneg ha n) ha

theorem rpow_pos {a : R} (ha : 0 < a) : ∀ n : Nat, 0 < rpow a n
  | 0 => zero_lt_one
  | n + 1 => mul_pos (rpow_pos ha n) ha

theorem rpow_mul (a b : R) : ∀ n : Nat, rpow (a * b) n = rpow a n * rpow b n
  | 0 => (one_mul 1).symm
  | n + 1 => by
    calc rpow (a * b) (n + 1)
        = (rpow a n * rpow b n) * (a * b) := by rw [rpow_succ, rpow_mul a b n]
      _ = (rpow a n * a) * (rpow b n * b) := by
          rw [mul_assoc, ← mul_assoc (rpow b n) a b, mul_comm (rpow b n) a,
              mul_assoc a (rpow b n) b, ← mul_assoc]
      _ = rpow a (n + 1) * rpow b (n + 1) := rfl

theorem rpow_le_rpow {a b : R} (ha : 0 ≤ a) (hab : a ≤ b) : ∀ n : Nat, rpow a n ≤ rpow b n
  | 0 => le_refl 1
  | n + 1 => mul_le_mul_nonneg (rpow_le_rpow ha hab n) hab (rpow_nonneg ha n) (le_trans ha hab)

theorem rpow_lt_rpow {a b : R} (ha : 0 ≤ a) (hab : a < b) : ∀ n : Nat, 1 ≤ n → rpow a n < rpow b n
  | 0, h => by omega
  | 1, _ => by rw [rpow_one, rpow_one]; exact hab
  | n + 2, _ => by
    have ih := rpow_lt_rpow ha hab (n + 1) (by omega)
    have hbpos : 0 < b := lt_of_le_of_lt ha hab
    have h1 : rpow a (n + 1) * a ≤ rpow a (n + 1) * b :=
      mul_le_mul_of_nonneg_left (le_of_lt hab) (rpow_nonneg ha (n + 1))
    have h2 : rpow a (n + 1) * b < rpow b (n + 1) * b := by
      apply lt_iff_le_not_le.mpr
      refine ⟨mul_le_mul_of_nonneg_right (le_of_lt ih) (le_of_lt hbpos), fun hle => ?_⟩
      have hdiff : 0 < (rpow b (n + 1) - rpow a (n + 1)) * b := by
        apply mul_pos _ hbpos
        rcases lt_iff_le_not_le.mp ih with ⟨ih1, ih2⟩
        refine lt_iff_le_not_le.mpr ⟨sub_nonneg_of_le ih1, fun hz => ih2 ?_⟩
        have h3 := add_le_add_right hz (rpow a (n + 1))
        rw [sub_add_cancel, zero_add] at h3; exact h3
      rw [sub_mul] at hdiff
      exact (lt_iff_le_not_le.mp hdiff).2 (by
        have h5 := add_le_add hle (le_refl (-(rpow a (n + 1) * b)))
        rw [add_neg_cancel, ← sub_eq_add_neg] at h5
        exact h5)
    exact lt_of_le_of_lt h1 h2

def natCast (R : Type u) [LinearOrderedCommRing R] : Nat → R
  | 0 => 0
  | n + 1 => natCast R n + 1

theorem natCast_zero : natCast R 0 = 0 := rfl
theorem natCast_one : natCast R 1 = 1 := zero_add 1
theorem natCast_succ (n : Nat) : natCast R (n + 1) = natCast R n + 1 := rfl

theorem natCast_add (m : Nat) : ∀ n : Nat, natCast R (m + n) = natCast R m + natCast R n
  | 0 => (add_zero _).symm
  | n + 1 => by
    change natCast R (m + n) + 1 = natCast R m + (natCast R n + 1)
    rw [natCast_add m n, add_assoc]

theorem natCast_mul (m : Nat) : ∀ n : Nat, natCast R (m * n) = natCast R m * natCast R n
  | 0 => (mul_zero _).symm
  | n + 1 => by
    rw [Nat.mul_succ, natCast_add, natCast_mul m n, natCast_succ, left_distrib, mul_one]

theorem natCast_nonneg : ∀ n : Nat, (0 : R) ≤ natCast R n
  | 0 => le_refl 0
  | n + 1 => by
    have h1 := add_le_add (natCast_nonneg n) zero_le_one
    rw [add_zero] at h1; exact h1

theorem natCast_pos : ∀ {n : Nat}, 0 < n → (0 : R) < natCast R n
  | 0, h => by omega
  | n + 1, _ => by
    have h1 := add_le_add_right (natCast_nonneg (R := R) n) 1
    rw [zero_add] at h1
    exact lt_of_lt_of_le zero_lt_one h1

theorem natCast_lt_natCast {m n : Nat} (h : m < n) : natCast R m < natCast R n := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, n = m + (k + 1) := ⟨n - m - 1, by omega⟩
  rw [hk, natCast_add]
  have hkpos : (0 : R) < natCast R (k + 1) := natCast_pos (by omega)
  rcases lt_iff_le_not_le.mp hkpos with ⟨hkle, hknot⟩
  refine lt_iff_le_not_le.mpr ⟨?_, fun hge => hknot ?_⟩
  · have h1 := add_le_add_left hkle (natCast R m)
    rw [add_zero] at h1; exact h1
  · have h2 := add_le_add_left hge (-(natCast R m))
    rw [← add_assoc, neg_add_cancel, zero_add] at h2
    exact h2

def ofInt (R : Type u) [LinearOrderedCommRing R] : Int → R
  | Int.ofNat n => natCast R n
  | Int.negSucc n => -(natCast R (n + 1))

theorem ofInt_ofNat (n : Nat) : ofInt R (Int.ofNat n) = natCast R n := rfl

theorem ofInt_neg : ∀ z : Int, ofInt R (-z) = -(ofInt R z)
  | Int.ofNat 0 => neg_zero.symm
  | Int.ofNat (_ + 1) => rfl
  | Int.negSucc _ => (neg_neg _).symm

theorem ofInt_nonneg_toNat {z : Int} (hz : 0 ≤ z) : ofInt R z = natCast R z.toNat := by
  cases z with
  | ofNat _ => rfl
  | negSucc _ => omega

theorem natCast_sub_add {m n : Nat} (h : n ≤ m) :
    natCast R (m - n) = natCast R m - natCast R n := by
  have heq : (m - n) + n = m := by omega
  have hcast := natCast_add (R := R) (m - n) n
  rw [heq] at hcast
  have h2 := congrArg (fun x => x - natCast R n) hcast.symm
  dsimp at h2
  rw [add_sub_cancel] at h2
  exact h2

theorem ofInt_add (a b : Int) : ofInt R (a + b) = ofInt R a + ofInt R b := by
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · have hab : 0 ≤ a + b := by omega
      have htn : (a + b).toNat = a.toNat + b.toNat := by omega
      rw [ofInt_nonneg_toNat ha, ofInt_nonneg_toNat hb, ofInt_nonneg_toNat hab, htn, natCast_add]
    · have hnb : 0 ≤ -b := by omega
      have hb_eq : ofInt R b = -(natCast R (-b).toNat) := by
        rw [← neg_neg (ofInt R b), ← ofInt_neg, ofInt_nonneg_toNat hnb]
      by_cases hab : 0 ≤ a + b
      · have hle : (-b).toNat ≤ a.toNat := by omega
        have htn : (a + b).toNat = a.toNat - (-b).toNat := by omega
        rw [ofInt_nonneg_toNat hab, htn, natCast_sub_add hle, ofInt_nonneg_toNat ha,
            hb_eq, ← sub_eq_add_neg]
      · have hnab : 0 ≤ -(a + b) := by omega
        have hle : a.toNat ≤ (-b).toNat := by omega
        have htn : (-(a + b)).toNat = (-b).toNat - a.toNat := by omega
        have hab_eq : ofInt R (a + b) = -(natCast R (-(a + b)).toNat) := by
          rw [← neg_neg (ofInt R (a + b)), ← ofInt_neg, ofInt_nonneg_toNat hnab]
        rw [hab_eq, htn, natCast_sub_add hle, ofInt_nonneg_toNat ha, hb_eq,
            sub_eq_add_neg, neg_add, neg_neg, add_comm]
  · have hna : 0 ≤ -a := by omega
    have ha_eq : ofInt R a = -(natCast R (-a).toNat) := by
      rw [← neg_neg (ofInt R a), ← ofInt_neg, ofInt_nonneg_toNat hna]
    by_cases hb : 0 ≤ b
    · by_cases hab : 0 ≤ a + b
      · have hle : (-a).toNat ≤ b.toNat := by omega
        have htn : (a + b).toNat = b.toNat - (-a).toNat := by omega
        rw [ofInt_nonneg_toNat hab, htn, natCast_sub_add hle, ha_eq,
            ofInt_nonneg_toNat hb, sub_eq_add_neg, add_comm]
      · have hnab : 0 ≤ -(a + b) := by omega
        have hle : b.toNat ≤ (-a).toNat := by omega
        have htn : (-(a + b)).toNat = (-a).toNat - b.toNat := by omega
        have hab_eq : ofInt R (a + b) = -(natCast R (-(a + b)).toNat) := by
          rw [← neg_neg (ofInt R (a + b)), ← ofInt_neg, ofInt_nonneg_toNat hnab]
        rw [hab_eq, htn, natCast_sub_add hle, ha_eq, ofInt_nonneg_toNat hb,
            sub_eq_add_neg, neg_add, neg_neg]
    · have hnb : 0 ≤ -b := by omega
      have hnab : 0 ≤ -(a + b) := by omega
      have htn : (-(a + b)).toNat = (-a).toNat + (-b).toNat := by omega
      have hab_eq : ofInt R (a + b) = -(natCast R (-(a + b)).toNat) := by
        rw [← neg_neg (ofInt R (a + b)), ← ofInt_neg, ofInt_nonneg_toNat hnab]
      have hb_eq : ofInt R b = -(natCast R (-b).toNat) := by
        rw [← neg_neg (ofInt R b), ← ofInt_neg, ofInt_nonneg_toNat hnb]
      rw [hab_eq, htn, natCast_add, neg_add, ha_eq, hb_eq]

theorem ofInt_sub (a b : Int) : ofInt R (a - b) = ofInt R a - ofInt R b := by
  rw [Int.sub_eq_add_neg, ofInt_add, ofInt_neg, ← sub_eq_add_neg]

theorem ofInt_mul_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ofInt R (a * b) = ofInt R a * ofInt R b := by
  have hab : 0 ≤ a * b := Int.mul_nonneg ha hb
  have htn : (a * b).toNat = a.toNat * b.toNat := by
    have ea : Int.ofNat a.toNat = a := Int.toNat_of_nonneg ha
    have eb : Int.ofNat b.toNat = b := Int.toNat_of_nonneg hb
    have eab : Int.ofNat (a.toNat * b.toNat) = a * b := by
      change Int.ofNat a.toNat * Int.ofNat b.toNat = a * b
      rw [ea, eb]
    rw [← eab]; rfl
  rw [ofInt_nonneg_toNat ha, ofInt_nonneg_toNat hb, ofInt_nonneg_toNat hab, htn, natCast_mul]

theorem ofInt_mul (a b : Int) : ofInt R (a * b) = ofInt R a * ofInt R b := by
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · exact ofInt_mul_nonneg ha hb
    · have hnb : 0 ≤ -b := by omega
      have h := ofInt_mul_nonneg (R := R) ha hnb
      rw [Int.mul_neg, ofInt_neg, ofInt_neg] at h
      calc ofInt R (a * b)
          = -(-(ofInt R (a * b))) := (neg_neg _).symm
        _ = -(ofInt R a * -(ofInt R b)) := by rw [h]
        _ = ofInt R a * ofInt R b := by rw [mul_neg, neg_neg]
  · have hna : 0 ≤ -a := by omega
    by_cases hb : 0 ≤ b
    · have h := ofInt_mul_nonneg (R := R) hna hb
      rw [Int.neg_mul, ofInt_neg, ofInt_neg] at h
      calc ofInt R (a * b)
          = -(-(ofInt R (a * b))) := (neg_neg _).symm
        _ = -(-(ofInt R a) * ofInt R b) := by rw [h]
        _ = ofInt R a * ofInt R b := by rw [neg_mul, neg_neg]
    · have hnb : 0 ≤ -b := by omega
      have h := ofInt_mul_nonneg (R := R) hna hnb
      rw [Int.neg_mul_neg, ofInt_neg, ofInt_neg, neg_mul_neg] at h
      exact h

theorem ofInt_lt {a b : Int} (h : a < b) : ofInt R a < ofInt R b := by
  have htn : 0 < (b - a).toNat := by omega
  have hsub : ofInt R b - ofInt R a = natCast R (b - a).toNat := by
    rw [← ofInt_sub, ofInt_nonneg_toNat (by omega)]
  have hcpos : (0 : R) < natCast R (b - a).toNat := natCast_pos htn
  rw [← hsub] at hcpos
  rcases lt_iff_le_not_le.mp hcpos with ⟨hle, hnot⟩
  exact lt_iff_le_not_le.mpr ⟨le_of_sub_nonneg hle, fun hba => hnot (by
    have h2 := sub_nonneg_of_le hba
    have h3 := add_le_add_right h2 (ofInt R b - ofInt R a)
    have hsum : (ofInt R a - ofInt R b) + (ofInt R b - ofInt R a) = 0 := by
      calc (ofInt R a - ofInt R b) + (ofInt R b - ofInt R a)
          = ofInt R a + (-(ofInt R b) + (ofInt R b + -(ofInt R a))) := by
              rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc]
        _ = ofInt R a + (0 + -(ofInt R a)) := by
              rw [← add_assoc (-(ofInt R b)) (ofInt R b), neg_add_cancel]
        _ = 0 := by rw [zero_add, add_neg_cancel]
    rw [zero_add, hsum] at h3
    exact h3)⟩

theorem ofInt_ne {a b : Int} (h : a ≠ b) : ofInt R a ≠ ofInt R b := by
  by_cases hlt : a < b
  · exact ne_of_lt (ofInt_lt hlt)
  · exact ne_of_gt (ofInt_lt (by omega))

end RingLemmas

section FieldLemmas
variable {F : Type u} [LinearOrderedField F]

abbrev finv (a : F) : F := LinearOrderedField.inv a
abbrev fdiv (a b : F) : F := a * finv b

theorem mul_finv_cancel {a : F} (ha : a ≠ 0) : a * finv a = 1 :=
  LinearOrderedField.mul_inv_cancel a ha

theorem finv_mul_cancel {a : F} (ha : a ≠ 0) : finv a * a = 1 := by
  rw [mul_comm, mul_finv_cancel ha]

theorem finv_one : finv (1 : F) = 1 := by
  calc finv (1 : F) = 1 * finv 1 := (one_mul _).symm
    _ = 1 := mul_finv_cancel one_ne_zero

theorem mul_eq_zero {a b : F} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · refine Or.inr ?_
    calc b = 1 * b := (one_mul b).symm
      _ = (finv a * a) * b := by rw [finv_mul_cancel ha]
      _ = finv a * (a * b) := mul_assoc _ _ _
      _ = finv a * 0 := by rw [h]
      _ = 0 := mul_zero _

theorem mul_right_cancel {a b c : F} (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  calc a = a * 1 := (mul_one a).symm
    _ = a * (c * finv c) := by rw [mul_finv_cancel hc]
    _ = (a * c) * finv c := (mul_assoc _ _ _).symm
    _ = (b * c) * finv c := by rw [h]
    _ = b * (c * finv c) := mul_assoc _ _ _
    _ = b * 1 := by rw [mul_finv_cancel hc]
    _ = b := mul_one b

theorem finv_pos {a : F} (ha : 0 < a) : 0 < finv a := by
  have hne : a ≠ 0 := ne_of_gt ha
  cases le_total 0 (finv a) with
  | inl hge =>
    refine lt_of_le_of_ne hge (fun hz => ?_)
    have h1 := mul_finv_cancel hne
    rw [← hz, mul_zero] at h1
    exact one_ne_zero h1.symm
  | inr hle =>
    exfalso
    have hlt : finv a < 0 := lt_of_le_of_ne hle (fun hz => by
      have h1 := mul_finv_cancel hne
      rw [hz, mul_zero] at h1
      exact one_ne_zero h1.symm)
    have hp := mul_pos ha (neg_pos_of_neg hlt)
    rw [mul_neg, mul_finv_cancel hne] at hp
    have h2 := add_le_add_right (le_of_lt hp) 1
    rw [zero_add, neg_add_cancel] at h2
    exact (lt_iff_le_not_le.mp zero_lt_one).2 h2

theorem finv_nonneg {a : F} (ha : 0 < a) : 0 ≤ finv a := le_of_lt (finv_pos ha)

theorem finv_lt_finv {a b : F} (ha : 0 < a) (hab : a < b) : finv b < finv a := by
  have hb : 0 < b := lt_trans ha hab
  have hpa : 0 < finv a := finv_pos ha
  have hpb : 0 < finv b := finv_pos hb
  have hdiff : 0 < (b - a) * (finv a * finv b) := by
    apply mul_pos _ (mul_pos hpa hpb)
    rcases lt_iff_le_not_le.mp hab with ⟨h1, h2⟩
    refine lt_iff_le_not_le.mpr ⟨sub_nonneg_of_le h1, fun hz => h2 ?_⟩
    have h3 := add_le_add_right hz a
    rw [sub_add_cancel, zero_add] at h3; exact h3
  have hexp : (b - a) * (finv a * finv b) = finv a - finv b := by
    rw [sub_mul]
    have t1 : b * (finv a * finv b) = finv a := by
      rw [mul_comm (finv a) (finv b), ← mul_assoc, mul_finv_cancel (ne_of_gt hb), one_mul]
    have t2 : a * (finv a * finv b) = finv b := by
      rw [← mul_assoc, mul_finv_cancel (ne_of_gt ha), one_mul]
    rw [t1, t2]
  rw [hexp] at hdiff
  rcases lt_iff_le_not_le.mp hdiff with ⟨hle, hnot⟩
  refine lt_iff_le_not_le.mpr ⟨le_of_sub_nonneg hle, fun hge => hnot ?_⟩
  have h2 := sub_nonneg_of_le hge
  have h3 := add_le_add_right h2 (finv a - finv b)
  have hsum : (finv b - finv a) + (finv a - finv b) = 0 := by
    calc (finv b - finv a) + (finv a - finv b)
        = finv b + (-(finv a) + (finv a + -(finv b))) := by
            rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc]
      _ = finv b + (0 + -(finv b)) := by rw [← add_assoc (-(finv a)) (finv a), neg_add_cancel]
      _ = 0 := by rw [zero_add, add_neg_cancel]
  rw [zero_add, hsum] at h3
  exact h3

end FieldLemmas

-- ============================================================================
-- §2. Finite Sums, Finite Products, Inner Products, and General-N Cauchy-Schwarz
-- ============================================================================

section SumsAndCauchySchwarz
variable {R : Type u} [LinearOrderedCommRing R]

def finSum : (n : Nat) → (Fin n → R) → R
  | 0, _ => 0
  | n + 1, f => finSum n (fun i => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) + f ⟨n, Nat.lt_succ_self n⟩

def finProd : (n : Nat) → (Fin n → R) → R
  | 0, _ => 1
  | n + 1, f => finProd n (fun i => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) * f ⟨n, Nat.lt_succ_self n⟩

theorem finSum_congr {n : Nat} {f g : Fin n → R} (h : ∀ i, f i = g i) :
    finSum n f = finSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold finSum
    rw [ih (fun i => h _), h]

theorem finSum_add (n : Nat) (f g : Fin n → R) :
    finSum n (fun i => f i + g i) = finSum n f + finSum n g := by
  induction n with
  | zero => exact (add_zero 0).symm
  | succ n ih =>
    unfold finSum
    rw [ih]
    calc (finSum n (fun i => f ⟨i.1, _⟩) + finSum n (fun i => g ⟨i.1, _⟩)) +
           (f ⟨n, _⟩ + g ⟨n, _⟩)
        = finSum n (fun i => f ⟨i.1, _⟩) +
            (finSum n (fun i => g ⟨i.1, _⟩) + (f ⟨n, _⟩ + g ⟨n, _⟩)) := add_assoc _ _ _
      _ = finSum n (fun i => f ⟨i.1, _⟩) +
            (f ⟨n, _⟩ + (finSum n (fun i => g ⟨i.1, _⟩) + g ⟨n, _⟩)) := by
            rw [← add_assoc (finSum n _) (f _) (g _),
                add_comm (finSum n (fun i => g ⟨i.1, _⟩)) (f _), add_assoc]
      _ = (finSum n (fun i => f ⟨i.1, _⟩) + f ⟨n, _⟩) +
            (finSum n (fun i => g ⟨i.1, _⟩) + g ⟨n, _⟩) := (add_assoc _ _ _).symm

theorem finSum_neg (n : Nat) (g : Fin n → R) :
    finSum n (fun i => -(g i)) = -(finSum n g) := by
  induction n with
  | zero => exact neg_zero.symm
  | succ n ih => unfold finSum; rw [ih, neg_add]

theorem finSum_sub (n : Nat) (f g : Fin n → R) :
    finSum n (fun i => f i - g i) = finSum n f - finSum n g := by
  calc finSum n (fun i => f i - g i)
      = finSum n (fun i => f i + -(g i)) := finSum_congr (fun i => sub_eq_add_neg _ _)
    _ = finSum n f + finSum n (fun i => -(g i)) := finSum_add _ _ _
    _ = finSum n f - finSum n g := by rw [finSum_neg, ← sub_eq_add_neg]

theorem finSum_mul_left (n : Nat) (c : R) (f : Fin n → R) :
    finSum n (fun i => c * f i) = c * finSum n f := by
  induction n with
  | zero => exact (mul_zero c).symm
  | succ n ih => unfold finSum; rw [ih, left_distrib]

theorem finSum_mul_right (n : Nat) (f : Fin n → R) (c : R) :
    finSum n (fun i => f i * c) = finSum n f * c := by
  induction n with
  | zero => exact (zero_mul c).symm
  | succ n ih => unfold finSum; rw [ih, right_distrib]

theorem finSum_const (n : Nat) (c : R) : finSum n (fun _ => c) = natCast R n * c := by
  induction n with
  | zero => exact (zero_mul c).symm
  | succ n ih => unfold finSum; rw [ih, natCast_succ, right_distrib, one_mul]

theorem finProd_const (n : Nat) (c : R) : finProd n (fun _ => c) = rpow c n := by
  induction n with
  | zero => rfl
  | succ n ih => unfold finProd; rw [ih, rpow_succ]

theorem finSum_nonneg {n : Nat} {f : Fin n → R} (hf : ∀ i, 0 ≤ f i) : 0 ≤ finSum n f := by
  induction n with
  | zero => exact le_refl 0
  | succ n ih =>
    unfold finSum
    have hinit : 0 ≤ finSum n (fun i => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) :=
      ih (fun i => hf ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
    have h1 := add_le_add hinit (hf ⟨n, Nat.lt_succ_self n⟩)
    rw [add_zero] at h1; exact h1

theorem finSum_le_finSum {n : Nat} {f g : Fin n → R} (h : ∀ i, f i ≤ g i) :
    finSum n f ≤ finSum n g := by
  induction n with
  | zero => exact le_refl 0
  | succ n ih =>
    unfold finSum
    exact add_le_add (ih (fun i => h ⟨i.1, Nat.lt_succ_of_lt i.2⟩)) (h ⟨n, Nat.lt_succ_self n⟩)

theorem finSum_eq_zero_iff_of_nonneg {n : Nat} {f : Fin n → R} (hf : ∀ i, 0 ≤ f i) :
    finSum n f = 0 ↔ ∀ i, f i = 0 := by
  induction n with
  | zero =>
    constructor
    · intro _ i; exact Fin.elim0 i
    · intro _; rfl
  | succ n ih =>
    unfold finSum
    constructor
    · intro hsum i
      have hinit : 0 ≤ finSum n (fun j => f ⟨j.1, Nat.lt_succ_of_lt j.2⟩) :=
        finSum_nonneg (fun j => hf ⟨j.1, Nat.lt_succ_of_lt j.2⟩)
      have hlast : 0 ≤ f ⟨n, Nat.lt_succ_self n⟩ := hf ⟨n, Nat.lt_succ_self n⟩
      have hlast0 : f ⟨n, Nat.lt_succ_self n⟩ = 0 := by
        apply le_antisymm _ hlast
        have h1 := add_le_add_right hinit (f ⟨n, Nat.lt_succ_self n⟩)
        rw [zero_add, hsum] at h1; exact h1
      have hinit0 : finSum n (fun j => f ⟨j.1, Nat.lt_succ_of_lt j.2⟩) = 0 := by
        rw [hlast0, add_zero] at hsum; exact hsum
      have hall := (ih (fun j => hf ⟨j.1, Nat.lt_succ_of_lt j.2⟩)).mp hinit0
      by_cases hi : i.1 < n
      · exact hall ⟨i.1, hi⟩
      · have hieq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext (by dsimp; have := i.2; omega)
        rw [hieq]; exact hlast0
    · intro hz
      rw [(ih (fun j => hf ⟨j.1, Nat.lt_succ_of_lt j.2⟩)).mpr (fun j => hz _),
          hz ⟨n, Nat.lt_succ_self n⟩, add_zero]

def dot {n : Nat} (u v : Fin n → R) : R := finSum n (fun i => u i * v i)
def normSq {n : Nat} (u : Fin n → R) : R := dot u u

theorem dot_comm {n : Nat} (u v : Fin n → R) : dot u v = dot v u :=
  finSum_congr (fun i => mul_comm (u i) (v i))

theorem normSq_nonneg {n : Nat} (u : Fin n → R) : 0 ≤ normSq u :=
  finSum_nonneg (fun i => sq_nonneg (u i))

def lagrangeDiff (n : Nat) (u v : Fin n → R) : R :=
  normSq u * normSq v - sq (dot u v)

private theorem lagrange_scalar_step (A B C x y : R) :
    (A + sq x) * (B + sq y) - sq (C + x * y) =
    (A * B - sq C) + ((A * sq y - C * (x * y)) + (B * sq x - C * (x * y))) := by
  unfold sq
  have lhs_exp : (A + x * x) * (B + y * y) =
      (A * B + A * (y * y)) + (B * (x * x) + (x * x) * (y * y)) := by
    rw [right_distrib, left_distrib, left_distrib, mul_comm (x * x) B]
  have rhs_exp : (C + x * y) * (C + x * y) =
      (C * C + C * (x * y)) + (C * (x * y) + (x * x) * (y * y)) := by
    rw [right_distrib, left_distrib, left_distrib, mul_comm (x * y) C]
    have xy_sq : (x * y) * (x * y) = (x * x) * (y * y) := by
      rw [mul_assoc, ← mul_assoc y x y, mul_comm y x, mul_assoc x y y, ← mul_assoc]
    rw [xy_sq]
  let a1 := A * B
  let a2 := A * (y * y)
  let a3 := B * (x * x)
  let p  := (x * x) * (y * y)
  let c1 := -(C * C)
  let c2 := -(C * (x * y))
  have rearrange : ((a1 + a2) + (a3 + p)) + ((c1 + c2) + (c2 + -p)) =
                   (a1 + c1) + ((a2 + c2) + (a3 + c2)) := by
    calc ((a1 + a2) + (a3 + p)) + ((c1 + c2) + (c2 + -p))
        = (a1 + a2 + a3) + (p + (-p + (c1 + c2 + c2))) := by
            rw [← add_assoc (a1 + a2) a3 p,
                add_comm c2 (-p), ← add_assoc (c1 + c2) (-p) c2,
                add_comm (c1 + c2) (-p), add_assoc (-p) (c1 + c2) c2,
                add_assoc (a1 + a2 + a3) p _]
      _ = (a1 + a2 + a3) + (c1 + c2 + c2) := by
            rw [← add_assoc p (-p) _, add_neg_cancel, zero_add]
      _ = a1 + (a2 + (a3 + (c1 + (c2 + c2)))) := by
            rw [add_assoc (a1 + a2) a3 _, add_assoc a1 a2 _, add_assoc c1 c2 c2]
      _ = a1 + (c1 + (a2 + (c2 + (a3 + c2)))) := by
            rw [← add_assoc a3 c1 (c2 + c2), add_comm a3 c1, add_assoc c1 a3 _,
                ← add_assoc a2 c1 _, add_comm a2 c1, add_assoc c1 a2 _,
                ← add_assoc a3 c2 c2, add_comm a3 c2, add_assoc c2 a3 c2, add_comm c2 a3]
      _ = (a1 + c1) + ((a2 + c2) + (a3 + c2)) := by
            rw [← add_assoc a1 c1 _, ← add_assoc a2 c2 (a3 + c2)]
  calc (A + x * x) * (B + y * y) - (C + x * y) * (C + x * y)
      = ((a1 + a2) + (a3 + p)) + -(((C * C + C * (x * y)) + (C * (x * y) + p))) := by
          rw [sub_eq_add_neg, lhs_exp, rhs_exp]
    _ = ((a1 + a2) + (a3 + p)) + ((c1 + c2) + (c2 + -p)) := by
          rw [neg_add, neg_add, neg_add]
    _ = (a1 + c1) + ((a2 + c2) + (a3 + c2)) := rearrange
    _ = (A * B - C * C) + ((A * (y * y) - C * (x * y)) + (B * (x * x) - C * (x * y))) := by
          dsimp [a1, a2, a3, c1, c2]
          rw [← sub_eq_add_neg, ← sub_eq_add_neg, ← sub_eq_add_neg]

private theorem sq_sub_expand (u v x y : R) :
    sq (u * y - v * x) = (sq u * sq y - (u * v) * (x * y)) + (sq v * sq x - (u * v) * (x * y)) := by
  unfold sq
  have t1 : (u * y) * (u * y) = (u * u) * (y * y) := by
    rw [mul_assoc, ← mul_assoc y u y, mul_comm y u, mul_assoc u y y, ← mul_assoc]
  have t2 : (v * x) * (v * x) = (v * v) * (x * x) := by
    rw [mul_assoc, ← mul_assoc x v x, mul_comm x v, mul_assoc v x x, ← mul_assoc]
  have t3 : (u * y) * (v * x) = (u * v) * (x * y) := by
    rw [mul_assoc, ← mul_assoc y v x, mul_comm y v, mul_assoc v y x, mul_comm y x, ← mul_assoc]
  have t4 : (v * x) * (u * y) = (u * v) * (x * y) := by
    rw [mul_comm (v * x) (u * y), t3]
  calc (u * y - v * x) * (u * y - v * x)
      = ((u * y) * (u * y) - (u * y) * (v * x)) - ((v * x) * (u * y) - (v * x) * (v * x)) := by
          rw [sub_mul, mul_sub, mul_sub]
    _ = ((u * u) * (y * y) + -((u * v) * (x * y))) +
        ((v * v) * (x * x) + -((u * v) * (x * y))) := by
          rw [t1, t2, t3, t4, sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg,
              neg_add, neg_neg, add_comm (-((u * v) * (x * y))) ((v * v) * (x * x))]
    _ = ((u * u) * (y * y) - (u * v) * (x * y)) + ((v * v) * (x * x) - (u * v) * (x * y)) := by
          rw [← sub_eq_add_neg, ← sub_eq_add_neg]

theorem lagrange_succ (n : Nat) (u v : Fin (n + 1) → R) :
    lagrangeDiff (n + 1) u v =
      lagrangeDiff n (fun i => u ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
                     (fun i => v ⟨i.1, Nat.lt_succ_of_lt i.2⟩) +
      finSum n (fun i => sq (u ⟨i.1, Nat.lt_succ_of_lt i.2⟩ * v ⟨n, Nat.lt_succ_self n⟩ -
                             v ⟨i.1, Nat.lt_succ_of_lt i.2⟩ * u ⟨n, Nat.lt_succ_self n⟩)) := by
  let ui : Fin n → R := fun i => u ⟨i.1, Nat.lt_succ_of_lt i.2⟩
  let vi : Fin n → R := fun i => v ⟨i.1, Nat.lt_succ_of_lt i.2⟩
  let x := u ⟨n, Nat.lt_succ_self n⟩
  let y := v ⟨n, Nat.lt_succ_self n⟩
  have hsum : finSum n (fun i => sq (ui i * y - vi i * x)) =
      (normSq ui * sq y - dot ui vi * (x * y)) + (normSq vi * sq x - dot ui vi * (x * y)) := by
    calc finSum n (fun i => sq (ui i * y - vi i * x))
        = finSum n (fun i => (sq (ui i) * sq y - (ui i * vi i) * (x * y)) +
                             (sq (vi i) * sq x - (ui i * vi i) * (x * y))) :=
            finSum_congr (fun i => sq_sub_expand (ui i) (vi i) x y)
      _ = finSum n (fun i => sq (ui i) * sq y - (ui i * vi i) * (x * y)) +
          finSum n (fun i => sq (vi i) * sq x - (ui i * vi i) * (x * y)) := finSum_add _ _ _
      _ = (normSq ui * sq y - dot ui vi * (x * y)) +
          (normSq vi * sq x - dot ui vi * (x * y)) := by
            rw [finSum_sub, finSum_sub, finSum_mul_right, finSum_mul_right, finSum_mul_right]
            rfl
  unfold lagrangeDiff normSq dot
  dsimp [finSum]
  rw [hsum]
  exact lagrange_scalar_step (finSum n (fun i => ui i * ui i))
                             (finSum n (fun i => vi i * vi i))
                             (finSum n (fun i => ui i * vi i)) x y

theorem lagrangeDiff_nonneg (n : Nat) (u v : Fin n → R) : 0 ≤ lagrangeDiff n u v := by
  induction n with
  | zero =>
    unfold lagrangeDiff normSq dot finSum sq
    rw [mul_zero, sub_self]; exact le_refl 0
  | succ n ih =>
    rw [lagrange_succ]
    have h1 := ih (fun i => u ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
                  (fun i => v ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
    have h2 := finSum_nonneg (fun i : Fin n => sq_nonneg
      (u ⟨i.1, Nat.lt_succ_of_lt i.2⟩ * v ⟨n, Nat.lt_succ_self n⟩ -
       v ⟨i.1, Nat.lt_succ_of_lt i.2⟩ * u ⟨n, Nat.lt_succ_self n⟩))
    have h3 := add_le_add h1 h2
    rw [add_zero] at h3; exact h3

/-- General-N Cauchy-Schwarz inequality over any `LinearOrderedCommRing`. -/
theorem cauchy_schwarz_sq {n : Nat} (u v : Fin n → R) :
    sq (dot u v) ≤ normSq u * normSq v :=
  le_of_sub_nonneg (lagrangeDiff_nonneg n u v)

theorem lagrangeDiff_eq_zero_iff : ∀ (n : Nat) (u v : Fin n → R),
    lagrangeDiff n u v = 0 ↔ ∀ i j : Fin n, u i * v j = v i * u j
  | 0, _, _ => by
    constructor
    · intro _ i; exact Fin.elim0 i
    · intro _; unfold lagrangeDiff normSq dot finSum sq; rw [mul_zero, sub_self]
  | n + 1, u, v => by
    rw [lagrange_succ]
    let ui : Fin n → R := fun i => u ⟨i.1, Nat.lt_succ_of_lt i.2⟩
    let vi : Fin n → R := fun i => v ⟨i.1, Nat.lt_succ_of_lt i.2⟩
    let remTerm : R := finSum n (fun i => sq (ui i * v ⟨n, Nat.lt_succ_self n⟩ -
                                              vi i * u ⟨n, Nat.lt_succ_self n⟩))
    have h1_nn : 0 ≤ lagrangeDiff n ui vi := lagrangeDiff_nonneg n ui vi
    have h2_nn : 0 ≤ remTerm := finSum_nonneg (fun _ => sq_nonneg _)
    constructor
    · intro hsum i j
      have h2_zero : remTerm = 0 := by
        apply le_antisymm _ h2_nn
        have ha := add_le_add_right h1_nn remTerm
        rw [zero_add] at ha
        exact le_trans ha (by rw [← hsum]; exact le_refl _)
      have h1_zero : lagrangeDiff n ui vi = 0 := by
        change lagrangeDiff n ui vi + remTerm = 0 at hsum
        rw [h2_zero, add_zero] at hsum; exact hsum
      have hall_init := (lagrangeDiff_eq_zero_iff n ui vi).mp h1_zero
      have hall_last := (finSum_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _)).mp h2_zero
      by_cases hi : i.1 < n
      · by_cases hj : j.1 < n
        · exact hall_init ⟨i.1, hi⟩ ⟨j.1, hj⟩
        · have hjeq : j = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext (by dsimp; have := j.2; omega)
          rw [hjeq]
          have hsq := sq_eq_zero_iff.mp (hall_last ⟨i.1, hi⟩)
          have hadd := congrArg (fun z => z + vi ⟨i.1, hi⟩ * u ⟨n, Nat.lt_succ_self n⟩) hsq
          dsimp [ui, vi] at hadd
          rw [sub_add_cancel, zero_add] at hadd
          exact hadd
      · have hieq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext (by dsimp; have := i.2; omega)
        by_cases hj : j.1 < n
        · rw [hieq]
          have hsq := sq_eq_zero_iff.mp (hall_last ⟨j.1, hj⟩)
          have hadd := congrArg (fun z => z + vi ⟨j.1, hj⟩ * u ⟨n, Nat.lt_succ_self n⟩) hsq
          dsimp [ui, vi] at hadd
          rw [sub_add_cancel, zero_add] at hadd
          rw [mul_comm (u _) (v j), mul_comm (v _) (u j)]
          exact hadd.symm
        · have hjeq : j = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext (by dsimp; have := j.2; omega)
          rw [hieq, hjeq, mul_comm]
    · intro hall
      have h1_zero : lagrangeDiff n ui vi = 0 :=
        (lagrangeDiff_eq_zero_iff n ui vi).mpr
          (fun i j => hall ⟨i.1, Nat.lt_succ_of_lt i.2⟩ ⟨j.1, Nat.lt_succ_of_lt j.2⟩)
      have h2_zero : remTerm = 0 := by
        apply (finSum_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _)).mpr
        intro k
        apply sq_eq_zero_iff.mpr
        have hk := hall ⟨k.1, Nat.lt_succ_of_lt k.2⟩ ⟨n, Nat.lt_succ_self n⟩
        change u ⟨k.1, _⟩ * v ⟨n, _⟩ - v ⟨k.1, _⟩ * u ⟨n, _⟩ = 0
        rw [hk, sub_self]
      change lagrangeDiff n ui vi + remTerm = 0
      rw [h1_zero, h2_zero, add_zero]

/-- Equality in Cauchy-Schwarz holds iff `u` and `v` have vanishing 2x2 minors (`u_i v_j = v_i u_j`). -/
theorem cauchy_schwarz_eq_iff_collinear {n : Nat} (u v : Fin n → R) :
    sq (dot u v) = normSq u * normSq v ↔ ∀ i j : Fin n, u i * v j = v i * u j := by
  have hzero : sq (dot u v) = normSq u * normSq v ↔ lagrangeDiff n u v = 0 := by
    unfold lagrangeDiff
    constructor
    · intro h; rw [h, sub_self]
    · intro h
      have h1 := congrArg (fun z => z + sq (dot u v)) h
      dsimp at h1
      rw [sub_add_cancel, zero_add] at h1
      exact h1.symm
  rw [hzero]
  exact lagrangeDiff_eq_zero_iff n u v

end SumsAndCauchySchwarz

-- ============================================================================
-- §3. Matrices, Operator-Norm / Singular-Value Bounds, & Orthogonal Invariance
-- ============================================================================

section MatrixAlgebra
variable {R : Type u} [LinearOrderedCommRing R]

abbrev Mat (R : Type u) (N : Nat) := Fin N → Fin N → R

def matZero (N : Nat) : Mat R N := fun _ _ => 0
def matId (N : Nat) : Mat R N := fun i j => if i = j then 1 else 0
def matAdd {N : Nat} (A B : Mat R N) : Mat R N := fun i j => A i j + B i j
def matScale {N : Nat} (c : R) (A : Mat R N) : Mat R N := fun i j => c * A i j
def matTr {N : Nat} (A : Mat R N) : Mat R N := fun i j => A j i
def matMul {N : Nat} (A B : Mat R N) : Mat R N :=
  fun i j => finSum N (fun k => A i k * B k j)
def matTrace {N : Nat} (A : Mat R N) : R := finSum N (fun i => A i i)
def matVec {N : Nat} (A : Mat R N) (v : Fin N → R) : Fin N → R :=
  fun i => dot (A i) v
def outer {N : Nat} (u v : Fin N → R) : Mat R N := fun i j => u i * v j
def gram {N : Nat} (A : Mat R N) : Mat R N := matMul (matTr A) A
def frobSq {N : Nat} (A : Mat R N) : R := finSum N (fun i => normSq (A i))

theorem finSum_comm (m n : Nat) (f : Fin m → Fin n → R) :
    finSum m (fun i => finSum n (fun j => f i j)) =
    finSum n (fun j => finSum m (fun i => f i j)) := by
  induction m with
  | zero =>
    have hz : finSum n (fun _ => (0 : R)) = 0 := by
      rw [finSum_const, mul_zero]
    exact hz.symm
  | succ m ih =>
    change finSum m (fun i => finSum n (fun j => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩ j)) +
             finSum n (fun j => f ⟨m, Nat.lt_succ_self m⟩ j) =
           finSum n (fun j => finSum m (fun i => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩ j) +
             f ⟨m, Nat.lt_succ_self m⟩ j)
    rw [ih, ← finSum_add]

theorem matMul_assoc {N : Nat} (A B C : Mat R N) :
    matMul (matMul A B) C = matMul A (matMul B C) := by
  funext i j
  unfold matMul
  calc finSum N (fun k => finSum N (fun l => A i l * B l k) * C k j)
      = finSum N (fun k => finSum N (fun l => (A i l * B l k) * C k j)) :=
          finSum_congr (fun k => (finSum_mul_right N _ (C k j)).symm)
    _ = finSum N (fun l => finSum N (fun k => A i l * (B l k * C k j))) := by
          rw [finSum_comm]
          exact finSum_congr (fun l => finSum_congr (fun k => mul_assoc _ _ _))
    _ = finSum N (fun l => A i l * finSum N (fun k => B l k * C k j)) :=
          finSum_congr (fun l => finSum_mul_left N (A i l) _)

theorem matVec_matMul {N : Nat} (A B : Mat R N) (v : Fin N → R) :
    matVec (matMul A B) v = matVec A (matVec B v) := by
  funext i
  unfold matVec dot matMul
  calc finSum N (fun j => finSum N (fun k => A i k * B k j) * v j)
      = finSum N (fun j => finSum N (fun k => (A i k * B k j) * v j)) :=
          finSum_congr (fun j => (finSum_mul_right N _ (v j)).symm)
    _ = finSum N (fun k => finSum N (fun j => A i k * (B k j * v j))) := by
          rw [finSum_comm]
          exact finSum_congr (fun k => finSum_congr (fun j => mul_assoc _ _ _))
    _ = finSum N (fun k => A i k * finSum N (fun j => B k j * v j)) :=
          finSum_congr (fun k => finSum_mul_left N (A i k) _)

theorem finSum_ite_eq (N : Nat) (i : Fin N) (f : Fin N → R) :
    finSum N (fun k => (if k = i then (1 : R) else 0) * f k) = f i := by
  induction N with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    unfold finSum
    by_cases hi : i.1 < n
    · have hne : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) ≠ i := fun h => by
        have h1 := congrArg Fin.val h; dsimp at h1; omega
      have hconv : (fun k : Fin n =>
          (if (⟨k.1, Nat.lt_succ_of_lt k.2⟩ : Fin (n + 1)) = i then (1 : R) else 0) *
            f ⟨k.1, Nat.lt_succ_of_lt k.2⟩) =
          (fun k : Fin n => (if k = ⟨i.1, hi⟩ then (1 : R) else 0) *
            f ⟨k.1, Nat.lt_succ_of_lt k.2⟩) := by
        funext k
        by_cases hk : k.1 = i.1
        · have e1 : (⟨k.1, Nat.lt_succ_of_lt k.2⟩ : Fin (n + 1)) = i := Fin.ext hk
          have e2 : k = ⟨i.1, hi⟩ := Fin.ext hk
          simp [e1, e2]
        · have e1 : (⟨k.1, Nat.lt_succ_of_lt k.2⟩ : Fin (n + 1)) ≠ i := fun h =>
            hk (congrArg Fin.val h)
          have e2 : k ≠ ⟨i.1, hi⟩ := fun h => hk (congrArg Fin.val h)
          simp [e1, e2]
      rw [hconv, ih ⟨i.1, hi⟩ (fun k => f ⟨k.1, Nat.lt_succ_of_lt k.2⟩)]
      have htail : (if (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = i then (1 : R) else 0) *
                     f ⟨n, Nat.lt_succ_self n⟩ = 0 := by
        simp [hne, zero_mul]
      dsimp
      rw [htail, add_zero]
    · have hieq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext (by dsimp; have := i.2; omega)
      have hz : finSum n (fun k : Fin n =>
          (if (⟨k.1, Nat.lt_succ_of_lt k.2⟩ : Fin (n + 1)) = i then (1 : R) else 0) *
            f ⟨k.1, Nat.lt_succ_of_lt k.2⟩) = 0 := by
        calc _ = finSum n (fun _ => (0 : R)) := finSum_congr (fun k => by
              have hne : (⟨k.1, Nat.lt_succ_of_lt k.2⟩ : Fin (n + 1)) ≠ i := by
                rw [hieq]; intro h; have hv := congrArg Fin.val h; dsimp at hv; omega
              simp [hne, zero_mul])
          _ = 0 := by rw [finSum_const, mul_zero]
      rw [hz, zero_add, hieq]
      simp [one_mul]

theorem matId_mul {N : Nat} (A : Mat R N) : matMul (matId N) A = A := by
  funext i j
  unfold matMul matId
  have hconv : (fun k : Fin N => (if i = k then (1 : R) else 0) * A k j) =
               (fun k : Fin N => (if k = i then (1 : R) else 0) * A k j) := by
    funext k; by_cases h : i = k
    · subst h; simp
    · have h2 : k ≠ i := fun hk => h hk.symm
      simp [h, h2]
  rw [hconv, finSum_ite_eq]

theorem mul_matId {N : Nat} (A : Mat R N) : matMul A (matId N) = A := by
  funext i j
  unfold matMul matId
  calc finSum N (fun k => A i k * (if k = j then 1 else 0))
      = finSum N (fun k => (if k = j then (1 : R) else 0) * A i k) :=
          finSum_congr (fun k => mul_comm _ _)
    _ = A i j := finSum_ite_eq N j (fun k => A i k)

theorem matVec_matId {N : Nat} (v : Fin N → R) : matVec (matId N) v = v := by
  funext i
  unfold matVec dot matId
  have hconv : (fun k : Fin N => (if i = k then (1 : R) else 0) * v k) =
               (fun k : Fin N => (if k = i then (1 : R) else 0) * v k) := by
    funext k; by_cases h : i = k
    · subst h; simp
    · have h2 : k ≠ i := fun hk => h hk.symm
      simp [h, h2]
  rw [hconv, finSum_ite_eq]

theorem matTr_matMul {N : Nat} (A B : Mat R N) :
    matTr (matMul A B) = matMul (matTr B) (matTr A) := by
  funext i j
  unfold matTr matMul
  exact finSum_congr (fun k => mul_comm (A j k) (B k i))

theorem matTrace_gram_eq_frobSq {N : Nat} (A : Mat R N) :
    matTrace (gram A) = frobSq A := by
  unfold matTrace gram matMul matTr frobSq normSq dot
  exact finSum_comm N N (fun j k => A k j * A k j)

theorem frobSq_nonneg {N : Nat} (A : Mat R N) : 0 ≤ frobSq A :=
  finSum_nonneg (fun i => normSq_nonneg (A i))

/-- `OpNormSqBound X μ` states `σ₁(X)² ≤ μ`, i.e., `0 ≤ μ` and `‖X v‖² ≤ μ ‖v‖²` for all `v`. -/
def OpNormSqBound {N : Nat} (X : Mat R N) (μ : R) : Prop :=
  0 ≤ μ ∧ ∀ v : Fin N → R, normSq (matVec X v) ≤ μ * normSq v

/-- `HasTopSingValSq X μ` states that the exact largest squared singular value `σ₁(X)²` is `μ`. -/
def HasTopSingValSq {N : Nat} (X : Mat R N) (μ : R) : Prop :=
  OpNormSqBound X μ ∧ ∃ v : Fin N → R, normSq v = 1 ∧ normSq (matVec X v) = μ

theorem hasTopSingValSq_unique {N : Nat} {X : Mat R N} {μ1 μ2 : R}
    (h1 : HasTopSingValSq X μ1) (h2 : HasTopSingValSq X μ2) : μ1 = μ2 := by
  rcases h1 with ⟨⟨_, hb1⟩, ⟨v1, hv1, heq1⟩⟩
  rcases h2 with ⟨⟨_, hb2⟩, ⟨v2, hv2, heq2⟩⟩
  apply le_antisymm
  · have u := hb2 v1
    rw [heq1, hv1, mul_one] at u; exact u
  · have u := hb1 v2
    rw [heq2, hv2, mul_one] at u; exact u

/-- Positive Theorem 1: Submultiplicativity of the top singular value squared (`σ₁(XY)² ≤ σ₁(X)² σ₁(Y)²`)
    in arbitrary dimension `N`. -/
theorem opNormSqBound_matMul {N : Nat} {X Y : Mat R N} {μX μY : R}
    (hX : OpNormSqBound X μX) (hY : OpNormSqBound Y μY) :
    OpNormSqBound (matMul X Y) (μX * μY) := by
  refine ⟨mul_nonneg hX.1 hY.1, fun v => ?_⟩
  rw [matVec_matMul]
  calc normSq (matVec X (matVec Y v))
      ≤ μX * normSq (matVec Y v) := hX.2 (matVec Y v)
    _ ≤ μX * (μY * normSq v) := mul_le_mul_of_nonneg_left (hY.2 v) hX.1
    _ = (μX * μY) * normSq v := (mul_assoc _ _ _).symm

/-- Universal Frobenius upper bound `σ₁(X)² ≤ ‖X‖_F²` in arbitrary dimension `N`. -/
theorem opNormSqBound_frobSq {N : Nat} (X : Mat R N) : OpNormSqBound X (frobSq X) := by
  refine ⟨frobSq_nonneg X, fun v => ?_⟩
  unfold normSq matVec
  calc dot (fun i => dot (X i) v) (fun i => dot (X i) v)
      = finSum N (fun i => sq (dot (X i) v)) := rfl
    _ ≤ finSum N (fun i => normSq (X i) * normSq v) :=
        finSum_le_finSum (fun i => cauchy_schwarz_sq (X i) v)
    _ = frobSq X * normSq v := finSum_mul_right N (fun i => normSq (X i)) (normSq v)

theorem matVec_outer {N : Nat} (u v w : Fin N → R) :
    matVec (outer u v) w = fun i => dot v w * u i := by
  funext i
  unfold matVec dot outer
  calc finSum N (fun j => (u i * v j) * w j)
      = finSum N (fun j => u i * (v j * w j)) := finSum_congr (fun j => mul_assoc _ _ _)
    _ = u i * finSum N (fun j => v j * w j) := finSum_mul_left N (u i) _
    _ = finSum N (fun j => v j * w j) * u i := mul_comm _ _

theorem normSq_scale {N : Nat} (c : R) (u : Fin N → R) :
    normSq (fun i => c * u i) = sq c * normSq u := by
  unfold normSq dot sq
  calc finSum N (fun i => (c * u i) * (c * u i))
      = finSum N (fun i => (c * c) * (u i * u i)) := finSum_congr (fun i => by
          rw [mul_assoc, ← mul_assoc (u i) c (u i), mul_comm (u i) c,
              mul_assoc c (u i) (u i), ← mul_assoc])
    _ = (c * c) * finSum N (fun i => u i * u i) := finSum_mul_left N (c * c) _

theorem outer_mul_outer {N : Nat} (u1 v1 u2 v2 : Fin N → R) :
    matMul (outer u1 v1) (outer u2 v2) = matScale (dot v1 u2) (outer u1 v2) := by
  funext i j
  unfold matMul outer matScale dot
  calc finSum N (fun k => (u1 i * v1 k) * (u2 k * v2 j))
      = finSum N (fun k => (v1 k * u2 k) * (u1 i * v2 j)) := finSum_congr (fun k => by
          calc (u1 i * v1 k) * (u2 k * v2 j)
              = u1 i * ((v1 k * u2 k) * v2 j) := by
                  rw [mul_assoc, ← mul_assoc (v1 k) (u2 k) (v2 j)]
            _ = (v1 k * u2 k) * (u1 i * v2 j) := by
                  rw [← mul_assoc (u1 i) (v1 k * u2 k) (v2 j),
                      mul_comm (u1 i) (v1 k * u2 k), mul_assoc])
    _ = finSum N (fun k => v1 k * u2 k) * (u1 i * v2 j) :=
          finSum_mul_right N (fun k => v1 k * u2 k) (u1 i * v2 j)

/-- Every rank-1 pure-state projection `P_ψ = |ψ⟩⟨ψ|` (`‖ψ‖² = 1`) has top singular value squared `1`. -/
theorem rankOneProj_hasTopSingValSq_one {N : Nat} {ψ : Fin N → R} (hψ : normSq ψ = 1) :
    HasTopSingValSq (outer ψ ψ) 1 := by
  refine ⟨⟨zero_le_one, fun w => ?_⟩, ⟨ψ, hψ, ?_⟩⟩
  · rw [matVec_outer, normSq_scale, hψ, mul_one, one_mul]
    have hcs := cauchy_schwarz_sq ψ w
    rw [hψ, one_mul] at hcs
    exact hcs
  · rw [matVec_outer, normSq_scale, hψ, mul_one]
    unfold sq normSq at *
    rw [hψ, one_mul]

private theorem quad_scalar_rearrange (c p u v : R) :
    (c * (p * u)) * (c * (p * v)) = (p * p) * ((c * c) * (u * v)) := by
  calc (c * (p * u)) * (c * (p * v))
      = (c * p) * (u * (c * (p * v))) := by
          rw [← mul_assoc c p u, mul_assoc (c * p) u _]
    _ = (c * p) * ((c * p) * (u * v)) := by
          rw [← mul_assoc c p v, ← mul_assoc u (c * p) v,
              mul_comm u (c * p), mul_assoc (c * p) u v]
    _ = ((c * p) * (c * p)) * (u * v) := (mul_assoc _ _ _).symm
    _ = ((p * p) * (c * c)) * (u * v) := by
          have e : (c * p) * (c * p) = (p * p) * (c * c) := by
            rw [mul_assoc c p _, ← mul_assoc p c p,
                mul_comm p c, mul_assoc c p p, ← mul_assoc, mul_comm (c * c)]
          rw [e]
    _ = (p * p) * ((c * c) * (u * v)) := mul_assoc _ _ _

/-- Positive Theorem 2: For any two normalized pure states `ψ, φ ∈ R^N`, the product of their
    rank-1 density projections `P_ψ P_φ` has exact Gram matrix `⟨ψ, φ⟩² P_φ`, trace `⟨ψ, φ⟩²`,
    and exact top squared singular value `σ₁(P_ψ P_φ)² = ⟨ψ, φ⟩² ≤ 1 = σ₁(P_ψ)² σ₁(P_φ)²`. -/
theorem rankOneProj_prod_singValSq {N : Nat} {ψ φ : Fin N → R}
    (hψ : normSq ψ = 1) (hφ : normSq φ = 1) :
    gram (matMul (outer ψ ψ) (outer φ φ)) = matScale (sq (dot ψ φ)) (outer φ φ) ∧
    matTrace (matMul (outer ψ ψ) (outer φ φ)) = sq (dot ψ φ) ∧
    HasTopSingValSq (matMul (outer ψ ψ) (outer φ φ)) (sq (dot ψ φ)) ∧
    sq (dot ψ φ) ≤ 1 := by
  have hprod : matMul (outer ψ ψ) (outer φ φ) = matScale (dot ψ φ) (outer ψ φ) :=
    outer_mul_outer ψ ψ φ φ
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext i j
    rw [hprod]
    unfold gram matMul matTr matScale outer sq
    calc finSum N (fun k => (dot ψ φ * (ψ k * φ i)) * (dot ψ φ * (ψ k * φ j)))
        = finSum N (fun k => (ψ k * ψ k) * ((dot ψ φ * dot ψ φ) * (φ i * φ j))) :=
            finSum_congr (fun k => quad_scalar_rearrange (dot ψ φ) (ψ k) (φ i) (φ j))
      _ = finSum N (fun k => ψ k * ψ k) * ((dot ψ φ * dot ψ φ) * (φ i * φ j)) :=
            finSum_mul_right N _ _
      _ = (dot ψ φ * dot ψ φ) * (φ i * φ j) := by
            change normSq ψ * _ = _; rw [hψ, one_mul]
  · rw [hprod]
    unfold matTrace matScale outer sq dot
    exact finSum_mul_left N _ _
  · refine ⟨⟨sq_nonneg (dot ψ φ), fun w => ?_⟩, ⟨φ, hφ, ?_⟩⟩
    · rw [hprod]
      have hvec : matVec (matScale (dot ψ φ) (outer ψ φ)) w =
                  fun i => (dot ψ φ * dot φ w) * ψ i := by
        funext i
        unfold matVec matScale outer dot
        calc finSum N (fun j => (finSum N (fun k => ψ k * φ k) * (ψ i * φ j)) * w j)
            = finSum N (fun j => (finSum N (fun k => ψ k * φ k) * ψ i) * (φ j * w j)) :=
                finSum_congr (fun j => by rw [← mul_assoc _ (ψ i) (φ j), mul_assoc _ (φ j) (w j)])
          _ = (finSum N (fun k => ψ k * φ k) * ψ i) * finSum N (fun j => φ j * w j) :=
                finSum_mul_left N _ _
          _ = (finSum N (fun k => ψ k * φ k) * finSum N (fun j => φ j * w j)) * ψ i := by
                rw [mul_assoc, mul_comm (ψ i) _, ← mul_assoc]
      rw [hvec, normSq_scale, hψ, mul_one]
      have hsq : sq (dot ψ φ * dot φ w) = sq (dot ψ φ) * sq (dot φ w) := by
        unfold sq; rw [mul_assoc, ← mul_assoc (dot φ w) (dot ψ φ) _,
                       mul_comm (dot φ w) (dot ψ φ), mul_assoc (dot ψ φ), ← mul_assoc]
      rw [hsq]
      have hcs := cauchy_schwarz_sq φ w
      rw [hφ, one_mul] at hcs
      exact mul_le_mul_of_nonneg_left hcs (sq_nonneg (dot ψ φ))
    · rw [hprod]
      have hvec : matVec (matScale (dot ψ φ) (outer ψ φ)) φ =
                  fun i => dot ψ φ * ψ i := by
        funext i
        unfold matVec matScale outer
        calc finSum N (fun j => (dot ψ φ * (ψ i * φ j)) * φ j)
            = finSum N (fun j => (dot ψ φ * ψ i) * (φ j * φ j)) :=
                finSum_congr (fun j => by rw [← mul_assoc _ (ψ i) (φ j), mul_assoc _ (φ j) (φ j)])
          _ = (dot ψ φ * ψ i) * normSq φ := finSum_mul_left N _ _
          _ = dot ψ φ * ψ i := by rw [hφ, mul_one]
      rw [hvec, normSq_scale, hψ, mul_one]
  · have hcs := cauchy_schwarz_sq ψ φ
    rw [hψ, hφ, one_mul] at hcs
    exact hcs

/-- Saturation characterization for pure-state density projections:
    `σ₁(P_ψ P_φ)² = 1` holds if and only if `P_ψ = P_φ` (state coincidence). -/
theorem rankOneProj_prod_saturated_iff_eq {N : Nat} {ψ φ : Fin N → R}
    (hψ : normSq ψ = 1) (hφ : normSq φ = 1) :
    sq (dot ψ φ) = 1 ↔ outer ψ ψ = outer φ φ := by
  constructor
  · intro hsat
    have hcs_eq : sq (dot ψ φ) = normSq ψ * normSq φ := by rw [hsat, hψ, hφ, one_mul]
    have hcol := (cauchy_schwarz_eq_iff_collinear ψ φ).mp hcs_eq
    funext i j
    unfold outer
    calc ψ i * ψ j
        = (ψ i * ψ j) * normSq φ := by rw [hφ, mul_one]
      _ = finSum N (fun k => (ψ i * ψ j) * (φ k * φ k)) :=
            (finSum_mul_left N (ψ i * ψ j) _).symm
      _ = finSum N (fun k => (ψ i * φ k) * (ψ j * φ k)) := finSum_congr (fun k => by
            rw [mul_assoc (ψ i) (ψ j) _, ← mul_assoc (ψ j) (φ k) (φ k),
                mul_comm (ψ j) (φ k), mul_assoc (φ k) (ψ j) (φ k),
                mul_comm (ψ j) (φ k), ← mul_assoc])
      _ = finSum N (fun k => (φ i * ψ k) * (φ j * ψ k)) :=
            finSum_congr (fun k => by rw [hcol i k, hcol j k])
      _ = finSum N (fun k => (φ i * φ j) * (ψ k * ψ k)) := finSum_congr (fun k => by
            rw [mul_assoc (φ i) (ψ k) _, ← mul_assoc (ψ k) (φ j) (ψ k),
                mul_comm (ψ k) (φ j), mul_assoc (φ j) (ψ k) (ψ k), ← mul_assoc])
      _ = (φ i * φ j) * normSq ψ := finSum_mul_left N (φ i * φ j) _
      _ = φ i * φ j := by rw [hψ, mul_one]
  · intro heq
    unfold sq dot
    calc finSum N (fun i => ψ i * φ i) * finSum N (fun j => ψ j * φ j)
        = finSum N (fun i => finSum N (fun j => (ψ i * φ i) * (ψ j * φ j))) := by
            rw [← finSum_mul_right]
            exact finSum_congr (fun i => (finSum_mul_left N (ψ i * φ i) _).symm)
      _ = finSum N (fun i => finSum N (fun j => (outer ψ ψ i j) * (outer φ φ i j))) :=
            finSum_congr (fun i => finSum_congr (fun j => by
              unfold outer
              rw [mul_assoc (ψ i) (φ i) _, ← mul_assoc (φ i) (ψ j) (φ j),
                  mul_comm (φ i) (ψ j), mul_assoc (ψ j) (φ i) (φ j), ← mul_assoc]))
      _ = finSum N (fun i => finSum N (fun j => (outer ψ ψ i j) * (outer ψ ψ i j))) := by
            rw [← heq]
      _ = finSum N (fun i => (ψ i * ψ i) * finSum N (fun j => ψ j * ψ j)) :=
            finSum_congr (fun i => by
              calc finSum N (fun j => (ψ i * ψ j) * (ψ i * ψ j))
                  = finSum N (fun j => (ψ i * ψ i) * (ψ j * ψ j)) := finSum_congr (fun j => by
                      rw [mul_assoc (ψ i) (ψ j) _, ← mul_assoc (ψ j) (ψ i) (ψ j),
                          mul_comm (ψ j) (ψ i), mul_assoc (ψ i) (ψ j) (ψ j), ← mul_assoc])
                _ = (ψ i * ψ i) * finSum N (fun j => ψ j * ψ j) := finSum_mul_left N _ _)
      _ = normSq ψ * normSq ψ := finSum_mul_right N _ _
      _ = 1 := by rw [hψ, one_mul]

/-- Orthogonal matrix predicate `Q^T Q = I ∧ Q Q^T = I` and orthogonal conjugation `Q X Q^T`. -/
def IsOrthogonal {N : Nat} (Q : Mat R N) : Prop :=
  matMul (matTr Q) Q = matId N ∧ matMul Q (matTr Q) = matId N

def conjBy {N : Nat} (Q X : Mat R N) : Mat R N := matMul (matMul Q X) (matTr Q)

theorem normSq_matVec_orthogonal {N : Nat} {Q : Mat R N} (hQ : IsOrthogonal Q) (v : Fin N → R) :
    normSq (matVec Q v) = normSq v := by
  unfold normSq dot matVec
  calc finSum N (fun i => finSum N (fun j => Q i j * v j) * finSum N (fun k => Q i k * v k))
      = finSum N (fun i => finSum N (fun j => finSum N (fun k => (Q i j * v j) * (Q i k * v k)))) :=
          finSum_congr (fun i => by
            rw [← finSum_mul_right]
            exact finSum_congr (fun j => (finSum_mul_left N _ _).symm))
    _ = finSum N (fun j => finSum N (fun k => finSum N (fun i => (Q i j * Q i k) * (v j * v k)))) := by
          rw [finSum_comm N N]
          refine finSum_congr (fun j => ?_)
          rw [finSum_comm N N]
          refine finSum_congr (fun k => finSum_congr (fun i => ?_))
          rw [mul_assoc (Q i j) (v j) _, ← mul_assoc (v j) (Q i k) (v k),
              mul_comm (v j) (Q i k), mul_assoc (Q i k) (v j) (v k), ← mul_assoc]
    _ = finSum N (fun j => finSum N (fun k => (matMul (matTr Q) Q j k) * (v j * v k))) :=
          finSum_congr (fun j => finSum_congr (fun k => finSum_mul_right N _ _))
    _ = finSum N (fun j => finSum N (fun k => (if k = j then (1 : R) else 0) * (v j * v k))) := by
          rw [hQ.1]
          refine finSum_congr (fun j => finSum_congr (fun k => ?_))
          unfold matId
          by_cases h : j = k
          · subst h; simp
          · have h2 : k ≠ j := fun hk => h hk.symm
            simp [h, h2]
    _ = finSum N (fun j => v j * v j) :=
          finSum_congr (fun j => finSum_ite_eq N j (fun k => v j * v k))

theorem isOrthogonal_matTr {N : Nat} {Q : Mat R N} (hQ : IsOrthogonal Q) :
    IsOrthogonal (matTr Q) := ⟨hQ.2, hQ.1⟩

theorem conjBy_mul {N : Nat} {Q : Mat R N} (hQ : IsOrthogonal Q) (X Y : Mat R N) :
    conjBy Q (matMul X Y) = matMul (conjBy Q X) (conjBy Q Y) := by
  unfold conjBy
  calc matMul (matMul Q (matMul X Y)) (matTr Q)
      = matMul (matMul (matMul Q X) (matId N)) (matMul Y (matTr Q)) := by
          rw [mul_matId, ← matMul_assoc (matMul Q X) Y (matTr Q), matMul_assoc Q X Y]
    _ = matMul (matMul (matMul Q X) (matMul (matTr Q) Q)) (matMul Y (matTr Q)) := by rw [hQ.1]
    _ = matMul (matMul (matMul Q X) (matTr Q)) (matMul (matMul Q Y) (matTr Q)) := by
          rw [← matMul_assoc (matMul Q X) (matTr Q) Q,
              matMul_assoc (matMul (matMul Q X) (matTr Q)) Q (matMul Y (matTr Q)),
              ← matMul_assoc Q Y (matTr Q)]

theorem conjBy_add {N : Nat} (Q X Y : Mat R N) :
    conjBy Q (matAdd X Y) = matAdd (conjBy Q X) (conjBy Q Y) := by
  funext i j
  unfold conjBy matMul matAdd
  calc finSum N (fun k => finSum N (fun l => Q i l * (X l k + Y l k)) * matTr Q k j)
      = finSum N (fun k => (finSum N (fun l => Q i l * X l k) +
                            finSum N (fun l => Q i l * Y l k)) * matTr Q k j) :=
          finSum_congr (fun k => by
            rw [← finSum_add]
            exact congrArg (fun s => s * matTr Q k j) (finSum_congr (fun l => left_distrib _ _ _)))
    _ = finSum N (fun k => finSum N (fun l => Q i l * X l k) * matTr Q k j +
                           finSum N (fun l => Q i l * Y l k) * matTr Q k j) :=
          finSum_congr (fun k => right_distrib _ _ _)
    _ = _ := finSum_add _ _ _

theorem conjBy_outer {N : Nat} (Q : Mat R N) (u v : Fin N → R) :
    conjBy Q (outer u v) = outer (matVec Q u) (matVec Q v) := by
  funext i j
  unfold conjBy matMul matTr outer matVec dot
  calc finSum N (fun k => finSum N (fun l => Q i l * (u l * v k)) * Q j k)
      = finSum N (fun k => (finSum N (fun l => Q i l * u l) * v k) * Q j k) :=
          finSum_congr (fun k => by
            have e : finSum N (fun l => Q i l * (u l * v k)) =
                     finSum N (fun l => Q i l * u l) * v k := by
              calc finSum N (fun l => Q i l * (u l * v k))
                  = finSum N (fun l => (Q i l * u l) * v k) :=
                      finSum_congr (fun l => (mul_assoc _ _ _).symm)
                _ = finSum N (fun l => Q i l * u l) * v k := finSum_mul_right N _ _
            rw [e])
    _ = finSum N (fun k => finSum N (fun l => Q i l * u l) * (Q j k * v k)) :=
          finSum_congr (fun k => by rw [mul_assoc, mul_comm (v k) (Q j k)])
    _ = finSum N (fun l => Q i l * u l) * finSum N (fun k => Q j k * v k) :=
          finSum_mul_left N _ _

theorem opNormSqBound_conjBy {N : Nat} {Q X : Mat R N} {μ : R}
    (hQ : IsOrthogonal Q) (hX : OpNormSqBound X μ) :
    OpNormSqBound (conjBy Q X) μ := by
  refine ⟨hX.1, fun v => ?_⟩
  unfold conjBy
  rw [matVec_matMul, matVec_matMul, normSq_matVec_orthogonal hQ]
  calc normSq (matVec X (matVec (matTr Q) v))
      ≤ μ * normSq (matVec (matTr Q) v) := hX.2 _
    _ = μ * normSq v := by rw [normSq_matVec_orthogonal (isOrthogonal_matTr hQ)]

/-- Global orthogonal conjugation invariance of exact top singular values squared. -/
theorem conjBy_hasTopSingValSq_iff {N : Nat} {Q X : Mat R N} {μ : R}
    (hQ : IsOrthogonal Q) :
    HasTopSingValSq (conjBy Q X) μ ↔ HasTopSingValSq X μ := by
  have hinv : conjBy (matTr Q) (conjBy Q X) = X := by
    unfold conjBy
    have htr : matTr (matTr Q) = Q := rfl
    calc matMul (matMul (matTr Q) (matMul (matMul Q X) (matTr Q))) (matTr (matTr Q))
        = matMul (matMul (matTr Q) (matMul (matMul Q X) (matTr Q))) Q := by rw [htr]
      _ = matMul (matTr Q) (matMul (matMul Q X) (matMul (matTr Q) Q)) := by
            rw [matMul_assoc (matTr Q) _ Q, matMul_assoc (matMul Q X) (matTr Q) Q]
      _ = matMul (matTr Q) (matMul Q X) := by rw [hQ.1, mul_matId]
      _ = matMul (matMul (matTr Q) Q) X := (matMul_assoc _ _ _).symm
      _ = X := by rw [hQ.1, matId_mul]
  constructor
  · intro ⟨hb, ⟨v, hv, heq⟩⟩
    refine ⟨?_, ⟨matVec (matTr Q) v, ?_, ?_⟩⟩
    · rw [← hinv]; exact opNormSqBound_conjBy (isOrthogonal_matTr hQ) hb
    · rw [normSq_matVec_orthogonal (isOrthogonal_matTr hQ), hv]
    · unfold conjBy at heq
      rw [matVec_matMul, matVec_matMul, normSq_matVec_orthogonal hQ] at heq
      exact heq
  · intro ⟨hb, ⟨v, hv, heq⟩⟩
    refine ⟨opNormSqBound_conjBy hQ hb, ⟨matVec Q v, ?_, ?_⟩⟩
    · rw [normSq_matVec_orthogonal hQ, hv]
    · unfold conjBy
      rw [matVec_matMul, matVec_matMul, normSq_matVec_orthogonal hQ]
      have htv : matVec (matTr Q) (matVec Q v) = v := by
        rw [← matVec_matMul, hQ.1, matVec_matId]
      rw [htv, heq]

end MatrixAlgebra

-- ============================================================================
-- §4. Bipartite Quantum Entanglement & General-d Schmidt AM-GM Resolution (Model M3)
-- ============================================================================

section BipartiteAndAMGM
variable {F : Type u} [LinearOrderedField F]

def rhoA {d : Nat} (M : Mat F d) : Mat F d := matMul M (matTr M)
def rhoB {d : Nat} (M : Mat F d) : Mat F d := matMul (matTr M) M

def IsProductState {d : Nat} (M : Mat F d) : Prop :=
  ∃ a b : Fin d → F, normSq a = 1 ∧ normSq b = 1 ∧ M = outer a b

def IsMaximallyEntangled (d : Nat) (M : Mat F d) : Prop :=
  frobSq M = 1 ∧
  rhoA M = matScale (finv (natCast F d)) (matId d) ∧
  rhoB M = matScale (finv (natCast F d)) (matId d)

/-- For every local dimension `d ≥ 2`, no maximally entangled state is a product state. -/
theorem maximallyEntangled_not_productState {d : Nat} (hd : 2 ≤ d) {M : Mat F d}
    (hME : IsMaximallyEntangled d M) : ¬ IsProductState M := by
  rintro ⟨a, b, ha, hb, rfl⟩
  have htr : matTr (outer a b) = outer b a := by
    funext i j; exact mul_comm (a j) (b i)
  have hrho : rhoA (outer a b) = outer a a := by
    unfold rhoA
    rw [htr, outer_mul_outer]
    change matScale (normSq b) (outer a a) = outer a a
    rw [hb]
    funext i j; unfold matScale; exact one_mul _
  have hidem : matMul (rhoA (outer a b)) (rhoA (outer a b)) = rhoA (outer a b) := by
    rw [hrho, outer_mul_outer]
    change matScale (normSq a) (outer a a) = outer a a
    rw [ha]
    funext i j; unfold matScale; exact one_mul _
  rw [hME.2.1] at hidem
  let c : F := finv (natCast F d)
  have h00 := congrFun (congrFun hidem ⟨0, by omega⟩) ⟨0, by omega⟩
  have hsq_id : matMul (matScale c (matId d)) (matScale c (matId d)) ⟨0, by omega⟩ ⟨0, by omega⟩ =
                c * c := by
    have hm : matMul (matScale c (matId d)) (matScale c (matId d)) = matScale (c * c) (matId d) := by
      funext i j
      unfold matMul matScale
      calc finSum d (fun k => (c * matId d i k) * (c * matId d k j))
          = finSum d (fun k => (c * c) * (matId d i k * matId d k j)) := finSum_congr (fun k => by
              rw [mul_assoc c (matId d i k) _, ← mul_assoc (matId d i k) c _,
                  mul_comm (matId d i k) c, mul_assoc c _ _, ← mul_assoc])
        _ = (c * c) * matMul (matId d) (matId d) i j := finSum_mul_left d (c * c) _
        _ = (c * c) * matId d i j := by rw [matId_mul]
    rw [hm]; unfold matScale matId; simp [mul_one]
  have hrhs : matScale c (matId d) ⟨0, by omega⟩ ⟨0, by omega⟩ = c := by
    unfold matScale matId; simp [mul_one]
  rw [hsq_id, hrhs] at h00
  have hd_pos : (0 : F) < natCast F d := natCast_pos (by omega)
  have hc_ne : c ≠ 0 := ne_of_gt (finv_pos hd_pos)
  have hc_one : c = 1 := mul_right_cancel hc_ne (by rw [one_mul]; exact h00)
  have hd_eq_one : natCast F d = 1 := by
    calc natCast F d = natCast F d * 1 := (mul_one _).symm
      _ = natCast F d * c := by rw [hc_one]
      _ = 1 := mul_finv_cancel (ne_of_gt hd_pos)
  have hd_gt_one : (1 : F) < natCast F d := by
    rw [← natCast_one (R := F)]
    exact natCast_lt_natCast (by omega)
  exact ne_of_gt hd_gt_one hd_eq_one

theorem bernoulli_prod_id (m : Nat) (t : F) :
    (1 + t) * (1 - natCast F (m + 1) * t) =
    (1 - natCast F m * t) - natCast F (m + 1) * sq t := by
  unfold sq
  rw [natCast_succ]
  have h1 : (natCast F m + 1) * t = natCast F m * t + t := by rw [right_distrib, one_mul]
  have h2 : (natCast F m + 1) * (t * t) = (natCast F m * t) * t + t * t := by
    rw [right_distrib, one_mul, mul_assoc]
  rw [h1, h2]
  let a := natCast F m * t
  calc (1 + t) * (1 - (a + t))
      = (1 - (a + t)) + (t - t * (a + t)) := by
          rw [right_distrib, one_mul, mul_sub, mul_one]
    _ = (1 + (-(a) + -t)) + (t + -(a * t + t * t)) := by
          rw [sub_eq_add_neg, neg_add, sub_eq_add_neg, left_distrib, mul_comm t a]
    _ = (1 + -(a)) + (-t + (t + -(a * t + t * t))) := by
          rw [← add_assoc 1 (-(a)) (-t), add_assoc (1 + -(a)) (-t) _]
    _ = (1 - a) - (a * t + t * t) := by
          rw [← add_assoc (-t) t _, neg_add_cancel, zero_add, ← sub_eq_add_neg, ← sub_eq_add_neg]

theorem one_add_pow_mul_one_sub_le (t : F) (ht : 0 ≤ 1 + t) :
    ∀ n : Nat, rpow (1 + t) n * (1 - natCast F n * t) ≤ 1
  | 0 => by rw [rpow_zero, natCast_zero, zero_mul, sub_zero, one_mul]; exact le_refl 1
  | m + 1 => by
    have ih := one_add_pow_mul_one_sub_le t ht m
    have hdrop : 0 ≤ rpow (1 + t) m * (natCast F (m + 1) * sq t) :=
      mul_nonneg (rpow_nonneg ht m) (mul_nonneg (natCast_nonneg (m + 1)) (sq_nonneg t))
    have hstep : rpow (1 + t) (m + 1) * (1 - natCast F (m + 1) * t) =
                 rpow (1 + t) m * (1 - natCast F m * t) -
                 rpow (1 + t) m * (natCast F (m + 1) * sq t) := by
      rw [rpow_succ, mul_assoc, bernoulli_prod_id, mul_sub]
    rw [hstep]
    have hle : rpow (1 + t) m * (1 - natCast F m * t) -
               rpow (1 + t) m * (natCast F (m + 1) * sq t) ≤
               rpow (1 + t) m * (1 - natCast F m * t) := by
      apply le_of_sub_nonneg
      let A := rpow (1 + t) m * (1 - natCast F m * t)
      let D := rpow (1 + t) m * (natCast F (m + 1) * sq t)
      have heq : A - (A - D) = D := by
        rw [sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_neg, ← add_assoc, add_neg_cancel, zero_add]
      rw [heq]; exact hdrop
    exact le_trans hle ih

theorem one_add_pow_mul_one_sub_eq_one_imp_zero {m : Nat} {t : F}
    (ht : 0 ≤ 1 + t)
    (heq : rpow (1 + t) (m + 1) * (1 - natCast F (m + 1) * t) = 1) : t = 0 := by
  by_cases h1t : 1 + t = 0
  · exfalso
    rw [rpow_succ, h1t, mul_zero, zero_mul] at heq
    exact one_ne_zero heq.symm
  · have hpos1t : 0 < 1 + t := lt_of_le_of_ne ht (fun h => h1t h.symm)
    have hp_pow : 0 < rpow (1 + t) m := rpow_pos hpos1t m
    have hp_m1 : (0 : F) < natCast F (m + 1) := natCast_pos (by omega)
    have hstep : rpow (1 + t) (m + 1) * (1 - natCast F (m + 1) * t) =
                 rpow (1 + t) m * (1 - natCast F m * t) -
                 rpow (1 + t) m * (natCast F (m + 1) * sq t) := by
      rw [rpow_succ, mul_assoc, bernoulli_prod_id, mul_sub]
    have ih := one_add_pow_mul_one_sub_le t ht m
    by_cases htz : t = 0
    · exact htz
    · exfalso
      have hposD : 0 < rpow (1 + t) m * (natCast F (m + 1) * sq t) :=
        mul_pos hp_pow (mul_pos hp_m1 (sq_pos_of_ne_zero htz))
      have hAD : rpow (1 + t) m * (1 - natCast F m * t) =
                 1 + rpow (1 + t) m * (natCast F (m + 1) * sq t) := by
        have h2 := congrArg (fun z => z + rpow (1 + t) m * (natCast F (m + 1) * sq t))
                     (hstep.symm.trans heq)
        dsimp at h2
        rw [sub_add_cancel] at h2
        exact h2
      rw [hAD] at ih
      have hle0 := add_le_add_left ih (-1)
      rw [← add_assoc, neg_add_cancel, zero_add] at hle0
      exact (lt_iff_le_not_le.mp hposD).2 hle0

private theorem avg_last_linear_id (k : Nat) (A1 t : F) :
    (natCast F k + 1) * A1 - natCast F k * (A1 * (1 + t)) =
    A1 * (1 - natCast F k * t) := by
  calc (natCast F k + 1) * A1 - natCast F k * (A1 * (1 + t))
      = (A1 * natCast F k + A1) - A1 * (natCast F k + natCast F k * t) := by
          rw [right_distrib, one_mul, mul_comm (natCast F k) A1,
              ← mul_assoc (natCast F k) A1 (1 + t), mul_comm (natCast F k) A1,
              mul_assoc A1 (natCast F k) (1 + t), left_distrib (natCast F k) 1 t, mul_one]
    _ = A1 - A1 * (natCast F k * t) := by
          rw [left_distrib A1 (natCast F k) _, sub_eq_add_neg, neg_add]
          let u := A1 * natCast F k
          let v := A1 * (natCast F k * t)
          calc (u + A1) + (-u + -v)
              = A1 + (u + (-u + -v)) := by rw [add_comm u A1, add_assoc]
            _ = A1 + -v := by rw [← add_assoc u (-u) (-v), add_neg_cancel, zero_add]
            _ = A1 - v := (sub_eq_add_neg _ _).symm
    _ = A1 * (1 - natCast F k * t) := by rw [mul_sub, mul_one]

/-- General-d AM-GM inequality over any `LinearOrderedField F`. -/
theorem am_gm : ∀ (d : Nat), 1 ≤ d → ∀ (x : Fin d → F), (∀ i, 0 ≤ x i) →
    finProd d x ≤ rpow (fdiv (finSum d x) (natCast F d)) d
  | 0, hd, _, _ => by omega
  | 1, _, x, _ => by
    dsimp [finProd, finSum, fdiv]
    rw [natCast_one, finv_one, mul_one, zero_add, rpow_one, one_mul]
    exact le_refl _
  | m + 2, _, x, hx => by
    let k := m + 1
    let xi : Fin k → F := fun i => x ⟨i.1, Nat.lt_succ_of_lt i.2⟩
    let xl : F := x ⟨k, Nat.lt_succ_self k⟩
    have ih := am_gm k (by omega) xi (fun i => hx _)
    let Sk := finSum k xi
    let S1 := finSum (k + 1) x
    have hS1_eq : S1 = Sk + xl := rfl
    have hSk_nn : 0 ≤ Sk := finSum_nonneg (fun i => hx _)
    have hxl_nn : 0 ≤ xl := hx _
    have hS1_nn : 0 ≤ S1 := by rw [hS1_eq]; exact le_trans hSk_nn (by
      have h := add_le_add_left hxl_nn Sk; rw [add_zero] at h; exact h)
    have hk_pos : (0 : F) < natCast F k := natCast_pos (by omega)
    have hk1_pos : (0 : F) < natCast F (k + 1) := natCast_pos (by omega)
    let Ak := fdiv Sk (natCast F k)
    let A1 := fdiv S1 (natCast F (k + 1))
    by_cases hS1z : S1 = 0
    · have hall0 := (finSum_eq_zero_iff_of_nonneg hx).mp hS1z
      have hxl0 : xl = 0 := hall0 ⟨k, Nat.lt_succ_self k⟩
      change finProd k xi * xl ≤ rpow A1 (k + 1)
      rw [hxl0, mul_zero]
      have hA1z : A1 = 0 := by unfold A1 fdiv; rw [hS1z, zero_mul]
      rw [hA1z, rpow_succ, mul_zero]
      exact le_refl 0
    · have hS1_pos : 0 < S1 := lt_of_le_of_ne hS1_nn (fun h => hS1z h.symm)
      have hA1_pos : 0 < A1 := mul_pos hS1_pos (finv_pos hk1_pos)
      have hAk_nn : 0 ≤ Ak := mul_nonneg hSk_nn (finv_nonneg hk_pos)
      let t : F := fdiv Ak A1 - 1
      have h1t : 1 + t = fdiv Ak A1 := by unfold t; rw [add_comm, sub_add_cancel]
      have h1t_nn : 0 ≤ 1 + t := by rw [h1t]; exact mul_nonneg hAk_nn (finv_nonneg hA1_pos)
      have hAk_eq : Ak = A1 * (1 + t) := by
        rw [h1t]; unfold fdiv
        rw [mul_comm A1 (Ak * finv A1), mul_assoc, finv_mul_cancel (ne_of_gt hA1_pos), mul_one]
      have hSk_eq : Sk = natCast F k * Ak := by
        unfold Ak fdiv
        rw [mul_comm (natCast F k) _, mul_assoc, finv_mul_cancel (ne_of_gt hk_pos), mul_one]
      have hS1_eq2 : S1 = natCast F (k + 1) * A1 := by
        unfold A1 fdiv
        rw [mul_comm (natCast F (k + 1)) _, mul_assoc, finv_mul_cancel (ne_of_gt hk1_pos), mul_one]
      have hxl_eq : xl = A1 * (1 - natCast F k * t) := by
        have hsum_rel : Sk + xl = natCast F (k + 1) * A1 := hS1_eq.symm.trans hS1_eq2
        have hxl_sub : xl = natCast F (k + 1) * A1 - Sk := by
          have h2 := congrArg (fun z => -Sk + z) hsum_rel
          dsimp at h2
          rw [← add_assoc, neg_add_cancel, zero_add] at h2
          rw [h2, sub_eq_add_neg, add_comm]
        rw [hxl_sub, hSk_eq, hAk_eq, natCast_succ]
        exact avg_last_linear_id k A1 t
      change finProd k xi * xl ≤ rpow A1 (k + 1)
      have hmul : finProd k xi * xl ≤ rpow Ak k * xl :=
        mul_le_mul_of_nonneg_right ih hxl_nn
      have hrhs_id : rpow Ak k * xl =
                     rpow A1 (k + 1) * (rpow (1 + t) k * (1 - natCast F k * t)) := by
        rw [hAk_eq, rpow_mul, hxl_eq]
        calc (rpow A1 k * rpow (1 + t) k) * (A1 * (1 - natCast F k * t))
            = (rpow A1 k * A1) * (rpow (1 + t) k * (1 - natCast F k * t)) := by
                rw [mul_assoc (rpow A1 k), ← mul_assoc (rpow (1 + t) k) A1 _,
                    mul_comm (rpow (1 + t) k) A1, mul_assoc A1 _ _, ← mul_assoc]
          _ = rpow A1 (k + 1) * (rpow (1 + t) k * (1 - natCast F k * t)) := rfl
      have hbern := one_add_pow_mul_one_sub_le t h1t_nn k
      have hstep2 : rpow A1 (k + 1) * (rpow (1 + t) k * (1 - natCast F k * t)) ≤
                    rpow A1 (k + 1) * 1 :=
        mul_le_mul_of_nonneg_left hbern (rpow_nonneg (le_of_lt hA1_pos) (k + 1))
      rw [mul_one] at hstep2
      rw [hrhs_id] at hmul
      exact le_trans hmul hstep2

/-- Equality characterization in AM-GM: equality holds iff all `x_i` are equal. -/
theorem am_gm_eq_iff : ∀ (d : Nat), 1 ≤ d → ∀ (x : Fin d → F), (∀ i, 0 ≤ x i) →
    (finProd d x = rpow (fdiv (finSum d x) (natCast F d)) d ↔ ∀ i j : Fin d, x i = x j)
  | 0, hd, _, _ => by omega
  | 1, _, x, _ => by
    constructor
    · intro _ i j
      have hi : i = ⟨0, by decide⟩ := Fin.ext (by have := i.2; omega)
      have hj : j = ⟨0, by decide⟩ := Fin.ext (by have := j.2; omega)
      rw [hi, hj]
    · intro _
      dsimp [finProd, finSum, fdiv]
      rw [natCast_one, finv_one, mul_one, zero_add, rpow_one, one_mul]
  | m + 2, _, x, hx => by
    let k := m + 1
    let xi : Fin k → F := fun i => x ⟨i.1, Nat.lt_succ_of_lt i.2⟩
    let xl : F := x ⟨k, Nat.lt_succ_self k⟩
    let Sk := finSum k xi
    let S1 := finSum (k + 1) x
    have hk_pos : (0 : F) < natCast F k := natCast_pos (by omega)
    have hk1_pos : (0 : F) < natCast F (k + 1) := natCast_pos (by omega)
    let Ak := fdiv Sk (natCast F k)
    let A1 := fdiv S1 (natCast F (k + 1))
    constructor
    · intro heq
      have hS1_nn : 0 ≤ S1 := finSum_nonneg hx
      by_cases hS1z : S1 = 0
      · have hall0 := (finSum_eq_zero_iff_of_nonneg hx).mp hS1z
        intro i j; rw [hall0 i, hall0 j]
      · have hS1_pos : 0 < S1 := lt_of_le_of_ne hS1_nn (fun h => hS1z h.symm)
        have hA1_pos : 0 < A1 := mul_pos hS1_pos (finv_pos hk1_pos)
        have hSk_nn : 0 ≤ Sk := finSum_nonneg (fun i => hx _)
        have hAk_nn : 0 ≤ Ak := mul_nonneg hSk_nn (finv_nonneg hk_pos)
        let t : F := fdiv Ak A1 - 1
        have h1t : 1 + t = fdiv Ak A1 := by unfold t; rw [add_comm, sub_add_cancel]
        have h1t_nn : 0 ≤ 1 + t := by rw [h1t]; exact mul_nonneg hAk_nn (finv_nonneg hA1_pos)
        have hAk_eq : Ak = A1 * (1 + t) := by
          rw [h1t]; unfold fdiv
          rw [mul_comm A1 (Ak * finv A1), mul_assoc, finv_mul_cancel (ne_of_gt hA1_pos), mul_one]
        have hSk_eq : Sk = natCast F k * Ak := by
          unfold Ak fdiv
          rw [mul_comm (natCast F k) _, mul_assoc, finv_mul_cancel (ne_of_gt hk_pos), mul_one]
        have hS1_eq2 : S1 = natCast F (k + 1) * A1 := by
          unfold A1 fdiv
          rw [mul_comm (natCast F (k + 1)) _, mul_assoc, finv_mul_cancel (ne_of_gt hk1_pos), mul_one]
        have hxl_eq : xl = A1 * (1 - natCast F k * t) := by
          have hsum_rel : Sk + xl = natCast F (k + 1) * A1 := hS1_eq2
          have hxl_sub : xl = natCast F (k + 1) * A1 - Sk := by
            have h2 := congrArg (fun z => -Sk + z) hsum_rel
            dsimp at h2
            rw [← add_assoc, neg_add_cancel, zero_add] at h2
            rw [h2, sub_eq_add_neg, add_comm]
          rw [hxl_sub, hSk_eq, hAk_eq, natCast_succ]
          exact avg_last_linear_id k A1 t
        have ih_le := am_gm k (by omega) xi (fun i => hx _)
        have hmul : finProd k xi * xl ≤ rpow Ak k * xl :=
          mul_le_mul_of_nonneg_right ih_le (hx _)
        have hrhs_id : rpow Ak k * xl =
                       rpow A1 (k + 1) * (rpow (1 + t) k * (1 - natCast F k * t)) := by
          rw [hAk_eq, rpow_mul, hxl_eq]
          calc (rpow A1 k * rpow (1 + t) k) * (A1 * (1 - natCast F k * t))
              = (rpow A1 k * A1) * (rpow (1 + t) k * (1 - natCast F k * t)) := by
                  rw [mul_assoc (rpow A1 k), ← mul_assoc (rpow (1 + t) k) A1 _,
                      mul_comm (rpow (1 + t) k) A1, mul_assoc A1 _ _, ← mul_assoc]
            _ = rpow A1 (k + 1) * (rpow (1 + t) k * (1 - natCast F k * t)) := rfl
        have hbern := one_add_pow_mul_one_sub_le t h1t_nn k
        have hstep2 : rpow A1 (k + 1) * (rpow (1 + t) k * (1 - natCast F k * t)) ≤
                      rpow A1 (k + 1) := by
          have h := mul_le_mul_of_nonneg_left hbern (rpow_nonneg (le_of_lt hA1_pos) (k + 1))
          rw [mul_one] at h; exact h
        change finProd k xi * xl = rpow A1 (k + 1) at heq
        have hmid_eq : rpow A1 (k + 1) * (rpow (1 + t) k * (1 - natCast F k * t)) =
                       rpow A1 (k + 1) := by
          apply le_antisymm hstep2
          rw [← hrhs_id, ← heq]; exact hmul
        have hfac1 : rpow (1 + t) k * (1 - natCast F k * t) = 1 := by
          apply mul_right_cancel (ne_of_gt (rpow_pos hA1_pos (k + 1)))
          rw [mul_comm _ (rpow A1 (k + 1)), one_mul]
          exact hmid_eq
        have ht0 : t = 0 := one_add_pow_mul_one_sub_eq_one_imp_zero h1t_nn hfac1
        have hAk_A1 : Ak = A1 := by rw [hAk_eq, ht0, add_zero, mul_one]
        have hxl_A1 : xl = A1 := by rw [hxl_eq, ht0, mul_zero, sub_zero, mul_one]
        have hprod_k : finProd k xi = rpow Ak k := by
          apply mul_right_cancel (ne_of_gt hA1_pos)
          rw [← hxl_A1, heq, hxl_A1, hAk_A1]; rfl
        have hall_k := (am_gm_eq_iff k (by omega) xi (fun i => hx _)).mp hprod_k
        have hxi0_Ak : xi ⟨0, by omega⟩ = Ak := by
          have hconst : Sk = finSum k (fun _ => xi ⟨0, by omega⟩) :=
            finSum_congr (fun i => hall_k i ⟨0, by omega⟩)
          rw [finSum_const] at hconst
          apply mul_right_cancel (ne_of_gt hk_pos)
          rw [mul_comm _ (natCast F k), ← hconst, hSk_eq, mul_comm]
        have hall_A1 : ∀ i : Fin (k + 1), x i = A1 := by
          intro i
          by_cases hi : i.1 < k
          · calc x i = xi ⟨i.1, hi⟩ := rfl
              _ = xi ⟨0, by omega⟩ := hall_k ⟨i.1, hi⟩ ⟨0, by omega⟩
              _ = Ak := hxi0_Ak
              _ = A1 := hAk_A1
          · have hieq : i = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext (by dsimp; have := i.2; omega)
            rw [hieq]; exact hxl_A1
        intro i j; rw [hall_A1 i, hall_A1 j]
    · intro hall
      let c := x ⟨0, by omega⟩
      have hsum_c : S1 = natCast F (k + 1) * c := by
        calc S1 = finSum (k + 1) (fun _ => c) := finSum_congr (fun i => hall i ⟨0, by omega⟩)
          _ = natCast F (k + 1) * c := finSum_const _ _
      have hA1_c : A1 = c := by
        unfold A1 fdiv
        rw [hsum_c, mul_comm (natCast F (k + 1)) c, mul_assoc,
            mul_finv_cancel (ne_of_gt hk1_pos), mul_one]
      have hprod_c : finProd (k + 1) x = rpow c (k + 1) := by
        have hpc : ∀ (n : Nat) (f : Fin n → F), (∀ i, f i = c) → finProd n f = rpow c n := by
          intro n f hf
          induction n with
          | zero => rfl
          | succ n ih =>
            unfold finProd
            rw [ih _ (fun i => hf _), hf _, rpow_succ]
        exact hpc (k + 1) x (fun i => hall i ⟨0, by omega⟩)
      change finProd (k + 1) x = rpow A1 (k + 1)
      rw [hprod_c, hA1_c]

/-- Positive Theorem 3 (Model M3, Full k = d Product):
    For every `d ≥ 1` and squared Schmidt spectrum `w` (`∀ i, 0 ≤ w_i`, `∑ w_i = 1`),
    `∏ w_i ≤ (1/d)^d`, with equality iff `w_i = 1/d` for all `i` (maximal entanglement). -/
theorem schmidt_full_product_max_iff_maximally_entangled
    {d : Nat} (hd : 1 ≤ d) (w : Fin d → F)
    (hw_nn : ∀ i, 0 ≤ w i) (hw_sum : finSum d w = 1) :
    finProd d w ≤ rpow (finv (natCast F d)) d ∧
    (finProd d w = rpow (finv (natCast F d)) d ↔ ∀ i : Fin d, w i = finv (natCast F d)) := by
  have hd_pos : (0 : F) < natCast F d := natCast_pos (by omega)
  have havg : fdiv (finSum d w) (natCast F d) = finv (natCast F d) := by
    unfold fdiv; rw [hw_sum, one_mul]
  refine ⟨?_, ?_⟩
  · have hb := am_gm d hd w hw_nn
    rw [havg] at hb; exact hb
  · have heq_iff := am_gm_eq_iff d hd w hw_nn
    rw [havg] at heq_iff
    rw [heq_iff]
    constructor
    · intro hall i
      have hconst : finSum d w = finSum d (fun _ => w i) :=
        finSum_congr (fun j => hall j i)
      rw [finSum_const, hw_sum] at hconst
      calc w i = w i * (natCast F d * finv (natCast F d)) := by
            rw [mul_finv_cancel (ne_of_gt hd_pos), mul_one]
        _ = (natCast F d * w i) * finv (natCast F d) := by
            rw [← mul_assoc, mul_comm (w i) (natCast F d)]
        _ = 1 * finv (natCast F d) := by rw [← hconst]
        _ = finv (natCast F d) := one_mul _
    · intro hme i j; rw [hme i, hme j]

theorem finSum_prefix_le_of_nonneg {d k : Nat} (hkd : k ≤ d) (w : Fin d → F)
    (hw : ∀ i, 0 ≤ w i) :
    finSum k (fun j => w ⟨j.1, Nat.lt_of_lt_of_le j.2 hkd⟩) ≤ finSum d w := by
  induction d with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0; exact le_refl 0
  | succ n ih =>
    by_cases hkn : k ≤ n
    · have step1 := ih hkn (fun i => w ⟨i.1, Nat.lt_succ_of_lt i.2⟩) (fun i => hw _)
      have hlast : 0 ≤ w ⟨n, Nat.lt_succ_self n⟩ := hw _
      change finSum k (fun j => w ⟨j.1, Nat.lt_of_lt_of_le j.2 hkd⟩) ≤
             finSum n (fun i => w ⟨i.1, Nat.lt_succ_of_lt i.2⟩) + w ⟨n, Nat.lt_succ_self n⟩
      have step2 := add_le_add step1 hlast
      rw [add_zero] at step2
      exact step2
    · have hkeq : k = n + 1 := by omega
      subst hkeq
      exact le_refl _

def schmidtRankKSpectrum (F : Type u) [LinearOrderedField F] (d k : Nat) : Fin d → F :=
  fun i => if i.1 < k then finv (natCast F k) else 0

def schmidtMaxEntSpectrum (F : Type u) [LinearOrderedField F] (d : Nat) : Fin d → F :=
  fun _ => finv (natCast F d)

theorem schmidtRankKSpectrum_sum {d k : Nat} (hk1 : 1 ≤ k) (hkd : k ≤ d) :
    finSum d (schmidtRankKSpectrum F d k) = 1 := by
  have haux : ∀ n : Nat, k ≤ n →
      finSum n (fun i : Fin n => if i.1 < k then finv (natCast F k) else 0) = 1 := by
    intro n hkn
    induction n with
    | zero => omega
    | succ m ih =>
      by_cases hkm : k ≤ m
      · change finSum m (fun i => if i.1 < k then finv (natCast F k) else 0) +
                 (if m < k then finv (natCast F k) else 0) = 1
        have hnot : ¬ (m < k) := by omega
        rw [ih hkm]
        simp [hnot, add_zero]
      · have hkeq : k = m + 1 := by omega
        subst hkeq
        have hall : finSum (m + 1) (fun i : Fin (m + 1) =>
            if i.1 < m + 1 then finv (natCast F (m + 1)) else 0) =
            finSum (m + 1) (fun _ => finv (natCast F (m + 1))) :=
          finSum_congr (fun i => by simp [i.2])
        rw [hall, finSum_const, mul_finv_cancel (ne_of_gt (natCast_pos (by omega)))]
  exact haux d hkd

/-- Complete Refutation of Maximal-Entanglement Saturation for Proper Schmidt Partial Products
    (`1 ≤ k < d`, all `d ≥ 2`, Model M3). -/
theorem schmidt_proper_partial_product_refutation
    {d k : Nat} (hk1 : 1 ≤ k) (hkd : k < d) :
    (∀ w : Fin d → F, (∀ i, 0 ≤ w i) → finSum d w = 1 →
      finProd k (fun j => w ⟨j.1, Nat.lt_trans j.2 hkd⟩) ≤ rpow (finv (natCast F k)) k) ∧
    ((∀ i, 0 ≤ schmidtRankKSpectrum F d k i) ∧
     finSum d (schmidtRankKSpectrum F d k) = 1 ∧
     finProd k (fun j => schmidtRankKSpectrum F d k ⟨j.1, Nat.lt_trans j.2 hkd⟩) =
       rpow (finv (natCast F k)) k ∧
     ¬ (∀ i : Fin d, schmidtRankKSpectrum F d k i = finv (natCast F d))) ∧
    (finProd k (fun j => schmidtMaxEntSpectrum F d ⟨j.1, Nat.lt_trans j.2 hkd⟩) <
       rpow (finv (natCast F k)) k) ∧
    (∀ w : Fin d → F, finSum d w = 1 → (∀ i, w i ≤ w ⟨0, by omega⟩) →
      finv (natCast F d) ≤ w ⟨0, by omega⟩) := by
  have hk_pos : (0 : F) < natCast F k := natCast_pos (by omega)
  have hd_pos : (0 : F) < natCast F d := natCast_pos (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw hsum
    let wk : Fin k → F := fun j => w ⟨j.1, Nat.lt_trans j.2 hkd⟩
    have hpre : finSum k wk ≤ 1 := by
      rw [← hsum]; exact finSum_prefix_le_of_nonneg (Nat.le_of_lt hkd) w hw
    have ham := am_gm k hk1 wk (fun j => hw _)
    have havg_le : fdiv (finSum k wk) (natCast F k) ≤ finv (natCast F k) := by
      unfold fdiv
      have h1 := mul_le_mul_of_nonneg_right hpre (finv_nonneg hk_pos)
      rw [one_mul] at h1; exact h1
    have havg_nn : 0 ≤ fdiv (finSum k wk) (natCast F k) :=
      mul_nonneg (finSum_nonneg (fun j => hw _)) (finv_nonneg hk_pos)
    exact le_trans ham (rpow_le_rpow havg_nn havg_le k)
  · refine ⟨?_, schmidtRankKSpectrum_sum hk1 (Nat.le_of_lt hkd), ?_, ?_⟩
    · intro i; unfold schmidtRankKSpectrum
      by_cases hi : i.1 < k
      · simp [hi]; exact finv_nonneg hk_pos
      · simp [hi]; exact le_refl 0
    · have hconst : (fun j : Fin k => schmidtRankKSpectrum F d k ⟨j.1, Nat.lt_trans j.2 hkd⟩) =
                    (fun _ : Fin k => finv (natCast F k)) := by
        funext j; unfold schmidtRankKSpectrum; simp [j.2]
      rw [hconst, finProd_const]
    · intro hall
      have hlast := hall ⟨k, hkd⟩
      unfold schmidtRankKSpectrum at hlast
      have hnot : ¬ (k < k) := by omega
      simp [hnot] at hlast
      exact ne_of_gt (finv_pos hd_pos) hlast.symm
  · unfold schmidtMaxEntSpectrum
    rw [finProd_const]
    have hlt_cast : natCast F k < natCast F d := natCast_lt_natCast hkd
    have hlt_inv : finv (natCast F d) < finv (natCast F k) := finv_lt_finv hk_pos hlt_cast
    exact rpow_lt_rpow (finv_nonneg hd_pos) hlt_inv k hk1
  · intro w hsum hmax
    have hle_const : 1 ≤ natCast F d * w ⟨0, by omega⟩ := by
      rw [← hsum, ← finSum_const]
      exact finSum_le_finSum hmax
    have hmul := mul_le_mul_of_nonneg_left hle_const (finv_nonneg hd_pos)
    rw [mul_one, ← mul_assoc, finv_mul_cancel (ne_of_gt hd_pos), one_mul] at hmul
    exact hmul

end BipartiteAndAMGM

-- ============================================================================
-- §5. Exact Rational Counterexamples Across Operator, AW POVM, & Marginal Models
-- ============================================================================

section IntTransportAndCounterexamples

theorem fin2_all {P : Fin 2 → Prop}
    (h0 : P ⟨0, by decide⟩) (h1 : P ⟨1, by decide⟩) (i : Fin 2) : P i := by
  match i with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1
  | ⟨_ + 2, h⟩ => omega

theorem fin4_all {P : Fin 4 → Prop}
    (h0 : P ⟨0, by decide⟩) (h1 : P ⟨1, by decide⟩)
    (h2 : P ⟨2, by decide⟩) (h3 : P ⟨3, by decide⟩) (i : Fin 4) : P i := by
  match i with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1
  | ⟨2, _⟩ => exact h2
  | ⟨3, _⟩ => exact h3
  | ⟨_ + 4, h⟩ => omega

def vecOfInt (R : Type u) [LinearOrderedCommRing R] {N : Nat} (v : Fin N → Int) : Fin N → R :=
  fun i => ofInt R (v i)

def matOfInt (R : Type u) [LinearOrderedCommRing R] {N : Nat} (A : Mat Int N) : Mat R N :=
  fun i j => ofInt R (A i j)

section TransportLemmas
variable {R : Type u} [LinearOrderedCommRing R]

theorem finSum_ofInt : ∀ (N : Nat) (f : Fin N → Int),
    finSum N (fun i => ofInt R (f i)) = ofInt R (finSum N f)
  | 0, _ => rfl
  | n + 1, f => by
    unfold finSum
    rw [finSum_ofInt n (fun i => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩), ← ofInt_add]

theorem dot_vecOfInt {N : Nat} (u v : Fin N → Int) :
    dot (vecOfInt R u) (vecOfInt R v) = ofInt R (dot u v) := by
  unfold dot vecOfInt
  calc finSum N (fun i => ofInt R (u i) * ofInt R (v i))
      = finSum N (fun i => ofInt R (u i * v i)) := finSum_congr (fun i => (ofInt_mul _ _).symm)
    _ = ofInt R (finSum N (fun i => u i * v i)) := finSum_ofInt N _

theorem normSq_vecOfInt {N : Nat} (u : Fin N → Int) :
    normSq (vecOfInt R u) = ofInt R (normSq u) :=
  dot_vecOfInt u u

theorem matMul_matOfInt {N : Nat} (A B : Mat Int N) :
    matMul (matOfInt R A) (matOfInt R B) = matOfInt R (matMul A B) := by
  funext i j
  unfold matMul matOfInt
  calc finSum N (fun k => ofInt R (A i k) * ofInt R (B k j))
      = finSum N (fun k => ofInt R (A i k * B k j)) := finSum_congr (fun k => (ofInt_mul _ _).symm)
    _ = ofInt R (finSum N (fun k => A i k * B k j)) := finSum_ofInt N _

theorem matTr_matOfInt {N : Nat} (A : Mat Int N) :
    matTr (matOfInt R A) = matOfInt R (matTr A) := rfl

theorem outer_vecOfInt {N : Nat} (u v : Fin N → Int) :
    outer (vecOfInt R u) (vecOfInt R v) = matOfInt R (outer u v) := by
  funext i j; unfold outer vecOfInt matOfInt; exact (ofInt_mul _ _).symm

theorem frobSq_matOfInt {N : Nat} (A : Mat Int N) :
    frobSq (matOfInt R A) = ofInt R (frobSq A) := by
  unfold frobSq
  calc finSum N (fun i => normSq (matOfInt R A i))
      = finSum N (fun i => ofInt R (normSq (A i))) :=
          finSum_congr (fun i => normSq_vecOfInt (A i))
    _ = ofInt R (finSum N (fun i => normSq (A i))) := finSum_ofInt N _

theorem matOfInt_scale_id (N : Nat) (k : Int) :
    matOfInt R (matScale k (matId N)) = matScale (ofInt R k) (matId N) := by
  funext i j
  unfold matOfInt matScale matId
  by_cases h : i = j
  · subst h; simp [Int.mul_one, mul_one]
  · simp [h, Int.mul_zero, mul_zero]; rfl

theorem matVec_matOfInt {N : Nat} (A : Mat Int N) (v : Fin N → Int) :
    matVec (matOfInt R A) (vecOfInt R v) = vecOfInt R (matVec A v) := by
  funext i; exact dot_vecOfInt (A i) v

def matDiag {N : Nat} (d : Fin N → R) : Mat R N := fun i j => if i = j then d i else 0

theorem matVec_matDiag {N : Nat} (d v : Fin N → R) :
    matVec (matDiag d) v = fun i => d i * v i := by
  funext i
  unfold matVec dot matDiag
  have hconv : (fun j : Fin N => (if i = j then d i else 0) * v j) =
               (fun j : Fin N => (if j = i then (1 : R) else 0) * (d i * v j)) := by
    funext j
    by_cases h : i = j
    · subst h; simp [one_mul]
    · have h2 : j ≠ i := fun hj => h hj.symm
      simp [h, h2, zero_mul]
  rw [hconv, finSum_ite_eq]

theorem matDiag_opNormSqBound {N : Nat} (d : Fin N → R) (μ : R)
    (hμ : 0 ≤ μ) (hd : ∀ i, sq (d i) ≤ μ) :
    OpNormSqBound (matDiag d) μ := by
  refine ⟨hμ, fun v => ?_⟩
  rw [matVec_matDiag]
  unfold normSq dot
  calc finSum N (fun i => (d i * v i) * (d i * v i))
      = finSum N (fun i => sq (d i) * sq (v i)) := finSum_congr (fun i => by
          unfold sq
          rw [mul_assoc (d i) (v i) _, ← mul_assoc (v i) (d i) (v i),
              mul_comm (v i) (d i), mul_assoc (d i) (v i) (v i), ← mul_assoc])
    _ ≤ finSum N (fun i => μ * sq (v i)) :=
          finSum_le_finSum (fun i => mul_le_mul_of_nonneg_right (hd i) (sq_nonneg (v i)))
    _ = μ * finSum N (fun i => v i * v i) := finSum_mul_left N μ (fun i => v i * v i)

def vecScale {N : Nat} (c : R) (v : Fin N → R) : Fin N → R := fun i => c * v i

theorem dot_vecScale {N : Nat} (c d : R) (u v : Fin N → R) :
    dot (vecScale c u) (vecScale d v) = (c * d) * dot u v := by
  unfold dot vecScale
  calc finSum N (fun i => (c * u i) * (d * v i))
      = finSum N (fun i => (c * d) * (u i * v i)) := finSum_congr (fun i => by
          rw [mul_assoc c (u i) _, ← mul_assoc (u i) d (v i),
              mul_comm (u i) d, mul_assoc d (u i) (v i), ← mul_assoc])
    _ = (c * d) * finSum N (fun i => u i * v i) := finSum_mul_left N (c * d) _

theorem outer_vecScale {N : Nat} (c d : R) (u v : Fin N → R) :
    outer (vecScale c u) (vecScale d v) = matScale (c * d) (outer u v) := by
  funext i j
  unfold outer vecScale matScale
  rw [mul_assoc c (u i) _, ← mul_assoc (u i) d (v j),
      mul_comm (u i) d, mul_assoc d (u i) (v j), ← mul_assoc]

theorem matMul_matScale {N : Nat} (a b : R) (A B : Mat R N) :
    matMul (matScale a A) (matScale b B) = matScale (a * b) (matMul A B) := by
  funext i j
  unfold matMul matScale
  calc finSum N (fun k => (a * A i k) * (b * B k j))
      = finSum N (fun k => (a * b) * (A i k * B k j)) := finSum_congr (fun k => by
          rw [mul_assoc a (A i k) _, ← mul_assoc (A i k) b (B k j),
              mul_comm (A i k) b, mul_assoc b (A i k) (B k j), ← mul_assoc])
    _ = (a * b) * finSum N (fun k => A i k * B k j) := finSum_mul_left N (a * b) _

theorem matScale_matScale {N : Nat} (a b : R) (A : Mat R N) :
    matScale a (matScale b A) = matScale (a * b) A := by
  funext i j; unfold matScale; exact (mul_assoc a b (A i j)).symm

theorem matScale_one {N : Nat} (A : Mat R N) : matScale 1 A = A := by
  funext i j; unfold matScale; exact one_mul (A i j)

theorem frobSq_matScale {N : Nat} (c : R) (A : Mat R N) :
    frobSq (matScale c A) = sq c * frobSq A := by
  unfold frobSq matScale
  calc finSum N (fun i => normSq (fun j => c * A i j))
      = finSum N (fun i => sq c * normSq (A i)) := finSum_congr (fun i => normSq_scale c (A i))
    _ = sq c * finSum N (fun i => normSq (A i)) := finSum_mul_left N (sq c) _

end TransportLemmas

-- Concrete Integer Matrices & Vectors for Fast Kernel Reduction (`decide`)
def twoQentInt : Mat Int 4 := fun i j =>
  match i.1, j.1 with
  | 0, 0 =>  1 | 0, 1 =>  1 | 0, 2 =>  1 | 0, 3 => -1
  | 1, 0 => -1 | 1, 1 =>  1 | 1, 2 =>  1 | 1, 3 =>  1
  | 2, 0 =>  1 | 2, 1 => -1 | 2, 2 =>  1 | 2, 3 =>  1
  | 3, 0 =>  1 | 3, 1 =>  1 | 3, 2 => -1 | 3, 3 =>  1
  | _, _ =>  0

def twoBetaVecInt (r : Fin 4) : Fin 4 → Int := fun i => twoQentInt i r

def reshape2x2 {T : Type u} (v : Fin 4 → T) : Fin 2 → Fin 2 → T := fun i j =>
  match i.1, j.1 with
  | 0, 0 => v ⟨0, by decide⟩
  | 0, 1 => v ⟨1, by decide⟩
  | 1, 0 => v ⟨2, by decide⟩
  | 1, 1 => v ⟨3, by decide⟩
  | _, _ => v ⟨0, by decide⟩

def twoPsi1Int : Fin 4 → Int := twoBetaVecInt ⟨0, by decide⟩

def tenPsi2Int : Fin 4 → Int
  | ⟨0, _⟩ =>  7
  | ⟨1, _⟩ =>  1
  | ⟨2, _⟩ => -1
  | ⟨3, _⟩ =>  7

def e00Int : Fin 4 → Int := fun i => if i.1 = 0 then 1 else 0
def e3Int  : Fin 4 → Int := fun i => if i.1 = 3 then 1 else 0
def e0_2Int : Fin 2 → Int := fun i => if i.1 = 0 then 1 else 0

def diag8421VecInt : Fin 4 → Int
  | ⟨0, _⟩ => 8 | ⟨1, _⟩ => 4 | ⟨2, _⟩ => 2 | ⟨3, _⟩ => 1

def diag1248VecInt : Fin 4 → Int
  | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 2 | ⟨2, _⟩ => 4 | ⟨3, _⟩ => 8

def diag8421Int : Mat Int 4 := matDiag diag8421VecInt
def diag1248Int : Mat Int 4 := matDiag diag1248VecInt

def fourXt1Int : Mat Int 4 :=
  matAdd (matScale 4 (matId 4)) (matScale 3 (outer twoPsi1Int twoPsi1Int))

def hundredXt2Int : Mat Int 4 :=
  matAdd (matScale 100 (matId 4)) (matScale 3 (outer tenPsi2Int tenPsi2Int))

theorem twoQentInt_tr_mul : matMul (matTr twoQentInt) twoQentInt = matScale 4 (matId 4) := by
  funext i j; revert j; revert i
  exact fin4_all
    (fin4_all (by decide) (by decide) (by decide) (by decide))
    (fin4_all (by decide) (by decide) (by decide) (by decide))
    (fin4_all (by decide) (by decide) (by decide) (by decide))
    (fin4_all (by decide) (by decide) (by decide) (by decide))

theorem twoQentInt_mul_tr : matMul twoQentInt (matTr twoQentInt) = matScale 4 (matId 4) := by
  funext i j; revert j; revert i
  exact fin4_all
    (fin4_all (by decide) (by decide) (by decide) (by decide))
    (fin4_all (by decide) (by decide) (by decide) (by decide))
    (fin4_all (by decide) (by decide) (by decide) (by decide))
    (fin4_all (by decide) (by decide) (by decide) (by decide))

theorem twoBetaInt_me (r : Fin 4) :
    normSq (twoBetaVecInt r) = 4 ∧
    frobSq (reshape2x2 (twoBetaVecInt r)) = 4 ∧
    matMul (reshape2x2 (twoBetaVecInt r)) (matTr (reshape2x2 (twoBetaVecInt r))) =
      matScale 2 (matId 2) ∧
    matMul (matTr (reshape2x2 (twoBetaVecInt r))) (reshape2x2 (twoBetaVecInt r)) =
      matScale 2 (matId 2) := by
  revert r
  refine fin4_all ?_ ?_ ?_ ?_
  all_goals
    refine ⟨by decide, by decide, ?_, ?_⟩
    · funext i j; revert j; revert i
      exact fin2_all (fin2_all (by decide) (by decide)) (fin2_all (by decide) (by decide))
    · funext i j; revert j; revert i
      exact fin2_all (fin2_all (by decide) (by decide)) (fin2_all (by decide) (by decide))

theorem tenPsi2Int_me :
    normSq tenPsi2Int = 100 ∧
    frobSq (reshape2x2 tenPsi2Int) = 100 ∧
    matMul (reshape2x2 tenPsi2Int) (matTr (reshape2x2 tenPsi2Int)) = matScale 50 (matId 2) ∧
    matMul (matTr (reshape2x2 tenPsi2Int)) (reshape2x2 tenPsi2Int) = matScale 50 (matId 2) := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · funext i j; revert j; revert i
    exact fin2_all (fin2_all (by decide) (by decide)) (fin2_all (by decide) (by decide))
  · funext i j; revert j; revert i
    exact fin2_all (fin2_all (by decide) (by decide)) (fin2_all (by decide) (by decide))

theorem psi1_psi2_int_props :
    dot twoPsi1Int tenPsi2Int = 12 ∧
    matMul (outer twoPsi1Int twoPsi1Int) (outer tenPsi2Int tenPsi2Int) ⟨0, by decide⟩ ⟨1, by decide⟩ = 12 ∧
    matMul (outer tenPsi2Int tenPsi2Int) (outer twoPsi1Int twoPsi1Int) ⟨0, by decide⟩ ⟨1, by decide⟩ = -84 ∧
    matMul fourXt1Int hundredXt2Int ⟨0, by decide⟩ ⟨1, by decide⟩ = -108 ∧
    matMul hundredXt2Int fourXt1Int ⟨0, by decide⟩ ⟨1, by decide⟩ = -972 ∧
    frobSq (matMul fourXt1Int hundredXt2Int) = 18400000 := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem diag8421_mul_diag1248 :
    matMul diag8421Int diag1248Int = matScale 8 (matId 4) := by
  funext i j; revert j; revert i
  exact fin4_all
    (fin4_all (by decide) (by decide) (by decide) (by decide))
    (fin4_all (by decide) (by decide) (by decide) (by decide))
    (fin4_all (by decide) (by decide) (by decide) (by decide))
    (fin4_all (by decide) (by decide) (by decide) (by decide))

theorem unitInt_props :
    normSq e0_2Int = 1 ∧
    normSq e00Int = 1 ∧
    normSq e3Int = 1 ∧
    normSq (matVec diag8421Int e00Int) = 64 ∧
    normSq (matVec diag1248Int e3Int) = 64 := by
  exact ⟨by decide, by decide, by decide, by decide, by decide⟩

-- Transport to Arbitrary `LinearOrderedField F` (covering both `QField` and `R`)
section FieldCounterexamples
variable (F : Type u) [LinearOrderedField F]

def qEnt : Mat F 4 := matScale (finv (ofInt F 2)) (matOfInt F twoQentInt)
def betaVec (r : Fin 4) : Fin 4 → F := vecScale (finv (ofInt F 2)) (vecOfInt F (twoBetaVecInt r))
def psi1Vec : Fin 4 → F := vecScale (finv (ofInt F 2)) (vecOfInt F twoPsi1Int)
def psi2Vec : Fin 4 → F := vecScale (finv (ofInt F 10)) (vecOfInt F tenPsi2Int)
def prodE00 : Fin 4 → F := vecOfInt F e00Int
def unitE0_2 : Fin 2 → F := vecOfInt F e0_2Int

private theorem sq_finv_pos_int {n : Int} (hn : 0 < n) :
    sq (finv (ofInt F n)) * ofInt F (n * n) = 1 := by
  have hpos : (0 : F) < ofInt F n := by
    have h0 : ofInt F 0 = 0 := rfl
    rw [← h0]; exact ofInt_lt hn
  have hne : ofInt F n ≠ 0 := ne_of_gt hpos
  unfold sq
  rw [ofInt_mul]
  calc (finv (ofInt F n) * finv (ofInt F n)) * (ofInt F n * ofInt F n)
      = finv (ofInt F n) * ((finv (ofInt F n) * ofInt F n) * ofInt F n) := by
          rw [mul_assoc (finv (ofInt F n)) _ _, ← mul_assoc (finv (ofInt F n)) (ofInt F n) _]
    _ = 1 := by rw [finv_mul_cancel hne, one_mul, finv_mul_cancel hne]

/-- `qEnt F ∈ O_4(F)` is an exact orthogonal matrix over `F`. -/
theorem qEnt_isOrthogonal : IsOrthogonal (qEnt F) := by
  have hsq2 : (finv (ofInt F 2) * finv (ofInt F 2)) * ofInt F 4 = 1 :=
    sq_finv_pos_int F (n := 2) (by decide)
  constructor
  · change matMul (matScale (finv (ofInt F 2)) (matOfInt F (matTr twoQentInt)))
                  (matScale (finv (ofInt F 2)) (matOfInt F twoQentInt)) = matId 4
    rw [matMul_matScale, matMul_matOfInt, twoQentInt_tr_mul,
        matOfInt_scale_id, matScale_matScale, hsq2, matScale_one]
  · change matMul (matScale (finv (ofInt F 2)) (matOfInt F twoQentInt))
                  (matScale (finv (ofInt F 2)) (matOfInt F (matTr twoQentInt))) = matId 4
    rw [matMul_matScale, matMul_matOfInt, twoQentInt_mul_tr,
        matOfInt_scale_id, matScale_matScale, hsq2, matScale_one]

/-- Every basis vector `betaVec F r` (`r = 0,1,2,3`) is a unit vector whose reshaped `2 x 2`
    matrix is maximally entangled (`IsMaximallyEntangled 2`). -/
theorem betaVec_maximallyEntangled (r : Fin 4) :
    normSq (betaVec F r) = 1 ∧ IsMaximallyEntangled 2 (reshape2x2 (betaVec F r)) := by
  rcases twoBetaInt_me r with ⟨hns, hfr, hmA, hmB⟩
  have hsq2 : sq (finv (ofInt F 2)) * ofInt F 4 = 1 :=
    sq_finv_pos_int F (n := 2) (by decide)
  have hresh : reshape2x2 (betaVec F r) =
               matScale (finv (ofInt F 2)) (matOfInt F (reshape2x2 (twoBetaVecInt r))) := by
    funext i j; revert j; revert i
    exact fin2_all (fin2_all rfl rfl) (fin2_all rfl rfl)
  have h2_pos : (0 : F) < ofInt F 2 := ofInt_lt (a := 0) (b := 2) (by decide)
  have h2_eq_nat : ofInt F 2 = natCast F 2 := rfl
  have hhalf : (finv (ofInt F 2) * finv (ofInt F 2)) * ofInt F 2 = finv (natCast F 2) := by
    rw [mul_assoc, finv_mul_cancel (ne_of_gt h2_pos), mul_one, h2_eq_nat]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold betaVec vecScale
    rw [normSq_scale, normSq_vecOfInt, hns, hsq2]
  · rw [hresh, frobSq_matScale, frobSq_matOfInt, hfr, hsq2]
  · unfold rhoA
    rw [hresh]
    change matMul (matScale (finv (ofInt F 2)) (matOfInt F (reshape2x2 (twoBetaVecInt r))))
                  (matScale (finv (ofInt F 2)) (matOfInt F (matTr (reshape2x2 (twoBetaVecInt r))))) =
           matScale (finv (natCast F 2)) (matId 2)
    rw [matMul_matScale, matMul_matOfInt, hmA, matOfInt_scale_id,
        matScale_matScale, hhalf]
  · unfold rhoB
    rw [hresh]
    change matMul (matScale (finv (ofInt F 2)) (matOfInt F (matTr (reshape2x2 (twoBetaVecInt r)))))
                  (matScale (finv (ofInt F 2)) (matOfInt F (reshape2x2 (twoBetaVecInt r)))) =
           matScale (finv (natCast F 2)) (matId 2)
    rw [matMul_matScale, matMul_matOfInt, hmB, matOfInt_scale_id,
        matScale_matScale, hhalf]

/-- `psi2Vec F = (1/10)(7, 1, -1, 7)` is also a unit maximally entangled state in `F^2 ⊗ F^2`. -/
theorem psi2Vec_maximallyEntangled :
    normSq (psi2Vec F) = 1 ∧ IsMaximallyEntangled 2 (reshape2x2 (psi2Vec F)) := by
  rcases tenPsi2Int_me with ⟨hns, hfr, hmA, hmB⟩
  have hsq10 : sq (finv (ofInt F 10)) * ofInt F 100 = 1 :=
    sq_finv_pos_int F (n := 10) (by decide)
  have hresh : reshape2x2 (psi2Vec F) =
               matScale (finv (ofInt F 10)) (matOfInt F (reshape2x2 tenPsi2Int)) := by
    funext i j; revert j; revert i
    exact fin2_all (fin2_all rfl rfl) (fin2_all rfl rfl)
  have h2_pos : (0 : F) < natCast F 2 := natCast_pos (by decide)
  have hhalf : (finv (ofInt F 10) * finv (ofInt F 10)) * ofInt F 50 = finv (natCast F 2) := by
    apply mul_right_cancel (ne_of_gt h2_pos)
    have h50_2 : ofInt F 50 * natCast F 2 = ofInt F 100 := by
      have he : ofInt F (50 * 2) = ofInt F 50 * ofInt F 2 := ofInt_mul 50 2
      exact he.symm
    rw [mul_assoc _ (ofInt F 50) (natCast F 2), h50_2]
    calc (finv (ofInt F 10) * finv (ofInt F 10)) * ofInt F 100
        = 1 := hsq10
      _ = finv (natCast F 2) * natCast F 2 := (finv_mul_cancel (ne_of_gt h2_pos)).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold psi2Vec vecScale
    rw [normSq_scale, normSq_vecOfInt, hns, hsq10]
  · rw [hresh, frobSq_matScale, frobSq_matOfInt, hfr, hsq10]
  · unfold rhoA
    rw [hresh]
    change matMul (matScale (finv (ofInt F 10)) (matOfInt F (reshape2x2 tenPsi2Int)))
                  (matScale (finv (ofInt F 10)) (matOfInt F (matTr (reshape2x2 tenPsi2Int)))) =
           matScale (finv (natCast F 2)) (matId 2)
    rw [matMul_matScale, matMul_matOfInt, hmA, matOfInt_scale_id,
        matScale_matScale, hhalf]
  · unfold rhoB
    rw [hresh]
    change matMul (matScale (finv (ofInt F 10)) (matOfInt F (matTr (reshape2x2 tenPsi2Int))))
                  (matScale (finv (ofInt F 10)) (matOfInt F (reshape2x2 tenPsi2Int))) =
           matScale (finv (natCast F 2)) (matId 2)
    rw [matMul_matScale, matMul_matOfInt, hmB, matOfInt_scale_id,
        matScale_matScale, hhalf]

/-- `prodE00 F = |00⟩` is an unentangled product state (hence NOT maximally entangled), yet its
    rank-1 projection `P_00` saturates `σ₁(P_00 P_00)² = 1 = σ₁(P_00)² σ₁(P_00)²`. -/
theorem productState_saturates_operator_bound :
    normSq (prodE00 F) = 1 ∧
    IsProductState (reshape2x2 (prodE00 F)) ∧
    ¬ IsMaximallyEntangled 2 (reshape2x2 (prodE00 F)) ∧
    HasTopSingValSq (outer (prodE00 F) (prodE00 F)) 1 ∧
    HasTopSingValSq (matMul (outer (prodE00 F) (prodE00 F)) (outer (prodE00 F) (prodE00 F))) 1 := by
  rcases unitInt_props with ⟨he0_int, he00_int, _, _, _⟩
  have he0_norm : normSq (unitE0_2 F) = 1 := by
    unfold unitE0_2; rw [normSq_vecOfInt, he0_int]; exact zero_add 1
  have he00_norm : normSq (prodE00 F) = 1 := by
    unfold prodE00; rw [normSq_vecOfInt, he00_int]; exact zero_add 1
  have hprod : IsProductState (reshape2x2 (prodE00 F)) := by
    refine ⟨unitE0_2 F, unitE0_2 F, he0_norm, he0_norm, ?_⟩
    funext i j; revert j; revert i
    refine fin2_all (fin2_all ?_ ?_) (fin2_all ?_ ?_)
    · change ofInt F 1 = ofInt F 1 * ofInt F 1; rw [← ofInt_mul]; rfl
    · change ofInt F 0 = ofInt F 1 * ofInt F 0; rw [← ofInt_mul]; rfl
    · change ofInt F 0 = ofInt F 0 * ofInt F 1; rw [← ofInt_mul]; rfl
    · change ofInt F 0 = ofInt F 0 * ofInt F 0; rw [← ofInt_mul]; rfl
  have hnot_me : ¬ IsMaximallyEntangled 2 (reshape2x2 (prodE00 F)) :=
    fun hme => maximallyEntangled_not_productState (by decide) hme hprod
  have htop1 := rankOneProj_hasTopSingValSq_one he00_norm
  have hprod_top := (rankOneProj_prod_singValSq he00_norm he00_norm).2.2.1
  have hsq1 : sq (dot (prodE00 F) (prodE00 F)) = 1 := by
    change sq (normSq (prodE00 F)) = 1
    rw [he00_norm]; unfold sq; exact one_mul 1
  rw [hsq1] at hprod_top
  exact ⟨he00_norm, hprod, hnot_me, htop1, hprod_top⟩

/-- Non-orthogonal, non-commuting rational maximally entangled projections `P₁, P₂` strictly
    fail to saturate the singular-value product bound (`σ₁(P₁ P₂)² = 9/25 < 1`). -/
theorem nonOrthogonal_maximallyEntangled_strict_nonsaturation :
    let P1 := outer (psi1Vec F) (psi1Vec F)
    let P2 := outer (psi2Vec F) (psi2Vec F)
    let nineOver25 := fdiv (ofInt F 9) (ofInt F 25)
    IsMaximallyEntangled 2 (reshape2x2 (psi1Vec F)) ∧
    IsMaximallyEntangled 2 (reshape2x2 (psi2Vec F)) ∧
    dot (psi1Vec F) (psi2Vec F) ≠ 0 ∧
    matMul P1 P2 ≠ matMul P2 P1 ∧
    HasTopSingValSq P1 1 ∧
    HasTopSingValSq P2 1 ∧
    HasTopSingValSq (matMul P1 P2) nineOver25 ∧
    nineOver25 < 1 := by
  dsimp
  have hpsi1_beta : psi1Vec F = betaVec F ⟨0, by decide⟩ := rfl
  rcases betaVec_maximallyEntangled F ⟨0, by decide⟩ with ⟨hn1_b, hme1_b⟩
  have hn1 : normSq (psi1Vec F) = 1 := by rw [hpsi1_beta]; exact hn1_b
  have hme1 : IsMaximallyEntangled 2 (reshape2x2 (psi1Vec F)) := by rw [hpsi1_beta]; exact hme1_b
  rcases psi2Vec_maximallyEntangled F with ⟨hn2, hme2⟩
  rcases psi1_psi2_int_props with ⟨hdot_int, hp12_int, hp21_int, _, _, _⟩
  have h2_pos : (0 : F) < ofInt F 2 := ofInt_lt (a := 0) (b := 2) (by decide)
  have h10_pos : (0 : F) < ofInt F 10 := ofInt_lt (a := 0) (b := 10) (by decide)
  have h25_pos : (0 : F) < ofInt F 25 := ofInt_lt (a := 0) (b := 25) (by decide)
  have hdot_eq : dot (psi1Vec F) (psi2Vec F) =
                 (finv (ofInt F 2) * finv (ofInt F 10)) * ofInt F 12 := by
    unfold psi1Vec psi2Vec
    rw [dot_vecScale, dot_vecOfInt, hdot_int]
  have hdot_ne : dot (psi1Vec F) (psi2Vec F) ≠ 0 := by
    rw [hdot_eq]
    have h12_pos : (0 : F) < ofInt F 12 := ofInt_lt (a := 0) (b := 12) (by decide)
    exact ne_of_gt (mul_pos (mul_pos (finv_pos h2_pos) (finv_pos h10_pos)) h12_pos)
  have hsq_dot : sq (dot (psi1Vec F) (psi2Vec F)) = fdiv (ofInt F 9) (ofInt F 25) := by
    apply mul_right_cancel (ne_of_gt (mul_pos (ofInt_lt (a := 0) (b := 400) (by decide)) h25_pos))
    have h400_eq : (ofInt F 2 * ofInt F 10) * (ofInt F 2 * ofInt F 10) = ofInt F 400 := by
      rw [← ofInt_mul, ← ofInt_mul]; rfl
    have hsq20 : sq (finv (ofInt F 2) * finv (ofInt F 10)) * ofInt F 400 = 1 := by
      rw [← h400_eq]; unfold sq
      let a := finv (ofInt F 2)
      let b := finv (ofInt F 10)
      let x := ofInt F 2
      let y := ofInt F 10
      have hax : a * x = 1 := finv_mul_cancel (ne_of_gt h2_pos)
      have hby : b * y = 1 := finv_mul_cancel (ne_of_gt h10_pos)
      have habxy : (a * b) * (x * y) = 1 := by
        calc (a * b) * (x * y)
            = a * ((b * y) * x) := by
                rw [mul_comm x y, mul_assoc a b (y * x), ← mul_assoc b y x]
          _ = 1 := by rw [hby, one_mul, hax]
      calc ((a * b) * (a * b)) * ((x * y) * (x * y))
          = (a * b) * (((a * b) * (x * y)) * (x * y)) := by
              rw [mul_assoc (a * b) (a * b) _, ← mul_assoc (a * b) (x * y) (x * y)]
        _ = 1 := by rw [habxy, one_mul, habxy]
    have hlhs400 : sq (dot (psi1Vec F) (psi2Vec F)) * ofInt F 400 = ofInt F 144 := by
      rw [hdot_eq]
      unfold sq
      let u := finv (ofInt F 2) * finv (ofInt F 10)
      have hpair : (u * ofInt F 12) * (u * ofInt F 12) = (u * u) * (ofInt F 12 * ofInt F 12) := by
        calc (u * ofInt F 12) * (u * ofInt F 12)
            = u * (ofInt F 12 * (u * ofInt F 12)) := mul_assoc u (ofInt F 12) _
          _ = u * (u * (ofInt F 12 * ofInt F 12)) := by
                rw [← mul_assoc (ofInt F 12) u _, mul_comm (ofInt F 12) u, mul_assoc u _ _]
          _ = (u * u) * (ofInt F 12 * ofInt F 12) := (mul_assoc _ _ _).symm
      have hexp : ((u * ofInt F 12) * (u * ofInt F 12)) * ofInt F 400 =
                  ((u * u) * ofInt F 400) * (ofInt F 12 * ofInt F 12) := by
        rw [hpair, mul_assoc (u * u), mul_comm (ofInt F 12 * ofInt F 12) (ofInt F 400), ← mul_assoc]
      rw [hexp]
      change (sq u * ofInt F 400) * (ofInt F 12 * ofInt F 12) = ofInt F 144
      rw [hsq20, one_mul, ← ofInt_mul]; rfl
    have hrhs400 : fdiv (ofInt F 9) (ofInt F 25) * (ofInt F 400 * ofInt F 25) =
                   ofInt F 144 * ofInt F 25 := by
      unfold fdiv
      calc (ofInt F 9 * finv (ofInt F 25)) * (ofInt F 400 * ofInt F 25)
          = (ofInt F 9 * ofInt F 400) * (finv (ofInt F 25) * ofInt F 25) := by
              rw [mul_assoc (ofInt F 9), ← mul_assoc (finv (ofInt F 25)) (ofInt F 400) _,
                  mul_comm (finv (ofInt F 25)) (ofInt F 400),
                  mul_assoc (ofInt F 400) _ _, ← mul_assoc]
        _ = ofInt F 9 * ofInt F 400 := by
              rw [finv_mul_cancel (ne_of_gt h25_pos), mul_one]
        _ = ofInt F 144 * ofInt F 25 := by rw [← ofInt_mul, ← ofInt_mul]; rfl
    calc sq (dot (psi1Vec F) (psi2Vec F)) * (ofInt F 400 * ofInt F 25)
        = (sq (dot (psi1Vec F) (psi2Vec F)) * ofInt F 400) * ofInt F 25 := (mul_assoc _ _ _).symm
      _ = ofInt F 144 * ofInt F 25 := by rw [hlhs400]
      _ = fdiv (ofInt F 9) (ofInt F 25) * (ofInt F 400 * ofInt F 25) := hrhs400.symm
  have hnoncomm : matMul (outer (psi1Vec F) (psi1Vec F)) (outer (psi2Vec F) (psi2Vec F)) ≠
                  matMul (outer (psi2Vec F) (psi2Vec F)) (outer (psi1Vec F) (psi1Vec F)) := by
    intro heq
    have h01 := congrFun (congrFun heq ⟨0, by decide⟩) ⟨1, by decide⟩
    let s1 := finv (ofInt F 2) * finv (ofInt F 2)
    let s2 := finv (ofInt F 10) * finv (ofInt F 10)
    have hp1 : outer (psi1Vec F) (psi1Vec F) = matScale s1 (matOfInt F (outer twoPsi1Int twoPsi1Int)) := by
      unfold psi1Vec; rw [outer_vecScale, outer_vecOfInt]
    have hp2 : outer (psi2Vec F) (psi2Vec F) = matScale s2 (matOfInt F (outer tenPsi2Int tenPsi2Int)) := by
      unfold psi2Vec; rw [outer_vecScale, outer_vecOfInt]
    rw [hp1, hp2, matMul_matScale, matMul_matScale, mul_comm s2 s1,
        matMul_matOfInt, matMul_matOfInt] at h01
    unfold matScale matOfInt at h01
    rw [hp12_int, hp21_int] at h01
    have hs_pos : 0 < s1 * s2 :=
      mul_pos (mul_pos (finv_pos h2_pos) (finv_pos h2_pos))
              (mul_pos (finv_pos h10_pos) (finv_pos h10_pos))
    have h12_eq_m84 : ofInt F 12 = ofInt F (-84) := by
      apply mul_right_cancel (ne_of_gt hs_pos)
      rw [mul_comm (ofInt F 12), mul_comm (ofInt F (-84))]
      exact h01
    exact ofInt_ne (by decide) h12_eq_m84
  have hlt1 : fdiv (ofInt F 9) (ofInt F 25) < 1 := by
    unfold fdiv
    have h9_lt_25 : ofInt F 9 < ofInt F 25 := ofInt_lt (by decide)
    have hmul : ofInt F 9 * finv (ofInt F 25) < ofInt F 25 * finv (ofInt F 25) := by
      have hdiff : 0 < (ofInt F 25 - ofInt F 9) * finv (ofInt F 25) := by
        apply mul_pos _ (finv_pos h25_pos)
        rcases lt_iff_le_not_le.mp h9_lt_25 with ⟨h1, h2⟩
        refine lt_iff_le_not_le.mpr ⟨sub_nonneg_of_le h1, fun hz => h2 ?_⟩
        have h3 := add_le_add_right hz (ofInt F 9)
        rw [sub_add_cancel, zero_add] at h3; exact h3
      rw [sub_mul] at hdiff
      rcases lt_iff_le_not_le.mp hdiff with ⟨hle, hnot⟩
      refine lt_iff_le_not_le.mpr ⟨le_of_sub_nonneg hle, fun hge => hnot ?_⟩
      have h2 := sub_nonneg_of_le hge
      have h3 := add_le_add_right h2 (ofInt F 25 * finv (ofInt F 25) - ofInt F 9 * finv (ofInt F 25))
      have hsum : (ofInt F 9 * finv (ofInt F 25) - ofInt F 25 * finv (ofInt F 25)) +
                  (ofInt F 25 * finv (ofInt F 25) - ofInt F 9 * finv (ofInt F 25)) = 0 := by
        let x := ofInt F 9 * finv (ofInt F 25)
        let y := ofInt F 25 * finv (ofInt F 25)
        calc (x - y) + (y - x)
            = x + (-y + (y + -x)) := by rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc]
          _ = x + (0 + -x) := by rw [← add_assoc (-y) y (-x), neg_add_cancel]
          _ = 0 := by rw [zero_add, add_neg_cancel]
      rw [zero_add, hsum] at h3; exact h3
    rw [mul_finv_cancel (ne_of_gt h25_pos)] at hmul
    exact hmul
  have htop_prod := (rankOneProj_prod_singValSq hn1 hn2).2.2.1
  rw [hsq_dot] at htop_prod
  exact ⟨hme1, hme2, hdot_ne, hnoncomm,
         rankOneProj_hasTopSingValSq_one hn1,
         rankOneProj_hasTopSingValSq_one hn2,
         htop_prod, hlt1⟩

/-- Full-rank invertible operators `X₁, X₂` diagonal in the maximally entangled basis `qEnt F`
    with singular values `(8, 4, 2, 1)` strictly fail `σ₁(X₁ X₂)² = σ₁(X₁)² σ₁(X₂)²` (`64 < 4096`). -/
def X1_me : Mat F 4 := conjBy (qEnt F) (matOfInt F diag8421Int)
def X2_me : Mat F 4 := conjBy (qEnt F) (matOfInt F diag1248Int)

theorem invertible_me_eigenbasis_strict_nonsaturation :
    HasTopSingValSq (X1_me F) (ofInt F 64) ∧
    HasTopSingValSq (X2_me F) (ofInt F 64) ∧
    matMul (X1_me F) (X2_me F) = matScale (ofInt F 8) (matId 4) ∧
    HasTopSingValSq (matMul (X1_me F) (X2_me F)) (ofInt F 64) ∧
    ofInt F 64 < ofInt F 64 * ofInt F 64 := by
  have hQ := qEnt_isOrthogonal F
  rcases unitInt_props with ⟨_, he00_int, he3_int, hd1_att, hd2_att⟩
  have hprod : matMul (X1_me F) (X2_me F) = matScale (ofInt F 8) (matId 4) := by
    unfold X1_me X2_me
    rw [← conjBy_mul hQ, matMul_matOfInt, diag8421_mul_diag1248, matOfInt_scale_id]
    unfold conjBy
    have hcomm : matMul (qEnt F) (matScale (ofInt F 8) (matId 4)) =
                 matScale (ofInt F 8) (qEnt F) := by
      have hid1 : matScale (1 : F) (qEnt F) = qEnt F := matScale_one _
      calc matMul (qEnt F) (matScale (ofInt F 8) (matId 4))
          = matMul (matScale 1 (qEnt F)) (matScale (ofInt F 8) (matId 4)) := by rw [hid1]
        _ = matScale (1 * ofInt F 8) (matMul (qEnt F) (matId 4)) := matMul_matScale _ _ _ _
        _ = matScale (ofInt F 8) (qEnt F) := by rw [one_mul, mul_matId]
    rw [hcomm]
    have hid2 : matScale (1 : F) (matTr (qEnt F)) = matTr (qEnt F) := matScale_one _
    calc matMul (matScale (ofInt F 8) (qEnt F)) (matTr (qEnt F))
        = matMul (matScale (ofInt F 8) (qEnt F)) (matScale 1 (matTr (qEnt F))) := by rw [hid2]
      _ = matScale (ofInt F 8 * 1) (matMul (qEnt F) (matTr (qEnt F))) := matMul_matScale _ _ _ _
      _ = matScale (ofInt F 8) (matId 4) := by rw [mul_one, hQ.2]
  have h64_nn : (0 : F) ≤ ofInt F 64 := le_of_lt (ofInt_lt (a := 0) (b := 64) (by decide))
  have hdiag1_eq : matOfInt F diag8421Int = matDiag (vecOfInt F diag8421VecInt) := by
    funext i j; unfold matOfInt diag8421Int matDiag vecOfInt
    by_cases h : i = j
    · subst h; simp
    · simp [h]; rfl
  have hdiag2_eq : matOfInt F diag1248Int = matDiag (vecOfInt F diag1248VecInt) := by
    funext i j; unfold matOfInt diag1248Int matDiag vecOfInt
    by_cases h : i = j
    · subst h; simp
    · simp [h]; rfl
  have htop_d1 : HasTopSingValSq (matOfInt F diag8421Int) (ofInt F 64) := by
    refine ⟨?_, ⟨prodE00 F, (productState_saturates_operator_bound F).1, ?_⟩⟩
    · rw [hdiag1_eq]
      refine matDiag_opNormSqBound _ (ofInt F 64) h64_nn ?_
      refine fin4_all ?_ ?_ ?_ ?_
      · unfold vecOfInt sq; rw [← ofInt_mul]; exact le_refl _
      · unfold vecOfInt sq; rw [← ofInt_mul]; exact le_of_lt (ofInt_lt (by decide))
      · unfold vecOfInt sq; rw [← ofInt_mul]; exact le_of_lt (ofInt_lt (by decide))
      · unfold vecOfInt sq; rw [← ofInt_mul]; exact le_of_lt (ofInt_lt (by decide))
    · unfold prodE00
      rw [matVec_matOfInt, normSq_vecOfInt, hd1_att]
  have htop_d2 : HasTopSingValSq (matOfInt F diag1248Int) (ofInt F 64) := by
    have he3_norm : normSq (vecOfInt F e3Int) = 1 := by
      rw [normSq_vecOfInt, he3_int]; exact zero_add 1
    refine ⟨?_, ⟨vecOfInt F e3Int, he3_norm, ?_⟩⟩
    · rw [hdiag2_eq]
      refine matDiag_opNormSqBound _ (ofInt F 64) h64_nn ?_
      refine fin4_all ?_ ?_ ?_ ?_
      · unfold vecOfInt sq; rw [← ofInt_mul]; exact le_of_lt (ofInt_lt (by decide))
      · unfold vecOfInt sq; rw [← ofInt_mul]; exact le_of_lt (ofInt_lt (by decide))
      · unfold vecOfInt sq; rw [← ofInt_mul]; exact le_of_lt (ofInt_lt (by decide))
      · unfold vecOfInt sq; rw [← ofInt_mul]; exact le_refl _
    · rw [matVec_matOfInt, normSq_vecOfInt, hd2_att]
  have htop_8I : HasTopSingValSq (matScale (ofInt F 8) (matId 4)) (ofInt F 64) := by
    have hvec8 : ∀ v : Fin 4 → F, matVec (matScale (ofInt F 8) (matId 4)) v =
                                  fun i => ofInt F 8 * v i := by
      intro v; funext i
      have hv_id := congrFun (matVec_matId v) i
      unfold matVec dot matScale at *
      rw [← hv_id]
      calc finSum 4 (fun j => (ofInt F 8 * matId 4 i j) * v j)
          = finSum 4 (fun j => ofInt F 8 * (matId 4 i j * v j)) :=
              finSum_congr (fun j => mul_assoc _ _ _)
        _ = ofInt F 8 * finSum 4 (fun j => matId 4 i j * v j) := finSum_mul_left 4 _ _
    have hsq8 : sq (ofInt F 8) = ofInt F 64 := by unfold sq; rw [← ofInt_mul]; rfl
    refine ⟨⟨h64_nn, fun v => ?_⟩, ⟨prodE00 F, (productState_saturates_operator_bound F).1, ?_⟩⟩
    · rw [hvec8, normSq_scale, hsq8]; exact le_refl _
    · rw [hvec8, normSq_scale, hsq8, (productState_saturates_operator_bound F).1, mul_one]
  refine ⟨(conjBy_hasTopSingValSq_iff hQ).mpr htop_d1,
          (conjBy_hasTopSingValSq_iff hQ).mpr htop_d2,
          hprod, ?_, ?_⟩
  · rw [hprod]; exact htop_8I
  · rw [← ofInt_mul]; exact ofInt_lt (by decide)

/-- Non-commuting invertible ME-principal-eigenvector operators `Xt1_me, Xt2_me` satisfy
    `σ₁(Xt1_me Xt2_me)² ≤ ‖Xt1_me Xt2_me‖_F² = 115 < 256 = σ₁(Xt1_me)² σ₁(Xt2_me)²`. -/
def Xt1_me : Mat F 4 := matScale (finv (ofInt F 4)) (matOfInt F fourXt1Int)
def Xt2_me : Mat F 4 := matScale (finv (ofInt F 100)) (matOfInt F hundredXt2Int)

theorem nonCommuting_invertible_me_strict_nonsaturation :
    matMul (Xt1_me F) (Xt2_me F) ≠ matMul (Xt2_me F) (Xt1_me F) ∧
    frobSq (matMul (Xt1_me F) (Xt2_me F)) = ofInt F 115 ∧
    OpNormSqBound (matMul (Xt1_me F) (Xt2_me F)) (ofInt F 115) ∧
    ofInt F 115 < ofInt F 16 * ofInt F 16 := by
  rcases psi1_psi2_int_props with ⟨_, _, _, hx12, hx21, hfrob_int⟩
  have h4_pos : (0 : F) < ofInt F 4 := ofInt_lt (a := 0) (b := 4) (by decide)
  have h100_pos : (0 : F) < ofInt F 100 := ofInt_lt (a := 0) (b := 100) (by decide)
  have hnoncomm : matMul (Xt1_me F) (Xt2_me F) ≠ matMul (Xt2_me F) (Xt1_me F) := by
    intro heq
    have h01 := congrFun (congrFun heq ⟨0, by decide⟩) ⟨1, by decide⟩
    unfold Xt1_me Xt2_me at h01
    rw [matMul_matScale, matMul_matScale, mul_comm (finv (ofInt F 100)) (finv (ofInt F 4)),
        matMul_matOfInt, matMul_matOfInt] at h01
    unfold matScale matOfInt at h01
    rw [hx12, hx21] at h01
    have hs_pos : 0 < finv (ofInt F 4) * finv (ofInt F 100) :=
      mul_pos (finv_pos h4_pos) (finv_pos h100_pos)
    have hm108_eq_m972 : ofInt F (-108) = ofInt F (-972) := by
      apply mul_right_cancel (ne_of_gt hs_pos)
      rw [mul_comm (ofInt F (-108)), mul_comm (ofInt F (-972))]
      exact h01
    exact ofInt_ne (by decide) hm108_eq_m972
  have hfrob : frobSq (matMul (Xt1_me F) (Xt2_me F)) = ofInt F 115 := by
    unfold Xt1_me Xt2_me
    rw [matMul_matScale, matMul_matOfInt, frobSq_matScale, frobSq_matOfInt, hfrob_int]
    have h400_eq : ofInt F 4 * ofInt F 100 = ofInt F 400 := by rw [← ofInt_mul]; rfl
    have hsq400 : sq (finv (ofInt F 4) * finv (ofInt F 100)) * ofInt F 160000 = 1 := by
      have h160k_split : (ofInt F 4 * ofInt F 100) * (ofInt F 4 * ofInt F 100) = ofInt F 160000 := by
        rw [h400_eq, ← ofInt_mul]; rfl
      rw [← h160k_split]; unfold sq
      let a := finv (ofInt F 4)
      let b := finv (ofInt F 100)
      let x := ofInt F 4
      let y := ofInt F 100
      have habxy : (a * b) * (x * y) = 1 := by
        calc (a * b) * (x * y)
            = a * ((b * y) * x) := by
                rw [mul_comm x y, mul_assoc a b (y * x), ← mul_assoc b y x]
          _ = 1 := by
                rw [finv_mul_cancel (ne_of_gt h100_pos), one_mul, finv_mul_cancel (ne_of_gt h4_pos)]
      calc ((a * b) * (a * b)) * ((x * y) * (x * y))
          = (a * b) * (((a * b) * (x * y)) * (x * y)) := by
              rw [mul_assoc (a * b) (a * b) _, ← mul_assoc (a * b) (x * y) (x * y)]
        _ = 1 := by rw [habxy, one_mul, habxy]
    have hsplit : ofInt F 18400000 = ofInt F 160000 * ofInt F 115 := by rw [← ofInt_mul]; rfl
    rw [hsplit, ← mul_assoc, hsq400, one_mul]
  have hbound : OpNormSqBound (matMul (Xt1_me F) (Xt2_me F)) (ofInt F 115) := by
    rw [← hfrob]; exact opNormSqBound_frobSq _
  refine ⟨hnoncomm, hfrob, hbound, ?_⟩
  rw [← ofInt_mul]; exact ofInt_lt (by decide)

/-- Model M2 (Akemann-Weaver POVM Subset-Sum Unitary Equivalence):
    For every subset indicator `S : Fin 4 → Bool`, the unentangled computational-basis POVM
    subset sum and the maximally entangled `betaVec` POVM subset sum are conjugate by `qEnt F`,
    hence possess identical exact top singular values squared. -/
def stdBasis4 (r : Fin 4) : Fin 4 → F := fun i => if i = r then 1 else 0

def matSubsetSum (ops : Fin 4 → Mat F 4) (S : Fin 4 → Bool) : Mat F 4 :=
  fun i j => finSum 4 (fun r => if S r then ops r i j else 0)

theorem qEnt_maps_stdBasis_to_betaVec (r : Fin 4) :
    matVec (qEnt F) (stdBasis4 F r) = betaVec F r := by
  funext i
  unfold matVec dot qEnt matScale matOfInt stdBasis4 betaVec vecScale vecOfInt twoBetaVecInt
  calc finSum 4 (fun k => (finv (ofInt F 2) * ofInt F (twoQentInt i k)) * (if k = r then 1 else 0))
      = finSum 4 (fun k => (if k = r then (1 : F) else 0) *
                             (finv (ofInt F 2) * ofInt F (twoQentInt i k))) :=
          finSum_congr (fun k => mul_comm _ _)
    _ = finv (ofInt F 2) * ofInt F (twoQentInt i r) :=
          finSum_ite_eq 4 r (fun k => finv (ofInt F 2) * ofInt F (twoQentInt i k))

theorem akemann_weaver_povm_orthogonal_equivalence (S : Fin 4 → Bool) (μ : F) :
    let prodPOVM : Fin 4 → Mat F 4 := fun r => outer (stdBasis4 F r) (stdBasis4 F r)
    let mePOVM   : Fin 4 → Mat F 4 := fun r => outer (betaVec F r) (betaVec F r)
    conjBy (qEnt F) (matSubsetSum F prodPOVM S) = matSubsetSum F mePOVM S ∧
    (HasTopSingValSq (matSubsetSum F mePOVM S) μ ↔
     HasTopSingValSq (matSubsetSum F prodPOVM S) μ) := by
  dsimp
  have hQ := qEnt_isOrthogonal F
  have hconj : conjBy (qEnt F) (matSubsetSum F (fun r => outer (stdBasis4 F r) (stdBasis4 F r)) S) =
               matSubsetSum F (fun r => outer (betaVec F r) (betaVec F r)) S := by
    have hlin : ∀ A : Fin 4 → Mat F 4,
        conjBy (qEnt F) (fun i j => finSum 4 (fun r => A r i j)) =
        fun i j => finSum 4 (fun r => conjBy (qEnt F) (A r) i j) := by
      intro A; funext i j; unfold conjBy matMul
      calc finSum 4 (fun k => finSum 4 (fun l => qEnt F i l * finSum 4 (fun r => A r l k)) *
                                matTr (qEnt F) k j)
          = finSum 4 (fun k => finSum 4 (fun r => finSum 4 (fun l => qEnt F i l * A r l k) *
                                matTr (qEnt F) k j)) := finSum_congr (fun k => by
              have e1 : finSum 4 (fun l => qEnt F i l * finSum 4 (fun r => A r l k)) =
                        finSum 4 (fun r => finSum 4 (fun l => qEnt F i l * A r l k)) := by
                calc finSum 4 (fun l => qEnt F i l * finSum 4 (fun r => A r l k))
                    = finSum 4 (fun l => finSum 4 (fun r => qEnt F i l * A r l k)) :=
                        finSum_congr (fun l => (finSum_mul_left 4 _ _).symm)
                  _ = finSum 4 (fun r => finSum 4 (fun l => qEnt F i l * A r l k)) :=
                        finSum_comm 4 4 _
              rw [e1, ← finSum_mul_right])
        _ = finSum 4 (fun r => finSum 4 (fun k => finSum 4 (fun l => qEnt F i l * A r l k) *
                                matTr (qEnt F) k j)) := finSum_comm 4 4 _
    unfold matSubsetSum
    have hstep := hlin (fun r i j =>
      if S r then outer (stdBasis4 F r) (stdBasis4 F r) i j else 0)
    rw [hstep]
    funext i j
    refine finSum_congr (fun r => ?_)
    cases hSr : S r with
    | false =>
      simp
      unfold conjBy matMul
      calc finSum 4 (fun k => finSum 4 (fun l => qEnt F i l * 0) * matTr (qEnt F) k j)
          = finSum 4 (fun _ => (0 : F)) := finSum_congr (fun k => by
              have hz : finSum 4 (fun l => qEnt F i l * (0 : F)) = 0 := by
                calc finSum 4 (fun l => qEnt F i l * (0 : F))
                    = finSum 4 (fun _ => (0 : F)) := finSum_congr (fun l => mul_zero _)
                  _ = 0 := by rw [finSum_const, mul_zero]
              rw [hz, zero_mul])
        _ = 0 := by rw [finSum_const, mul_zero]
    | true =>
      simp
      have ho := conjBy_outer (qEnt F) (stdBasis4 F r) (stdBasis4 F r)
      rw [qEnt_maps_stdBasis_to_betaVec F r] at ho
      exact congrFun (congrFun ho i) j
  refine ⟨hconj, ?_⟩
  rw [← hconj]
  exact conjBy_hasTopSingValSq_iff hQ

end FieldCounterexamples

end IntTransportAndCounterexamples

-- ============================================================================
-- §6. Master Resolution Theorem Instantiated over `QField` (and General `F`)
-- ============================================================================

theorem conjecture_00000007172_resolution :
    -- (A) Positive Full-Schmidt Product Characterization (all d ≥ 1 over QField)
    (∀ (d : Nat), 1 ≤ d → ∀ (w : Fin d → QField),
      (∀ i, 0 ≤ w i) → finSum d w = 1 →
      finProd d w ≤ rpow (finv (natCast QField d)) d ∧
      (finProd d w = rpow (finv (natCast QField d)) d ↔
        ∀ i : Fin d, w i = finv (natCast QField d))) ∧
    -- (B) Refutation of Proper Schmidt Partial-Product Saturation (all d ≥ 2, 1 ≤ k < d)
    (∀ (d k : Nat) (_ : 1 ≤ k) (hkd : k < d),
      finProd k (fun j => schmidtMaxEntSpectrum QField d ⟨j.1, Nat.lt_trans j.2 hkd⟩) <
        rpow (finv (natCast QField k)) k ∧
      finProd k (fun j => schmidtRankKSpectrum QField d k ⟨j.1, Nat.lt_trans j.2 hkd⟩) =
        rpow (finv (natCast QField k)) k ∧
      ¬ (∀ i : Fin d, schmidtRankKSpectrum QField d k i = finv (natCast QField d))) ∧
    -- (C) Unentangled Product State Saturates Operator Bound on QField^4
    (IsProductState (reshape2x2 (prodE00 QField)) ∧
     ¬ IsMaximallyEntangled 2 (reshape2x2 (prodE00 QField)) ∧
     HasTopSingValSq (matMul (outer (prodE00 QField) (prodE00 QField))
                             (outer (prodE00 QField) (prodE00 QField))) 1) ∧
    -- (D) Non-Orthogonal Non-Commuting Maximally Entangled Pair Strictly Fails (9/25 < 1)
    (IsMaximallyEntangled 2 (reshape2x2 (psi1Vec QField)) ∧
     IsMaximallyEntangled 2 (reshape2x2 (psi2Vec QField)) ∧
     matMul (outer (psi1Vec QField) (psi1Vec QField)) (outer (psi2Vec QField) (psi2Vec QField)) ≠
       matMul (outer (psi2Vec QField) (psi2Vec QField)) (outer (psi1Vec QField) (psi1Vec QField)) ∧
     HasTopSingValSq (matMul (outer (psi1Vec QField) (psi1Vec QField))
                             (outer (psi2Vec QField) (psi2Vec QField)))
                     (fdiv (ofInt QField 9) (ofInt QField 25)) ∧
     fdiv (ofInt QField 9) (ofInt QField 25) < 1) ∧
    -- (E) Invertible Commuting & Non-Commuting ME Operators Strictly Fail (64 < 4096 and 115 < 256)
    (HasTopSingValSq (X1_me QField) (ofInt QField 64) ∧
     HasTopSingValSq (X2_me QField) (ofInt QField 64) ∧
     HasTopSingValSq (matMul (X1_me QField) (X2_me QField)) (ofInt QField 64) ∧
     ofInt QField 64 < ofInt QField 64 * ofInt QField 64 ∧
     OpNormSqBound (matMul (Xt1_me QField) (Xt2_me QField)) (ofInt QField 115) ∧
     ofInt QField 115 < ofInt QField 16 * ofInt QField 16) ∧
    -- (F) Akemann-Weaver POVM Orthogonal Equivalence Between Unentangled and ME Bases
    (∀ (S : Fin 4 → Bool) (μ : QField),
      HasTopSingValSq (matSubsetSum QField (fun r => outer (betaVec QField r) (betaVec QField r)) S) μ ↔
      HasTopSingValSq (matSubsetSum QField (fun r => outer (stdBasis4 QField r) (stdBasis4 QField r)) S) μ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd w hnn hsum
    exact schmidt_full_product_max_iff_maximally_entangled hd w hnn hsum
  · intro d k hk1 hkd
    rcases schmidt_proper_partial_product_refutation (F := QField) hk1 hkd with ⟨_, hrk, hme_lt, _⟩
    exact ⟨hme_lt, hrk.2.2.1, hrk.2.2.2⟩
  · rcases productState_saturates_operator_bound QField with ⟨_, hp, hnme, _, htop⟩
    exact ⟨hp, hnme, htop⟩
  · rcases nonOrthogonal_maximallyEntangled_strict_nonsaturation QField with
      ⟨hme1, hme2, _, hnc, _, _, htop, hlt⟩
    exact ⟨hme1, hme2, hnc, htop, hlt⟩
  · rcases invertible_me_eigenbasis_strict_nonsaturation QField with ⟨hx1, hx2, _, hx12, hlt64⟩
    rcases nonCommuting_invertible_me_strict_nonsaturation QField with ⟨_, _, hxt12, hlt115⟩
    exact ⟨hx1, hx2, hx12, hlt64, hxt12, hlt115⟩
  · intro S μ
    exact (akemann_weaver_povm_orthogonal_equivalence QField S μ).2

end Conjecture00000007172

-- ============================================================================
-- Axiom Verification (Standard Lean 4 Core Foundations Only)
-- ============================================================================

#print axioms Conjecture00000007172.opNormSqBound_matMul
#print axioms Conjecture00000007172.rankOneProj_prod_singValSq
#print axioms Conjecture00000007172.rankOneProj_prod_saturated_iff_eq
#print axioms Conjecture00000007172.schmidt_full_product_max_iff_maximally_entangled
#print axioms Conjecture00000007172.schmidt_proper_partial_product_refutation
#print axioms Conjecture00000007172.nonOrthogonal_maximallyEntangled_strict_nonsaturation
#print axioms Conjecture00000007172.akemann_weaver_povm_orthogonal_equivalence
#print axioms Conjecture00000007172.conjecture_00000007172_resolution
