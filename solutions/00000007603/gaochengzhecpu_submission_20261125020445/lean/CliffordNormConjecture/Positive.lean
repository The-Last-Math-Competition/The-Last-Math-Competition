/-
Copyright (c) 2026. All rights reserved.
Positive non-vacuity theorems for Conjecture 00000007603:
1. Clifford contraction `v² = Q(v) · 1` for all signatures.
2. Coincidence of scalar reversal/conjugation norms with the L²-blade norm on
   positive-definite `Cl_{n,0}` and `Cl_{0,n}` for all `n ∈ ℕ`.
3. Universal multiplicative norm law on grade-1 vector pairs and versors in `Cl_{n,0}`
   for all `n ∈ ℕ`.
4. Exact Hurwitz composition-algebra multiplicativity on `Cl_{0,0}`, `Cl_{0,1}`, `Cl_{0,2}`
   for all multivectors.
5. Sharp conversion-constant doubling bound (`C = 2` on `Cl_{1,0}`, `Cl_{1,1}`, `Cl_{0,3}`, `Cl_{1,2}`).
-/
import CliffordNormConjecture.Algebra

namespace CliffordNormConjecture
namespace Cl

section VectorAndVersorLaws

variable {R : Type} [CommRing R]

/-- Grade-1 vectors are negated by grade involution: `v̂ = -v`. -/
theorem involute_ofVec {sig : List R} (v : Vec R sig) :
    involute (ofVec v) = neg (ofVec v) := by
  induction sig with
  | nil => exact neg_zero_eq.symm
  | cons _ _ ih =>
    rcases v with ⟨vs, r⟩
    simp only [ofVec, involute, ih, involute_smul, involute_one, neg]

/-- Grade-1 vectors are fixed by reversal: `ṽ = v`. -/
theorem rev_ofVec {sig : List R} (v : Vec R sig) :
    rev (ofVec v) = ofVec v := by
  induction sig with
  | nil => rfl
  | cons _ _ ih =>
    rcases v with ⟨vs, r⟩
    simp only [ofVec, rev, ih, rev_smul, rev_one, involute_smul, involute_one]

/-- Grade-1 vectors are negated by Clifford conjugation: `v̄ = -v`. -/
theorem conj_ofVec {sig : List R} (v : Vec R sig) :
    conj (ofVec v) = neg (ofVec v) := by
  rw [conj_eq_rev_involute, involute_ofVec, rev_neg, rev_ofVec]

/-- Every embedded coordinate vector satisfies the `isGradeOne` predicate. -/
theorem ofVec_isGradeOne {sig : List R} (v : Vec R sig) :
    isGradeOne (ofVec v) := by
  induction sig with
  | nil => rfl
  | cons _ _ ih =>
    rcases v with ⟨vs, r⟩
    exact ⟨ih vs, r, rfl⟩

/-- Fundamental Clifford Contraction Law: `v * v = Q_sig(v) · 1` for all `sig` and `v ∈ V`. -/
theorem ofVec_sq_eq_quadForm {sig : List R} (v : Vec R sig) :
    mul (ofVec v) (ofVec v) = smul (quadForm v) one := by
  induction sig with
  | nil =>
    change (0 : R) * 0 = 0 * 1
    rw [zero_mul, zero_mul]
  | cons c _ ih =>
    rcases v with ⟨vs, r⟩
    refine Prod.ext ?_ ?_
    · simp only [ofVec, mul, quadForm, one, smul, ih, involute_smul, involute_one,
        smul_mul_cl, mul_smul_cl, one_mul_cl]
      rw [← smul_smul_cl, ← smul_smul_cl, CommRing.mul_assoc c r r, ← add_smul_cl]
    · simp only [ofVec, mul, quadForm, one, smul, involute_ofVec, mul_smul_cl, smul_mul_cl,
        mul_one_cl, one_mul_cl, mul_neg_cl, smul_neg_cl, add_neg_cancel_cl, smul_zero_cl]

/-- The L²-blade norm of an embedded vector equals its coordinate sum of squares. -/
theorem l2NormSq_ofVec {sig : List R} (v : Vec R sig) :
    l2NormSq (ofVec v) = vecL2Sq v := by
  induction sig with
  | nil => exact zero_mul (0 : R)
  | cons _ _ ih =>
    rcases v with ⟨vs, r⟩
    simp only [ofVec, l2NormSq, vecL2Sq, ih, l2NormSq_smul, l2NormSq_one, CommRing.mul_one]

/-- On Euclidean `Cl_{n,0}`, `Q(v)` coincides with the sum of squared coordinates `vecL2Sq v`. -/
theorem euc_quadForm_eq_vecL2Sq (n : Nat) (v : Vec R (eucSig R n)) :
    quadForm v = vecL2Sq v := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rcases v with ⟨vs, r⟩
    simp only [eucSig, repSig, quadForm, vecL2Sq, CommRing.one_mul]
    exact congrArg (fun t => t + r * r) (ih vs)

/-- Positive-definite Euclidean norm coincidence:
    On `Cl_{n,0}`, the scalar reversal form `⟨X̃ X⟩₀` equals `‖X‖₂²` for all `n ∈ ℕ` and all `X`. -/
theorem euc_revNorm_eq_l2NormSq (n : Nat) (x : Cl R (eucSig R n)) :
    revNorm x = l2NormSq x := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rcases x with ⟨x0, x1⟩
    have hstep : revNorm (sig := (1 : R) :: eucSig R m) (x0, x1) = revNorm x0 + revNorm x1 := by
      simp only [revNorm, rev, mul, one_smul_cl, ← involute_mul, scalarPart,
        scalarPart_add, scalarPart_involute]
    rw [hstep, ih x0, ih x1]
    rfl

/-- Positive-definite Spin-geometry norm coincidence:
    On `Cl_{0,n}`, the scalar conjugation form `⟨X̄ X⟩₀` equals `‖X‖₂²` for all `n ∈ ℕ` and all `X`. -/
theorem spin_conjNorm_eq_l2NormSq (n : Nat) (x : Cl R (spinSig R n)) :
    conjNorm x = l2NormSq x := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rcases x with ⟨x0, x1⟩
    have hstep : conjNorm (sig := -(1 : R) :: spinSig R m) (x0, x1) =
        conjNorm x0 + conjNorm x1 := by
      simp only [conjNorm, conj, mul, neg_mul_cl, neg_smul_cl, one_smul_cl,
        neg_involutive_cl, ← involute_mul, scalarPart, scalarPart_add, scalarPart_involute]
    rw [hstep, ih x0, ih x1]
    rfl

/-- General left-multiplication norm scaling when `w̃ * w = s · 1` is scalar. -/
theorem rev_mul_self_scalar_left {sig : List R} {w : Cl R sig} {s : R}
    (hw : mul (rev w) w = smul s one) (y : Cl R sig) :
    mul (rev (mul w y)) (mul w y) = smul s (mul (rev y) y) := by
  rw [rev_mul, mul_assoc_cl, ← mul_assoc_cl (rev w) w y, hw,
      smul_mul_cl, one_mul_cl, mul_smul_cl]

theorem revNorm_mul_of_rev_mul_self_scalar {sig : List R} {w : Cl R sig} {s : R}
    (hw : mul (rev w) w = smul s one) (y : Cl R sig) :
    revNorm (mul w y) = s * revNorm y := by
  unfold revNorm
  rw [rev_mul_self_scalar_left hw y, scalarPart_smul]

/-- Universal Grade-1 Vector Pair Identity (all signatures):
    `(u v)̃ (u v) = (Q(u) Q(v)) · 1` and `N_rev(u v) = Q(u) Q(v)`. -/
theorem vec_pair_rev_prod {sig : List R} (u v : Vec R sig) :
    mul (rev (mul (ofVec u) (ofVec v))) (mul (ofVec u) (ofVec v)) =
      smul (quadForm u * quadForm v) one := by
  have hu : mul (rev (ofVec u)) (ofVec u) = smul (quadForm u) one := by
    rw [rev_ofVec, ofVec_sq_eq_quadForm]
  have hv : mul (rev (ofVec v)) (ofVec v) = smul (quadForm v) one := by
    rw [rev_ofVec, ofVec_sq_eq_quadForm]
  rw [rev_mul_self_scalar_left hu (ofVec v), hv, ← smul_smul_cl]

theorem vec_pair_revNorm {sig : List R} (u v : Vec R sig) :
    revNorm (mul (ofVec u) (ofVec v)) = quadForm u * quadForm v := by
  unfold revNorm
  rw [vec_pair_rev_prod, scalarPart_smul, scalarPart_one, CommRing.mul_one]

/-- Product of quadratic forms along a list of vectors (versor norm product). -/
def versorQuad {sig : List R} : List (Vec R sig) → R
  | [] => 1
  | v :: vs => quadForm v * versorQuad vs

/-- Every versor `W = v₁ ⋯ v_k` satisfies `W̃ W = (∏ Q(v_i)) · 1`. -/
theorem versor_rev_mul_self {sig : List R} (vs : List (Vec R sig)) :
    mul (rev (versor vs)) (versor vs) = smul (versorQuad vs) one := by
  induction vs with
  | nil =>
    simp only [versor, versorQuad, rev_one, one_mul_cl, one_smul_cl]
  | cons v rest ih =>
    simp only [versor, versorQuad]
    have hv : mul (rev (ofVec v)) (ofVec v) = smul (quadForm v) one := by
      rw [rev_ofVec, ofVec_sq_eq_quadForm]
    rw [rev_mul_self_scalar_left hv (versor rest), ih, ← smul_smul_cl]

theorem versor_revNorm {sig : List R} (vs : List (Vec R sig)) :
    revNorm (versor vs) = versorQuad vs := by
  unfold revNorm
  rw [versor_rev_mul_self, scalarPart_smul, scalarPart_one, CommRing.mul_one]

/-- Universal versor left-multiplicativity under `N_rev`:
    `N_rev(W Y) = N_rev(W) * N_rev(Y)` for every versor `W` and multivector `Y`. -/
theorem versor_revNorm_mul {sig : List R} (vs : List (Vec R sig)) (y : Cl R sig) :
    revNorm (mul (versor vs) y) = revNorm (versor vs) * revNorm y := by
  rw [revNorm_mul_of_rev_mul_self_scalar (versor_rev_mul_self vs) y, versor_revNorm]

/-- Positive Theorem 1 (Euclidean Grade-1 Vector Pairs, all `n ∈ ℕ`):
    `‖u v‖₂² = Q(u) Q(v) = ‖u‖₂² ‖v‖₂²` for all vectors `u, v ∈ V` in `Cl_{n,0}`. -/
theorem euc_vec_pair_l2NormSq (n : Nat) (u v : Vec R (eucSig R n)) :
    l2NormSq (mul (ofVec u) (ofVec v)) = quadForm u * quadForm v ∧
    l2NormSq (mul (ofVec u) (ofVec v)) = l2NormSq (ofVec u) * l2NormSq (ofVec v) := by
  rw [← euc_revNorm_eq_l2NormSq, vec_pair_revNorm]
  refine ⟨rfl, ?_⟩
  rw [euc_quadForm_eq_vecL2Sq, euc_quadForm_eq_vecL2Sq, l2NormSq_ofVec, l2NormSq_ofVec]

/-- Positive Theorem 2 (Euclidean Versors, all `n ∈ ℕ`):
    `‖W Y‖₂² = ‖W‖₂² ‖Y‖₂²` for every versor `W` and arbitrary multivector `Y ∈ Cl_{n,0}`. -/
theorem euc_versor_l2NormSq_mul (n : Nat) (vs : List (Vec R (eucSig R n)))
    (y : Cl R (eucSig R n)) :
    l2NormSq (mul (versor vs) y) = l2NormSq (versor vs) * l2NormSq y := by
  rw [← euc_revNorm_eq_l2NormSq, ← euc_revNorm_eq_l2NormSq, ← euc_revNorm_eq_l2NormSq]
  exact versor_revNorm_mul vs y

end VectorAndVersorLaws

section HurwitzLowDim

variable {R : Type} [CommRing R]

theorem conjNorm_mul_of_conj_mul_self_scalar {sig : List R} {w : Cl R sig} {s : R}
    (hw : mul (conj w) w = smul s one) (y : Cl R sig) :
    conjNorm (mul w y) = s * conjNorm y := by
  unfold conjNorm
  rw [conj_mul, mul_assoc_cl, ← mul_assoc_cl (conj w) w y, hw,
      smul_mul_cl, one_mul_cl, mul_smul_cl, scalarPart_smul]

/-- In dimension 1 (`Cl R [c]`), multiplication is commutative. -/
theorem cl1_mul_comm {c : R} (a b : Cl R [c]) : mul a b = mul b a := by
  rcases a with ⟨a0, a1⟩; rcases b with ⟨b0, b1⟩
  refine Prod.ext ?_ ?_
  · change a0 * b0 + c * (a1 * b1) = b0 * a0 + c * (b1 * a1)
    rw [CommRing.mul_comm a0 b0, CommRing.mul_comm a1 b1]
  · change a0 * b1 + a1 * b0 = b0 * a1 + b1 * a0
    rw [CommRing.mul_comm a0 b1, CommRing.mul_comm a1 b0, CommRing.add_comm]

/-- In dimension 1 (`Cl R [c]`), Clifford conjugation coincides with grade involution. -/
theorem cl1_conj_eq_involute {c : R} (a : Cl R [c]) : conj a = involute a := by
  rcases a with ⟨a0, a1⟩
  rfl

/-- In dimension 1 (`Cl R [c]`), `X̄ X = N_conj(X) · 1` is purely scalar for all `X`. -/
theorem cl1_conj_mul_self {c : R} (x : Cl R [c]) :
    mul (conj x) x = smul (conjNorm x) one := by
  rcases x with ⟨x0, x1⟩
  refine Prod.ext ?_ ?_
  · change x0 * x0 + c * ((-x1) * x1) = (x0 * x0 + c * ((-x1) * x1)) * 1
    rw [CommRing.mul_one]
  · change x0 * x1 + (-x1) * x0 = (x0 * x0 + c * ((-x1) * x1)) * 0
    rw [mul_zero, CommRing.mul_comm (-x1) x0, mul_neg, add_neg_cancel]

theorem cl1_conjNorm_mul {c : R} (x y : Cl R [c]) :
    conjNorm (mul x y) = conjNorm x * conjNorm y :=
  conjNorm_mul_of_conj_mul_self_scalar (cl1_conj_mul_self x) y

/-- In dimension 2 (`Cl R [c₁, c₂]`), `X̄ X = N_conj(X) · 1` is purely scalar for all `X`. -/
theorem cl2_conj_mul_self {c1 c2 : R} (x : Cl R [c1, c2]) :
    mul (conj x) x = smul (conjNorm x) one := by
  rcases x with ⟨x0, x1⟩
  have hx0 : mul (conj x0) x0 = smul (conjNorm x0) one := cl1_conj_mul_self x0
  have hx1 : mul (conj x1) x1 = smul (conjNorm x1) one := cl1_conj_mul_self x1
  have h1 : involute (conj x1) = x1 := by
    rw [cl1_conj_eq_involute, involute_involutive]
  have h2 : involute x1 = conj x1 := (cl1_conj_eq_involute x1).symm
  have hfst : add (mul (conj x0) x0) (smul c1 (mul (neg (involute (conj x1))) (involute x1))) =
      smul (conjNorm x0 + (-c1) * conjNorm x1) one := by
    rw [h1, h2, neg_mul_cl, cl1_mul_comm x1 (conj x1), hx1,
        smul_neg_cl, ← neg_smul_cl, ← smul_smul_cl, hx0, ← add_smul_cl]
  have hnorm : conjNorm (sig := [c1, c2]) (x0, x1) = conjNorm x0 + (-c1) * conjNorm x1 := by
    change scalarPart (add (mul (conj x0) x0)
      (smul c1 (mul (neg (involute (conj x1))) (involute x1)))) = _
    rw [hfst, scalarPart_smul, scalarPart_one, CommRing.mul_one]
  refine Prod.ext ?_ ?_
  · change add (mul (conj x0) x0) (smul c1 (mul (neg (involute (conj x1))) (involute x1))) =
      smul (conjNorm (sig := [c1, c2]) (x0, x1)) one
    rw [hfst, hnorm]
  · change add (mul (conj x0) x1) (mul (neg (involute (conj x1))) (involute x0)) =
      smul (conjNorm (sig := [c1, c2]) (x0, x1)) zero
    rw [smul_zero_cl, cl1_conj_eq_involute x1, involute_involutive,
        cl1_conj_eq_involute x0, neg_mul_cl, cl1_mul_comm x1 (involute x0), add_neg_cancel_cl]

theorem cl2_conjNorm_mul {c1 c2 : R} (x y : Cl R [c1, c2]) :
    conjNorm (mul x y) = conjNorm x * conjNorm y :=
  conjNorm_mul_of_conj_mul_self_scalar (cl2_conj_mul_self x) y

/-- Hurwitz Positive Theorem (`Cl_{0,0} ≅ ℝ`, `Cl_{0,1} ≅ ℂ`, `Cl_{0,2} ≅ ℍ`):
    Exact L²-norm multiplicativity `‖X Y‖₂² = ‖X‖₂² ‖Y‖₂²` holds for ALL multivectors
    in `Cl_{0,n}` for `n ∈ {0, 1, 2}`. -/
theorem hurwitz_cl00_l2NormSq_mul (x y : Cl R (spinSig R 0)) :
    l2NormSq (mul x y) = l2NormSq x * l2NormSq y := by
  change (x * y) * (x * y) = (x * x) * (y * y)
  rw [CommRing.mul_assoc x y (x * y), ← CommRing.mul_assoc y x y,
      CommRing.mul_comm y x, CommRing.mul_assoc x y y, ← CommRing.mul_assoc x x (y * y)]

theorem hurwitz_cl01_l2NormSq_mul (x y : Cl R (spinSig R 1)) :
    l2NormSq (mul x y) = l2NormSq x * l2NormSq y := by
  rw [← spin_conjNorm_eq_l2NormSq 1, ← spin_conjNorm_eq_l2NormSq 1, ← spin_conjNorm_eq_l2NormSq 1]
  exact cl1_conjNorm_mul x y

theorem hurwitz_cl02_l2NormSq_mul (x y : Cl R (spinSig R 2)) :
    l2NormSq (mul x y) = l2NormSq x * l2NormSq y := by
  rw [← spin_conjNorm_eq_l2NormSq 2, ← spin_conjNorm_eq_l2NormSq 2, ← spin_conjNorm_eq_l2NormSq 2]
  exact cl2_conjNorm_mul x y

end HurwitzLowDim

section SharpConversionBounds

variable {R : Type} [OrderedCommRing R]

theorem two_mul_le_two_mul {a b : R} (h : a ≤ b) : two R * a ≤ two R * b := by
  unfold two
  rw [CommRing.right_distrib, CommRing.right_distrib, CommRing.one_mul, CommRing.one_mul]
  exact add_le_add h h

/-- Nonnegativity of `l2NormSq` over any `OrderedCommRing`. -/
theorem l2NormSq_nonneg {sig : List R} (x : Cl R sig) : (0 : R) ≤ l2NormSq x := by
  induction sig with
  | nil => exact OrderedCommRing.sq_nonneg x
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    exact add_nonneg (ih x0) (ih x1)

/-- Multivector parallelogram inequality: `‖X + Y‖₂² ≤ 2 (‖X‖₂² + ‖Y‖₂²)`. -/
theorem l2NormSq_add_le_two_mul {sig : List R} (x y : Cl R sig) :
    l2NormSq (add x y) ≤ two R * (l2NormSq x + l2NormSq y) := by
  induction sig with
  | nil => exact sq_add_le_two_mul_add_sq x y
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    have h0 := ih x0 y0
    have h1 := ih x1 y1
    have hsum := add_le_add h0 h1
    rw [← CommRing.left_distrib] at hsum
    have harr : (l2NormSq x0 + l2NormSq y0) + (l2NormSq x1 + l2NormSq y1) =
        (l2NormSq x0 + l2NormSq x1) + (l2NormSq y0 + l2NormSq y1) :=
      add_add_add_comm _ _ _ _
    rw [harr] at hsum
    exact hsum

/-- Conversion-Constant Doubling Theorem:
    If `Cl R sig` satisfies `‖A B‖₂² ≤ K ‖A‖₂² ‖B‖₂²` and `c² = 1`, then adjoining `c`
    satisfies `‖X Y‖₂² ≤ (2 K) ‖X‖₂² ‖Y‖₂²`. -/
theorem l2NormSq_mul_cons_le {sig : List R} {c K : R} (hc : c * c = 1)
    (hbound : ∀ a b : Cl R sig, l2NormSq (mul a b) ≤ K * (l2NormSq a * l2NormSq b))
    (x y : Cl R (c :: sig)) :
    l2NormSq (mul x y) ≤ (two R * K) * (l2NormSq x * l2NormSq y) := by
  rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
  have p0 := l2NormSq_add_le_two_mul (mul x0 y0) (smul c (mul x1 (involute y1)))
  have p1 := l2NormSq_add_le_two_mul (mul x0 y1) (mul x1 (involute y0))
  rw [l2NormSq_smul, hc, CommRing.one_mul] at p0
  have b00 := hbound x0 y0
  have b11 := hbound x1 (involute y1)
  rw [l2NormSq_involute] at b11
  have b01 := hbound x0 y1
  have b10 := hbound x1 (involute y0)
  rw [l2NormSq_involute] at b10
  have s0 : l2NormSq (mul x0 y0) + l2NormSq (mul x1 (involute y1)) ≤
      K * (l2NormSq x0 * l2NormSq y0 + l2NormSq x1 * l2NormSq y1) := by
    rw [CommRing.left_distrib]
    exact add_le_add b00 b11
  have s1 : l2NormSq (mul x0 y1) + l2NormSq (mul x1 (involute y0)) ≤
      K * (l2NormSq x0 * l2NormSq y1 + l2NormSq x1 * l2NormSq y0) := by
    rw [CommRing.left_distrib]
    exact add_le_add b01 b10
  have q0 := OrderedCommRing.le_trans p0 (two_mul_le_two_mul s0)
  have q1 := OrderedCommRing.le_trans p1 (two_mul_le_two_mul s1)
  have qsum := add_le_add q0 q1
  have hrhs :
      two R * (K * (l2NormSq x0 * l2NormSq y0 + l2NormSq x1 * l2NormSq y1)) +
      two R * (K * (l2NormSq x0 * l2NormSq y1 + l2NormSq x1 * l2NormSq y0)) =
      (two R * K) * ((l2NormSq x0 + l2NormSq x1) * (l2NormSq y0 + l2NormSq y1)) := by
    rw [← CommRing.mul_assoc (two R) K, ← CommRing.mul_assoc (two R) K,
        ← CommRing.left_distrib (two R * K)]
    apply congrArg (fun t => (two R * K) * t)
    rw [CommRing.right_distrib (l2NormSq x0) (l2NormSq x1),
        CommRing.left_distrib (l2NormSq x0), CommRing.left_distrib (l2NormSq x1)]
    rw [CommRing.add_comm (l2NormSq x1 * l2NormSq y0) (l2NormSq x1 * l2NormSq y1)]
    exact (add_add_add_comm (R := R) _ _ _ _).symm
  rw [hrhs] at qsum
  exact qsum

/-- Sharp upper bound `‖X Y‖₂² ≤ 2 ‖X‖₂² ‖Y‖₂²` on `Cl_{1,0}`, `Cl_{1,1}`, `Cl_{0,3}`, and `Cl_{1,2}`. -/
theorem sharp_upper_cl10 (x y : Cl R (eucSig R 1)) :
    l2NormSq (mul x y) ≤ two R * (l2NormSq x * l2NormSq y) := by
  have h := l2NormSq_mul_cons_le (sig := ([] : List R)) (c := (1 : R)) (K := (1 : R))
    (CommRing.one_mul (1 : R))
    (fun a b => by
      rw [CommRing.one_mul, hurwitz_cl00_l2NormSq_mul]
      exact OrderedCommRing.le_refl _)
    x y
  rw [CommRing.mul_one] at h
  exact h

theorem sharp_upper_cl11 (x y : Cl R [(1 : R), -(1 : R)]) :
    l2NormSq (mul x y) ≤ two R * (l2NormSq x * l2NormSq y) := by
  have h := l2NormSq_mul_cons_le (sig := spinSig R 1) (c := (1 : R)) (K := (1 : R))
    (CommRing.one_mul (1 : R))
    (fun a b => by
      rw [CommRing.one_mul, hurwitz_cl01_l2NormSq_mul]
      exact OrderedCommRing.le_refl _)
    x y
  rw [CommRing.mul_one] at h
  exact h

theorem sharp_upper_cl03 (x y : Cl R (spinSig R 3)) :
    l2NormSq (mul x y) ≤ two R * (l2NormSq x * l2NormSq y) := by
  have hc : (-(1 : R)) * (-(1 : R)) = 1 := by
    rw [neg_mul_neg, CommRing.one_mul]
  have h := l2NormSq_mul_cons_le (sig := spinSig R 2) (c := -(1 : R)) (K := (1 : R))
    hc
    (fun a b => by
      rw [CommRing.one_mul, hurwitz_cl02_l2NormSq_mul]
      exact OrderedCommRing.le_refl _)
    x y
  rw [CommRing.mul_one] at h
  exact h

theorem sharp_upper_cl12 (x y : Cl R [(1 : R), -(1 : R), -(1 : R)]) :
    l2NormSq (mul x y) ≤ two R * (l2NormSq x * l2NormSq y) := by
  have h := l2NormSq_mul_cons_le (sig := spinSig R 2) (c := (1 : R)) (K := (1 : R))
    (CommRing.one_mul (1 : R))
    (fun a b => by
      rw [CommRing.one_mul, hurwitz_cl02_l2NormSq_mul]
      exact OrderedCommRing.le_refl _)
    x y
  rw [CommRing.mul_one] at h
  exact h

end SharpConversionBounds

end Cl
end CliffordNormConjecture
