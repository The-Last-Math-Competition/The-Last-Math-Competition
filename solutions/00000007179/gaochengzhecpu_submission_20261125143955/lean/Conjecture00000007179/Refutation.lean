/-
Copyright (c) 2026. All rights reserved.
Formalization of Conjecture 00000007179 in Core Lean 4.19.0 (zero external dependencies).

Module: Conjecture00000007179.Refutation
Purpose:
  1. Exhaustive formal refutation of Clause 2 ("and the coefficient of the perturbation is
     the residual projection") across every candidate mathematical interpretation:
       * Reading A: First-order eigenvalue coefficient `λ₁` via the residual projection
         `Q = I - P`, including `± tr(Q A₁)`, `w₀ᵀ Q A₁ v₀ / w₀ᵀ v₀`, `‖Q A₁ v₀‖₁`,
         squared Euclidean norm `‖Q A₁ v₀‖₂²`, and universal `n × n` trace-duality
         impossibility (`¬ ∀ A₁, λ₁(A₁) = tr(Q A₁)` for every simple eigenvalue in every
         dimension `n`).
       * Reading B: First-order eigenvector coefficient `v₁ = ± Q A₁ v₀`.
       * Reading C: Second-order eigenvalue coefficient `λ₂ = ± tr(P A₁ Q A₁)`.
       * Reading D: First-order eigenprojection coefficient `P₁ = ± Q` or
         `P₁ = ± (P A₁ Q + Q A₁ P)`.
  2. Sharpness of the simplicity hypothesis in Clause 1: formal impossibility of a formal
     power series eigenvalue or eigenpair for the defective `2 × 2` Jordan perturbation
     `A(ε) = [[0, 1], [ε, 0]]` around the double eigenvalue `λ₀ = 0`.
-/

import Conjecture00000007179.KatoPerturbation

namespace Conjecture00000007179

section UniversalTraceDualityRefutation

variable {F : Type u} [LinearOrderedField F]

/-- Elementary matrix unit `E_{r,c}` in `Mat n F` with `1` at `(r, c)` and `0` elsewhere. -/
def matUnit {n : Nat} (r c : Fin n) : Mat n F :=
  fun i j => if i = r ∧ j = c then 1 else 0

theorem matTrace_mul_matUnit {n : Nat} (M : Mat n F) (r c : Fin n) :
    matTrace (matMul M (matUnit c r)) = M r c := by
  unfold matTrace matMul matUnit
  rw [finSum_eq_single n r _ (fun i hir => by
    have hz : (fun k : Fin n => M i k * (if k = c ∧ i = r then (1 : F) else 0)) =
        (fun _ => 0) := by
      funext k
      have hcond : ¬ (k = c ∧ i = r) := fun h => hir h.2
      rw [if_neg hcond, mul_zero]
    rw [hz, finSum_zero_fn])]
  rw [finSum_eq_single n c _ (fun k hkc => by
    have hcond : ¬ (k = c ∧ r = r) := fun h => hkc h.1
    rw [if_neg hcond, mul_zero])]
  have htrue : c = c ∧ r = r := ⟨rfl, rfl⟩
  rw [if_pos htrue, lofMulOne]

/-- **Unique Trace-Duality Operator Representation of `A₁ ↦ λ₁(A₁)`:**
    If `M ∈ Mat n F` represents the first-order eigenvalue functional `λ₁(A₁) = tr(M A₁)`
    for every perturbation `A₁`, then necessarily `M = P`. -/
theorem firstOrder_operator_unique {n : Nat} {A0 : Mat n F} {lam0 : F}
    (D : SimpleEigenvalueKatoData n F A0 lam0) (M : Mat n F)
    (hrep : ∀ A1 : Mat n F, D.katoLambda A1 1 = matTrace (matMul M A1)) :
    M = D.P := by
  funext r c
  have h1 := hrep (matUnit c r)
  have h2 := (D.kato_first_order_eigenvalue (matUnit c r)).2.1
  have heq : matTrace (matMul M (matUnit c r)) = matTrace (matMul D.P (matUnit c r)) :=
    h1.symm.trans h2
  rw [matTrace_mul_matUnit, matTrace_mul_matUnit] at heq
  exact heq

/-- For every simple eigenvalue in every dimension `n`, the eigenprojection `P` and the
    residual projection `Q = I - P` are strictly distinct (`P ≠ Q`). -/
theorem eigenProj_ne_residualProj {n : Nat} {A0 : Mat n F} {lam0 : F}
    (D : SimpleEigenvalueKatoData n F A0 lam0) :
    D.P ≠ D.Q := by
  intro hPQ
  have hv : matVec D.P D.v0 = matVec D.Q D.v0 := congrArg (fun X => matVec X D.v0) hPQ
  rw [D.P_v0, D.Q_v0] at hv
  have hdot : vecDot D.w0 D.v0 = 0 := by
    rw [hv, vecDot_zero_right]
  exact D.pair_ne_zero hdot

/-- **Universal `n × n` Impossibility of Reading A (`λ₁(A₁) = tr(Q A₁)`):**
    For *every* simple eigenvalue Kato datum `(A₀, λ₀)` in *every* dimension `n`, the
    residual projection `Q = I - P` fails to represent the first-order eigenvalue shift
    `A₁ ↦ λ₁(A₁)`. -/
theorem universal_readingA_trace_impossible {n : Nat} {A0 : Mat n F} {lam0 : F}
    (D : SimpleEigenvalueKatoData n F A0 lam0) :
    ¬ (∀ A1 : Mat n F, D.katoLambda A1 1 = matTrace (matMul D.Q A1)) := by
  intro hall
  have hQP : D.Q = D.P := firstOrder_operator_unique D D.Q hall
  exact eigenProj_ne_residualProj D hQP.symm

/-- **Universal Vanishing of `w₀ᵀ Q A₁ v₀ / w₀ᵀ v₀`:**
    Replacing `P` by `Q` inside the Rayleigh-quotient numerator `w₀ᵀ (Q A₁ v₀) / w₀ᵀ v₀`
    yields identically `0` for every `A₁`. -/
theorem w0_Q_rayleigh_identically_zero {n : Nat} {A0 : Mat n F} {lam0 : F}
    (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F) :
    vecDot D.w0 (matVec D.Q (matVec A1 D.v0)) / vecDot D.w0 D.v0 = 0 := by
  rw [D.w0_dot_Q, zero_div]

end UniversalTraceDualityRefutation

section TwoByTwoExplicitCalculus

variable {F : Type u} [LinearOrderedField F]

/-- Explicit `2`-vectors and `2 × 2` matrices over `F`. -/
def vec2 (x y : F) : Vec 2 F :=
  fun i => if i.val = 0 then x else y

def mat2 (a b c d : F) : Mat 2 F :=
  fun i j =>
    if i.val = 0 then
      if j.val = 0 then a else b
    else
      if j.val = 0 then c else d

def fin2Zero : Fin 2 := ⟨0, by decide⟩
def fin2One : Fin 2 := ⟨1, by decide⟩

theorem finSum_two (f : Fin 2 → F) :
    finSum 2 f = f fin2Zero + f fin2One := by
  rw [finSum_succ 1, finSum_succ 0, finSum_zero, lofZeroAdd]
  rfl

omit [LinearOrderedField F] in
theorem vec2_ext {x1 y1 x2 y2 : F} (h : vec2 x1 y1 = vec2 x2 y2) :
    x1 = x2 ∧ y1 = y2 := by
  have h0 := congrFun h fin2Zero
  have h1 := congrFun h fin2One
  unfold vec2 fin2Zero at h0
  unfold vec2 fin2One at h1
  dsimp only at h0 h1
  rw [if_pos rfl, if_pos rfl] at h0
  rw [if_neg (by decide), if_neg (by decide)] at h1
  exact ⟨h0, h1⟩

omit [LinearOrderedField F] in
theorem mat2_entry_01 {a1 b1 c1 d1 a2 b2 c2 d2 : F}
    (h : mat2 a1 b1 c1 d1 = mat2 a2 b2 c2 d2) : b1 = b2 := by
  have h01 := congrFun (congrFun h fin2Zero) fin2One
  unfold mat2 fin2Zero fin2One at h01
  dsimp only at h01
  rw [if_pos rfl, if_pos rfl, if_neg (by decide), if_neg (by decide)] at h01
  exact h01

omit [LinearOrderedField F] in
theorem mat2_entry_11 {a1 b1 c1 d1 a2 b2 c2 d2 : F}
    (h : mat2 a1 b1 c1 d1 = mat2 a2 b2 c2 d2) : d1 = d2 := by
  have h11 := congrFun (congrFun h fin2One) fin2One
  unfold mat2 fin2One at h11
  dsimp only at h11
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)] at h11
  exact h11

theorem vecDot_vec2 (x1 y1 x2 y2 : F) :
    vecDot (vec2 x1 y1) (vec2 x2 y2) = x1 * x2 + y1 * y2 := by
  unfold vecDot
  rw [finSum_two]
  unfold vec2 fin2Zero fin2One
  dsimp only
  rw [if_pos rfl, if_pos rfl, if_neg (by decide), if_neg (by decide)]

theorem vecNorm1_vec2 (x y : F) :
    vecNorm1 (vec2 x y) = absF x + absF y := by
  unfold vecNorm1
  rw [finSum_two]
  unfold vec2 fin2Zero fin2One
  dsimp only
  rw [if_pos rfl, if_neg (by decide)]

theorem matVec_mat2 (a b c d x y : F) :
    matVec (mat2 a b c d) (vec2 x y) = vec2 (a * x + b * y) (c * x + d * y) := by
  funext i
  unfold matVec
  rw [finSum_two]
  unfold mat2 vec2 fin2Zero fin2One
  dsimp only
  have h10 : (1 : Nat) ≠ 0 := by decide
  by_cases hi : i.val = 0
  · simp only [hi, h10, ite_true, ite_false]
  · simp only [hi, h10, ite_true, ite_false]

theorem matMul_mat2 (a1 b1 c1 d1 a2 b2 c2 d2 : F) :
    matMul (mat2 a1 b1 c1 d1) (mat2 a2 b2 c2 d2) =
      mat2 (a1 * a2 + b1 * c2) (a1 * b2 + b1 * d2)
           (c1 * a2 + d1 * c2) (c1 * b2 + d1 * d2) := by
  funext i j
  unfold matMul
  rw [finSum_two]
  unfold mat2 fin2Zero fin2One
  dsimp only
  have h10 : (1 : Nat) ≠ 0 := by decide
  by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0 <;>
    simp only [hi, hj, h10, ite_true, ite_false]

theorem matTrace_mat2 (a b c d : F) :
    matTrace (mat2 a b c d) = a + d := by
  unfold matTrace
  rw [finSum_two]
  unfold mat2 fin2Zero fin2One
  dsimp only
  rw [if_pos rfl, if_pos rfl, if_neg (by decide), if_neg (by decide)]

omit [LinearOrderedField F] in
theorem matTranspose_mat2 (a b c d : F) :
    matTranspose (mat2 a b c d) = mat2 a c b d := by
  funext i j
  unfold matTranspose mat2
  by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
  · rw [if_pos hj, if_pos hi, if_pos hi, if_pos hj]
  · rw [if_neg hj, if_pos hi, if_pos hi, if_neg hj]
  · rw [if_pos hj, if_neg hi, if_neg hi, if_pos hj]
  · rw [if_neg hj, if_neg hi, if_neg hi, if_neg hj]

theorem matId_two : (matId 2 : Mat 2 F) = mat2 1 0 0 1 := by
  funext i j
  unfold matId mat2
  have hi2 := i.isLt
  have hj2 := j.isLt
  by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
  · have hij : i = j := Fin.ext (by omega)
    rw [if_pos hij, if_pos hi, if_pos hj]
  · have hij : i ≠ j := fun h => hj (by have := congrArg Fin.val h; omega)
    rw [if_neg hij, if_pos hi, if_neg hj]
  · have hij : i ≠ j := fun h => hi (by have := congrArg Fin.val h; omega)
    rw [if_neg hij, if_neg hi, if_pos hj]
  · have hij : i = j := Fin.ext (by omega)
    rw [if_pos hij, if_neg hi, if_neg hj]

theorem matZero_two : (matZero 2 : Mat 2 F) = mat2 0 0 0 0 := by
  funext i j
  unfold matZero mat2
  by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
  · rw [if_pos hi, if_pos hj]
  · rw [if_pos hi, if_neg hj]
  · rw [if_neg hi, if_pos hj]
  · rw [if_neg hi, if_neg hj]

theorem matAdd_mat2 (a1 b1 c1 d1 a2 b2 c2 d2 : F) :
    matAdd (mat2 a1 b1 c1 d1) (mat2 a2 b2 c2 d2) =
      mat2 (a1 + a2) (b1 + b2) (c1 + c2) (d1 + d2) := by
  funext i j
  unfold matAdd mat2
  by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
  · rw [if_pos hi, if_pos hj, if_pos hi, if_pos hj, if_pos hi, if_pos hj]
  · rw [if_pos hi, if_neg hj, if_pos hi, if_neg hj, if_pos hi, if_neg hj]
  · rw [if_neg hi, if_pos hj, if_neg hi, if_pos hj, if_neg hi, if_pos hj]
  · rw [if_neg hi, if_neg hj, if_neg hi, if_neg hj, if_neg hi, if_neg hj]

theorem matSub_mat2 (a1 b1 c1 d1 a2 b2 c2 d2 : F) :
    matSub (mat2 a1 b1 c1 d1) (mat2 a2 b2 c2 d2) =
      mat2 (a1 - a2) (b1 - b2) (c1 - c2) (d1 - d2) := by
  funext i j
  unfold matSub mat2
  by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
  · rw [if_pos hi, if_pos hj, if_pos hi, if_pos hj, if_pos hi, if_pos hj]
  · rw [if_pos hi, if_neg hj, if_pos hi, if_neg hj, if_pos hi, if_neg hj]
  · rw [if_neg hi, if_pos hj, if_neg hi, if_pos hj, if_neg hi, if_pos hj]
  · rw [if_neg hi, if_neg hj, if_neg hi, if_neg hj, if_neg hi, if_neg hj]

theorem matNeg_mat2 (a b c d : F) :
    matNeg (mat2 a b c d) = mat2 (-a) (-b) (-c) (-d) := by
  funext i j
  unfold matNeg mat2
  by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
  · rw [if_pos hi, if_pos hj, if_pos hi, if_pos hj]
  · rw [if_pos hi, if_neg hj, if_pos hi, if_neg hj]
  · rw [if_neg hi, if_pos hj, if_neg hi, if_pos hj]
  · rw [if_neg hi, if_neg hj, if_neg hi, if_neg hj]

theorem matSmul_mat2 (s a b c d : F) :
    matSmul s (mat2 a b c d) = mat2 (s * a) (s * b) (s * c) (s * d) := by
  funext i j
  unfold matSmul mat2
  by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
  · rw [if_pos hi, if_pos hj, if_pos hi, if_pos hj]
  · rw [if_pos hi, if_neg hj, if_pos hi, if_neg hj]
  · rw [if_neg hi, if_pos hj, if_neg hi, if_pos hj]
  · rw [if_neg hi, if_neg hj, if_neg hi, if_neg hj]

theorem vecSmul_vec2 (s x y : F) :
    vecSmul s (vec2 x y) = vec2 (s * x) (s * y) := by
  funext i
  unfold vecSmul vec2
  by_cases hi : i.val = 0
  · rw [if_pos hi, if_pos hi]
  · rw [if_neg hi, if_neg hi]

theorem vecNeg_vec2 (x y : F) :
    vecNeg (vec2 x y) = vec2 (-x) (-y) := by
  funext i
  unfold vecNeg vec2
  by_cases hi : i.val = 0
  · rw [if_pos hi, if_pos hi]
  · rw [if_neg hi, if_neg hi]

theorem vecAdd_vec2 (x1 y1 x2 y2 : F) :
    vecAdd (vec2 x1 y1) (vec2 x2 y2) = vec2 (x1 + x2) (y1 + y2) := by
  funext i
  unfold vecAdd vec2
  by_cases hi : i.val = 0
  · rw [if_pos hi, if_pos hi, if_pos hi]
  · rw [if_neg hi, if_neg hi, if_neg hi]

theorem eigenProj_e1 :
    eigenProj (vec2 (1 : F) 0) (vec2 1 0) = mat2 1 0 0 0 := by
  have hd : vecDot (vec2 (1 : F) 0) (vec2 1 0) = 1 := by
    rw [vecDot_vec2]
    simp only [lofOneMul, zero_mul, lofAddZero]
  funext i j
  unfold eigenProj rankOneProj
  rw [hd, div_one]
  unfold vec2 mat2
  by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0 <;>
    simp only [hi, hj, ite_true, ite_false, lofOneMul, mul_zero, zero_mul]

theorem residualProj_e1 :
    residualProj (vec2 (1 : F) 0) (vec2 1 0) = mat2 0 0 0 1 := by
  unfold residualProj
  rw [matId_two, eigenProj_e1, matSub_mat2]
  simp only [sub_self, sub_zero]

/-- Canonical Kato spectral datum for `A₀ = diag(λ₀, μ₀)` around the simple eigenvalue `λ₀`
    whenever `μ₀ - λ₀ ≠ 0`. -/
def diag2KatoData (lam0 mu0 : F) (hgap : mu0 - lam0 ≠ 0) :
    SimpleEigenvalueKatoData 2 F (mat2 lam0 0 0 mu0) lam0 where
  v0 := vec2 1 0
  w0 := vec2 1 0
  S := mat2 0 0 0 (mu0 - lam0)⁻¹
  right_eig := by
    rw [matVec_mat2, vecSmul_vec2]
    simp only [lofMulOne, mul_zero, zero_mul, lofAddZero, lofZeroAdd]
  left_eig := by
    rw [matTranspose_mat2, matVec_mat2, vecSmul_vec2]
    simp only [lofMulOne, mul_zero, zero_mul, lofAddZero, lofZeroAdd]
  pair_ne_zero := by
    rw [vecDot_vec2]
    simp only [lofOneMul, zero_mul, lofAddZero]
    exact one_ne_zero
  shifted_mul_S := by
    rw [matId_two, matSmul_mat2, matSub_mat2, matMul_mat2, residualProj_e1]
    simp only [lofMulOne, mul_zero, zero_mul, sub_self, sub_zero, lofAddZero, lofZeroAdd,
      lofMulInvCancel hgap]
  S_mul_shifted := by
    rw [matId_two, matSmul_mat2, matSub_mat2, matMul_mat2, residualProj_e1]
    simp only [lofMulOne, mul_zero, zero_mul, sub_self, sub_zero, lofAddZero, lofZeroAdd,
      inv_mul_cancel hgap]
  P_mul_S := by
    rw [eigenProj_e1, matMul_mat2, matZero_two]
    simp only [mul_zero, zero_mul, lofAddZero]
  S_mul_P := by
    rw [eigenProj_e1, matMul_mat2, matZero_two]
    simp only [mul_zero, zero_mul, lofAddZero]

/-! ### Explicit Refutations of Readings A, B, C, and D -/

theorem zero_sub_two_ne_zero : (0 : F) - twoF ≠ 0 := by
  rw [zero_sub]
  intro h
  have h2 := congrArg Neg.neg h
  rw [neg_neg, neg_zero] at h2
  exact twoF_ne_zero h2

theorem one_sub_five_eq_neg_four : (1 : F) - fiveF = - fourF := by
  unfold fiveF
  rw [lofSubEqAddNeg, neg_add_rev, lofAddComm (-fourF) (-1), ← lofAddAssoc,
      add_neg_cancel, lofZeroAdd]

theorem one_sub_five_ne_zero : (1 : F) - fiveF ≠ 0 := by
  rw [one_sub_five_eq_neg_four]
  intro h
  have h2 := congrArg Neg.neg h
  rw [neg_neg, neg_zero] at h2
  exact fourF_ne_zero h2

theorem inv_four_ne_one : (fourF : F)⁻¹ ≠ 1 := by
  intro h
  have hm := congrArg (fun x => (fourF : F) * x) h
  dsimp only at hm
  rw [lofMulInvCancel fourF_ne_zero, lofMulOne] at hm
  have hgt : (1 : F) < fourF := by
    unfold fourF twoF
    have h12 : (1 : F) < 1 + 1 := by
      have h0 := add_lt_add_left (LinearOrderedField.zero_lt_one (F := F)) 1
      rw [lofAddZero] at h0
      exact h0
    have h24 : (1 : F) + 1 < (1 + 1) + (1 + 1) := by
      have h0 := add_lt_add_left (twoF_pos (F := F)) twoF
      rw [lofAddZero] at h0
      exact h0
    exact lt_trans h12 h24
  exact ne_of_lt hgt hm

theorem inv_four_ne_neg_one : (fourF : F)⁻¹ ≠ -1 := by
  have hp : (0 : F) < (fourF : F)⁻¹ := inv_pos_of_pos fourF_pos
  have hn : (-1 : F) < 0 := by
    have h0 := add_lt_add_right (LinearOrderedField.zero_lt_one (F := F)) (-1)
    rw [lofZeroAdd, add_neg_cancel] at h0
    exact h0
  exact ne_of_gt (lt_trans hn hp)

/-- **Refutation of Reading A (First-Order Eigenvalue Coefficient via `Q = I - P`):**
    On `A₀ = diag(2, 0)` around the simple eigenvalue `λ₀ = 2`:
    1. With `A₁ = diag(1, 0)`, exact `λ₁ = 1`, whereas `tr(Q A₁) = 0`, `w₀ᵀ Q A₁ v₀ / w₀ᵀ v₀ = 0`,
       and `‖Q A₁ v₀‖₁ = 0`.
    2. With `A₁ = diag(0, 5)`, exact `λ₁ = 0`, whereas `tr(Q A₁) = 5 ≠ 0` (`λ₁ ≠ ± tr(Q A₁)`).
    3. With `A₁ = [[0, 1], [1, 0]]`, exact `λ₁ = 0`, whereas `‖Q A₁ v₀‖₁ = 1 ≠ |λ₁|` and
       `‖Q A₁ v₀‖₂² = 1 ≠ λ₁²`. -/
theorem readingA_refuted :
    let D := diag2KatoData (twoF : F) 0 zero_sub_two_ne_zero
    let A1_10 := mat2 (1 : F) 0 0 0
    let A1_05 := mat2 (0 : F) 0 0 fiveF
    let A1_off := mat2 (0 : F) 1 1 0
    -- Case 1: A₁ = diag(1, 0)
    (D.katoLambda A1_10 1 = 1 ∧
     matTrace (matMul D.Q A1_10) = 0 ∧
     D.katoLambda A1_10 1 ≠ matTrace (matMul D.Q A1_10) ∧
     D.katoLambda A1_10 1 ≠ - matTrace (matMul D.Q A1_10) ∧
     D.katoLambda A1_10 1 ≠ vecDot D.w0 (matVec D.Q (matVec A1_10 D.v0)) / vecDot D.w0 D.v0 ∧
     absF (D.katoLambda A1_10 1) ≠ vecNorm1 (matVec D.Q (matVec A1_10 D.v0))) ∧
    -- Case 2: A₁ = diag(0, 5)
    (D.katoLambda A1_05 1 = 0 ∧
     matTrace (matMul D.Q A1_05) = fiveF ∧
     D.katoLambda A1_05 1 ≠ matTrace (matMul D.Q A1_05) ∧
     D.katoLambda A1_05 1 ≠ - matTrace (matMul D.Q A1_05)) ∧
    -- Case 3: Off-diagonal A₁ = [[0, 1], [1, 0]]
    (D.katoLambda A1_off 1 = 0 ∧
     vecNorm1 (matVec D.Q (matVec A1_off D.v0)) = 1 ∧
     vecDot (matVec D.Q (matVec A1_off D.v0)) (matVec D.Q (matVec A1_off D.v0)) = 1 ∧
     absF (D.katoLambda A1_off 1) ≠ vecNorm1 (matVec D.Q (matVec A1_off D.v0)) ∧
     D.katoLambda A1_off 1 * D.katoLambda A1_off 1 ≠
       vecDot (matVec D.Q (matVec A1_off D.v0)) (matVec D.Q (matVec A1_off D.v0))) := by
  intro D A1_10 A1_05 A1_off
  have hDP : D.P = mat2 1 0 0 0 := eigenProj_e1
  have hDQ : D.Q = mat2 0 0 0 1 := residualProj_e1
  -- Case 1
  have hlam10 : D.katoLambda A1_10 1 = 1 := by
    rw [(D.kato_first_order_eigenvalue A1_10).2.1, hDP, matMul_mat2, matTrace_mat2]
    simp only [lofOneMul, zero_mul, mul_zero, lofAddZero, lofZeroAdd]
  have htrQ10 : matTrace (matMul D.Q A1_10) = 0 := by
    rw [hDQ, matMul_mat2, matTrace_mat2]
    simp only [zero_mul, mul_zero, lofAddZero, lofZeroAdd]
  have hQA10 : matVec D.Q (matVec A1_10 D.v0) = vec2 0 0 := by
    change matVec D.Q (matVec A1_10 (vec2 1 0)) = vec2 0 0
    rw [hDQ, matVec_mat2, matVec_mat2]
    simp only [lofOneMul, mul_zero, zero_mul, lofAddZero, lofZeroAdd]
  have hnorm10 : vecNorm1 (matVec D.Q (matVec A1_10 D.v0)) = 0 := by
    rw [hQA10, vecNorm1_vec2, absF_zero, lofAddZero]
  -- Case 2
  have hlam05 : D.katoLambda A1_05 1 = 0 := by
    rw [(D.kato_first_order_eigenvalue A1_05).2.1, hDP, matMul_mat2, matTrace_mat2]
    simp only [mul_zero, zero_mul, lofAddZero, lofZeroAdd]
  have htrQ05 : matTrace (matMul D.Q A1_05) = fiveF := by
    rw [hDQ, matMul_mat2, matTrace_mat2]
    simp only [zero_mul, mul_zero, lofOneMul, lofAddZero, lofZeroAdd]
  -- Case 3
  have hlamOff : D.katoLambda A1_off 1 = 0 := by
    rw [(D.kato_first_order_eigenvalue A1_off).2.1, hDP, matMul_mat2, matTrace_mat2]
    simp only [mul_zero, zero_mul, lofAddZero, lofZeroAdd]
  have hQAoff : matVec D.Q (matVec A1_off D.v0) = vec2 0 1 := by
    change matVec D.Q (matVec A1_off (vec2 1 0)) = vec2 0 1
    rw [hDQ, matVec_mat2, matVec_mat2]
    simp only [zero_mul, mul_zero, lofOneMul, lofMulOne, lofAddZero, lofZeroAdd]
  have hnormOff : vecNorm1 (matVec D.Q (matVec A1_off D.v0)) = 1 := by
    rw [hQAoff, vecNorm1_vec2, absF_zero, absF_of_nonneg one_nonneg, lofZeroAdd]
  have hdotOff : vecDot (matVec D.Q (matVec A1_off D.v0)) (matVec D.Q (matVec A1_off D.v0)) = 1 := by
    rw [hQAoff, vecDot_vec2, zero_mul, lofOneMul, lofZeroAdd]
  refine ⟨⟨hlam10, htrQ10, ?_, ?_, ?_, ?_⟩, ⟨hlam05, htrQ05, ?_, ?_⟩,
          ⟨hlamOff, hnormOff, hdotOff, ?_, ?_⟩⟩
  · rw [hlam10, htrQ10]; exact one_ne_zero
  · rw [hlam10, htrQ10, neg_zero]; exact one_ne_zero
  · rw [hlam10, w0_Q_rayleigh_identically_zero]; exact one_ne_zero
  · rw [hlam10, absF_of_nonneg one_nonneg, hnorm10]; exact one_ne_zero
  · rw [hlam05, htrQ05]; exact Ne.symm fiveF_ne_zero
  · rw [hlam05, htrQ05]
    intro h
    have h2 := congrArg Neg.neg h
    rw [neg_zero, neg_neg] at h2
    exact fiveF_ne_zero h2.symm
  · rw [hlamOff, absF_zero, hnormOff]; exact LinearOrderedField.zero_ne_one
  · rw [hlamOff, zero_mul, hdotOff]; exact LinearOrderedField.zero_ne_one

/-- **Refutation of Reading B (First-Order Eigenvector Coefficient `v₁ = ± Q A₁ v₀`):**
    On `A₀ = diag(5, 1)` at `λ₀ = 5` with `A₁ = [[0, 1], [1, 0]]`, the exact Kato eigenvector
    slope is `v₁ = - S A₁ v₀ = (0, 1/4)ᵀ` (weighted by the inverse spectral gap `(5 - 1)⁻¹ = 1/4`),
    whereas `± Q A₁ v₀ = (0, ± 1)ᵀ`, so `v₁ ≠ Q A₁ v₀` and `v₁ ≠ - Q A₁ v₀`. -/
theorem readingB_refuted :
    let D := diag2KatoData (fiveF : F) 1 one_sub_five_ne_zero
    let A1 := mat2 (0 : F) 1 1 0
    D.katoVec A1 1 = vec2 0 (fourF : F)⁻¹ ∧
    matVec D.Q (matVec A1 D.v0) = vec2 0 1 ∧
    D.katoVec A1 1 ≠ matVec D.Q (matVec A1 D.v0) ∧
    D.katoVec A1 1 ≠ vecNeg (matVec D.Q (matVec A1 D.v0)) := by
  intro D A1
  have hDS : D.S = mat2 0 0 0 (-(fourF : F)⁻¹) := by
    change mat2 0 0 0 ((1 : F) - fiveF)⁻¹ = mat2 0 0 0 (-(fourF : F)⁻¹)
    rw [one_sub_five_eq_neg_four, inv_neg]
  have hv1 : D.katoVec A1 1 = vec2 0 (fourF : F)⁻¹ := by
    rw [D.kato_first_order_eigenvector A1, hDS]
    change vecNeg (matVec (mat2 0 0 0 (-(fourF : F)⁻¹)) (matVec (mat2 0 1 1 0) (vec2 1 0))) = _
    rw [matVec_mat2, matVec_mat2, vecNeg_vec2]
    simp only [zero_mul, mul_zero, lofOneMul, lofMulOne, lofAddZero, lofZeroAdd, neg_zero, neg_neg]
  have hQAv0 : matVec D.Q (matVec A1 D.v0) = vec2 0 1 := by
    have hDQ : D.Q = mat2 0 0 0 1 := residualProj_e1
    change matVec D.Q (matVec (mat2 0 1 1 0) (vec2 1 0)) = vec2 0 1
    rw [hDQ, matVec_mat2, matVec_mat2]
    simp only [zero_mul, mul_zero, lofOneMul, lofMulOne, lofAddZero, lofZeroAdd]
  refine ⟨hv1, hQAv0, ?_, ?_⟩
  · intro heq
    rw [hv1, hQAv0] at heq
    exact inv_four_ne_one (vec2_ext heq).2
  · intro heq
    rw [hv1, hQAv0, vecNeg_vec2] at heq
    exact inv_four_ne_neg_one (vec2_ext heq).2

/-- **Refutation of Reading C (Second-Order Eigenvalue Coefficient `λ₂ = ± tr(P A₁ Q A₁)`):**
    On `A₀ = diag(5, 1)` at `λ₀ = 5` with `A₁ = [[0, 1], [1, 0]]`, the exact Kato quadratic
    coefficient is `λ₂ = - tr(P A₁ S A₁) = + 1/4` (from `λ(ε) = 3 + √(4 + ε²) = 5 + ε²/4 - ...`),
    whereas `tr(P A₁ Q A₁) = 1`, so `λ₂ ≠ ± tr(P A₁ Q A₁)`. -/
theorem readingC_refuted :
    let D := diag2KatoData (fiveF : F) 1 one_sub_five_ne_zero
    let A1 := mat2 (0 : F) 1 1 0
    D.katoLambda A1 2 = (fourF : F)⁻¹ ∧
    matTrace (matMul (matMul (matMul D.P A1) D.Q) A1) = 1 ∧
    D.katoLambda A1 2 ≠ matTrace (matMul (matMul (matMul D.P A1) D.Q) A1) ∧
    D.katoLambda A1 2 ≠ - matTrace (matMul (matMul (matMul D.P A1) D.Q) A1) := by
  intro D A1
  have hDP : D.P = mat2 1 0 0 0 := eigenProj_e1
  have hDQ : D.Q = mat2 0 0 0 1 := residualProj_e1
  have hDS : D.S = mat2 0 0 0 (-(fourF : F)⁻¹) := by
    change mat2 0 0 0 ((1 : F) - fiveF)⁻¹ = mat2 0 0 0 (-(fourF : F)⁻¹)
    rw [one_sub_five_eq_neg_four, inv_neg]
  have hlam2 : D.katoLambda A1 2 = (fourF : F)⁻¹ := by
    rw [(D.kato_second_order_eigenvalue A1).2, hDP, hDS]
    rw [matMul_mat2, matMul_mat2, matMul_mat2, matTrace_mat2]
    simp only [mul_zero, zero_mul, lofOneMul, lofMulOne, lofZeroAdd, lofAddZero, neg_zero, neg_neg]
  have htrPAQA : matTrace (matMul (matMul (matMul D.P A1) D.Q) A1) = 1 := by
    rw [hDP, hDQ, matMul_mat2, matMul_mat2, matMul_mat2, matTrace_mat2]
    simp only [mul_zero, zero_mul, lofOneMul, lofMulOne, lofZeroAdd, lofAddZero]
  refine ⟨hlam2, htrPAQA, ?_, ?_⟩
  · rw [hlam2, htrPAQA]; exact inv_four_ne_one
  · rw [hlam2, htrPAQA]; exact inv_four_ne_neg_one

/-- **Refutation of Reading D (First-Order Eigenprojection Coefficient `P₁` via `Q`):**
    On `A₀ = diag(5, 1)` at `λ₀ = 5` with `A₁ = [[0, 1], [1, 0]]`, the exact Kato eigenprojection
    derivative is `P₁ = - P A₁ S - S A₁ P = [[0, 1/4], [1/4, 0]]`, which disagrees with `± Q`
    and with the unweighted residual commutator-type expression `± (P A₁ Q + Q A₁ P)`. -/
theorem readingD_refuted :
    let D := diag2KatoData (fiveF : F) 1 one_sub_five_ne_zero
    let A1 := mat2 (0 : F) 1 1 0
    let unweighted := matAdd (matMul (matMul D.P A1) D.Q) (matMul (matMul D.Q A1) D.P)
    D.katoProjFirstOrder A1 = mat2 0 (fourF : F)⁻¹ (fourF : F)⁻¹ 0 ∧
    D.katoProjFirstOrder A1 ≠ D.Q ∧
    D.katoProjFirstOrder A1 ≠ matNeg D.Q ∧
    D.katoProjFirstOrder A1 ≠ unweighted ∧
    D.katoProjFirstOrder A1 ≠ matNeg unweighted := by
  intro D A1 unweighted
  have hDP : D.P = mat2 1 0 0 0 := eigenProj_e1
  have hDQ : D.Q = mat2 0 0 0 1 := residualProj_e1
  have hDS : D.S = mat2 0 0 0 (-(fourF : F)⁻¹) := by
    change mat2 0 0 0 ((1 : F) - fiveF)⁻¹ = mat2 0 0 0 (-(fourF : F)⁻¹)
    rw [one_sub_five_eq_neg_four, inv_neg]
  have hP1 : D.katoProjFirstOrder A1 = mat2 0 (fourF : F)⁻¹ (fourF : F)⁻¹ 0 := by
    unfold SimpleEigenvalueKatoData.katoProjFirstOrder
    rw [hDP, hDS, matMul_mat2, matMul_mat2, matMul_mat2, matMul_mat2, matAdd_mat2, matNeg_mat2]
    simp only [mul_zero, zero_mul, lofOneMul, lofMulOne, lofAddZero, lofZeroAdd, neg_zero, neg_neg]
  have hunw : unweighted = mat2 0 1 1 0 := by
    unfold unweighted
    rw [hDP, hDQ, matMul_mat2, matMul_mat2, matMul_mat2, matMul_mat2, matAdd_mat2]
    simp only [mul_zero, zero_mul, lofOneMul, lofMulOne, lofAddZero, lofZeroAdd]
  refine ⟨hP1, ?_, ?_, ?_, ?_⟩
  · intro heq
    rw [hP1, hDQ] at heq
    exact LinearOrderedField.zero_ne_one (mat2_entry_11 heq)
  · intro heq
    rw [hP1, hDQ, matNeg_mat2] at heq
    have h01 := mat2_entry_11 heq
    have h1 := congrArg Neg.neg h01
    rw [neg_zero, neg_neg] at h1
    exact LinearOrderedField.zero_ne_one h1
  · intro heq
    rw [hP1, hunw] at heq
    exact inv_four_ne_one (mat2_entry_01 heq)
  · intro heq
    rw [hP1, hunw, matNeg_mat2] at heq
    exact inv_four_ne_neg_one (mat2_entry_01 heq)

/-! ### Sharpness of Simplicity in Clause 1: Defective Jordan Puiseux Obstruction -/

/-- **Defective Jordan Perturbation Obstruction (`A(ε) = [[0, 1], [ε, 0]]`):**
    Around the algebraically double defective eigenvalue `λ₀ = 0` of `A₀ = [[0, 1], [0, 0]]`,
    `χ_{A(ε)}(λ) = λ² - ε` has Puiseux branches `± √ε` and admits NO formal power series
    eigenvalue root and NO formal power series eigenpair `(λ(ε), v(ε))` with `v₀ ≠ 0`. -/
theorem defective_jordan_not_analytically_perturbable :
    let A0 := mat2 (0 : F) 1 0 0
    let A1 := mat2 (0 : F) 0 1 0
    -- (1) No formal power series root of `λ(ε)² - ε = 0` even through degree 1:
    (¬ ∃ lamSeq : Nat → F,
        lamSeq 0 * lamSeq 0 = 0 ∧
        (lamSeq 0 * lamSeq 1 + lamSeq 1 * lamSeq 0) - 1 = 0) ∧
    -- (2) No formal power series eigenpair `(λ(ε), v(ε))` with `v₀ ≠ 0` even through degree 1:
    (¬ ∃ (lamSeq : Nat → F) (vecSeq : Nat → Vec 2 F),
        vecSeq 0 ≠ vecZero 2 ∧
        matVec A0 (vecSeq 0) = vecSmul (lamSeq 0) (vecSeq 0) ∧
        vecAdd (matVec A0 (vecSeq 1)) (matVec A1 (vecSeq 0)) =
          vecAdd (vecSmul (lamSeq 0) (vecSeq 1)) (vecSmul (lamSeq 1) (vecSeq 0))) := by
  intro A0 A1
  refine ⟨?_, ?_⟩
  · intro ⟨lamSeq, hdeg0, hdeg1⟩
    have hl0 : lamSeq 0 = 0 := by
      rcases mul_eq_zero.mp hdeg0 with h | h <;> exact h
    rw [hl0, zero_mul, mul_zero, lofAddZero, zero_sub] at hdeg1
    have h1 := congrArg Neg.neg hdeg1
    rw [neg_neg, neg_zero] at h1
    exact one_ne_zero h1
  · intro ⟨lamSeq, vecSeq, hv0_ne, heq0, heq1⟩
    let x0 := vecSeq 0 fin2Zero
    let y0 := vecSeq 0 fin2One
    let x1 := vecSeq 1 fin2Zero
    let y1 := vecSeq 1 fin2One
    have hv0_rep : vecSeq 0 = vec2 x0 y0 := by
      funext i
      have hi2 := i.isLt
      unfold vec2 x0 y0 fin2Zero fin2One
      by_cases hi : i.val = 0
      · rw [if_pos hi]
        exact congrArg (vecSeq 0) (Fin.ext hi)
      · rw [if_neg hi]
        have hi1 : i.val = 1 := by omega
        exact congrArg (vecSeq 0) (Fin.ext hi1)
    have hv1_rep : vecSeq 1 = vec2 x1 y1 := by
      funext i
      have hi2 := i.isLt
      unfold vec2 x1 y1 fin2Zero fin2One
      by_cases hi : i.val = 0
      · rw [if_pos hi]
        exact congrArg (vecSeq 1) (Fin.ext hi)
      · rw [if_neg hi]
        have hi1 : i.val = 1 := by omega
        exact congrArg (vecSeq 1) (Fin.ext hi1)
    unfold A0 at heq0
    rw [hv0_rep, matVec_mat2, vecSmul_vec2] at heq0
    simp only [zero_mul, mul_zero, lofOneMul, lofMulOne, lofZeroAdd, lofAddZero] at heq0
    have ⟨hy0_eq, h0_eq⟩ := vec2_ext heq0
    -- From `0 = lamSeq 0 * y0` and `y0 = lamSeq 0 * x0`:
    have hx0_ne : x0 ≠ 0 := by
      intro hx0
      apply hv0_ne
      rw [hv0_rep, hy0_eq, hx0, mul_zero]
      funext i
      unfold vec2 vecZero
      by_cases hi : i.val = 0
      · rw [if_pos hi]
      · rw [if_neg hi]
    have hlam0_zero : lamSeq 0 = 0 := by
      rcases mul_eq_zero.mp h0_eq.symm with hl | hy
      · exact hl
      · rw [hy] at hy0_eq
        rcases mul_eq_zero.mp hy0_eq.symm with hl | hx
        · exact hl
        · exact False.elim (hx0_ne hx)
    have hy0_zero : y0 = 0 := by
      rw [hy0_eq, hlam0_zero, zero_mul]
    -- Now examine the degree-1 equation second coordinate: `x0 = 0`!
    unfold A0 A1 at heq1
    rw [hv0_rep, hv1_rep, hy0_zero, hlam0_zero,
        matVec_mat2, matVec_mat2, vecAdd_vec2, vecSmul_vec2, vecSmul_vec2, vecAdd_vec2] at heq1
    have hrow2 := (vec2_ext heq1).2
    simp only [zero_mul, mul_zero, lofOneMul, lofMulOne, lofAddZero, lofZeroAdd] at hrow2
    exact hx0_ne hrow2

end TwoByTwoExplicitCalculus

end Conjecture00000007179
