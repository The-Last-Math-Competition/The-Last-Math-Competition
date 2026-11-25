/-
Copyright (c) 2026. All rights reserved.
Formalization of Conjecture 00000007179 in Core Lean 4.19.0 (zero external dependencies).

Module: Conjecture00000007179.KatoPerturbation
Purpose:
  Complete formalization of Clause 1 (Kato's analytic perturbation theory for
  algebraically simple eigenvalues):
  1. Lagrange-Sylvester-Riesz polynomial construction of the spectral eigenprojection `P`,
     complementary (residual) projection `Q = I - P`, and Kato reduced resolvent `S`
     directly from a factored characteristic relation `(A₀ - λ₀ I) q(A₀) = 0` with `q(λ₀) ≠ 0`.
  2. Exact properties and uniqueness of `(P, Q, S)` for `SimpleEigenvalueKatoData`.
  3. Constructive all-orders Kato formal power series `(katoLambda, katoVec)` satisfying
     normalization `w₀ᵀ v_k = 0` (`k ≥ 1`), the exact perturbed eigenvalue equation at every
     order `k ≥ 0`, and all-orders uniqueness.
  4. Exact closed-form first- and second-order Kato perturbation formulas:
       * `λ₁ = tr(P A₁) = tr(P A₁ P) = (w₀ᵀ A₁ v₀) / (w₀ᵀ v₀)`,
       * `v₁ = - S A₁ v₀`,
       * `λ₂ = - tr(P A₁ S A₁) = - (w₀ᵀ A₁ S A₁ v₀) / (w₀ᵀ v₀)`,
       * `P₁ = - P A₁ S - S A₁ P` (first-order eigenprojection derivative).
  5. Explicit Cauchy-Kato analytic convergence majorant theorem: explicit positive radius
     `R₀ = ρ⁻¹ > 0` with `‖v_k‖₁ ≤ ‖v₀‖₁ / (k + 1)² · ρ^k`, `|λ_k| ≤ α ‖v₀‖₁ / k² · ρ^(k-1)`,
     and explicit `O(1 / N)` Cauchy tail bounds for all `|ε| ≤ R₀`.
-/

import Conjecture00000007179.OrderedField

namespace Conjecture00000007179

section VectorRangeSums

variable {F : Type u} [LinearOrderedField F]

/-- Finite range sum of vectors in `Vec n F`: `v(a) + v(a+1) + ... + v(a+len-1)`. -/
def vecSumRange {n : Nat} (a : Nat) : Nat → (Nat → Vec n F) → Vec n F
  | 0, _ => vecZero n
  | len + 1, f => vecAdd (vecSumRange a len f) (f (a + len))

theorem vecSumRange_eval {n : Nat} (a len : Nat) (f : Nat → Vec n F) (i : Fin n) :
    vecSumRange a len f i = sumRange a len (fun j => f j i) := by
  induction len with
  | zero => rfl
  | succ k ih =>
    unfold vecSumRange vecAdd sumRange
    rw [ih]

theorem vecSumRange_congr {n : Nat} (a len : Nat) {f g : Nat → Vec n F}
    (h : ∀ j, a ≤ j → j < a + len → f j = g j) :
    vecSumRange a len f = vecSumRange a len g := by
  funext i
  rw [vecSumRange_eval, vecSumRange_eval]
  exact sumRange_congr a len (fun j h1 h2 => congrFun (h j h1 h2) i)

theorem matVec_vecSumRange {n : Nat} (A : Mat n F) (a len : Nat) (f : Nat → Vec n F) :
    matVec A (vecSumRange a len f) = vecSumRange a len (fun j => matVec A (f j)) := by
  induction len with
  | zero =>
    unfold vecSumRange
    exact matVec_zero A
  | succ k ih =>
    unfold vecSumRange
    rw [matVec_add, ih]

theorem vecDot_vecSumRange {n : Nat} (w : Vec n F) (a len : Nat) (f : Nat → Vec n F) :
    vecDot w (vecSumRange a len f) = sumRange a len (fun j => vecDot w (f j)) := by
  induction len with
  | zero =>
    unfold vecSumRange sumRange
    exact vecDot_zero_right w
  | succ k ih =>
    unfold vecSumRange sumRange
    rw [vecDot_add_right, ih]

theorem vecNorm1_vecSumRange_le {n : Nat} (a len : Nat) (f : Nat → Vec n F) :
    vecNorm1 (vecSumRange a len f) ≤ sumRange a len (fun j => vecNorm1 (f j)) := by
  induction len with
  | zero =>
    unfold vecSumRange sumRange
    rw [vecNorm1_zero]
    exact LinearOrderedField.le_refl 0
  | succ k ih =>
    unfold vecSumRange sumRange
    exact LinearOrderedField.le_trans (vecNorm1_add_le _ _)
      (add_le_add ih (LinearOrderedField.le_refl _))

theorem sumRange_zero_fn (a len : Nat) : sumRange a len (fun _ => (0 : F)) = 0 := by
  induction len with
  | zero => rfl
  | succ k ih => rw [sumRange_succ, ih, lofAddZero]

end VectorRangeSums

section RieszPolynomialConstruction

variable {F : Type u} [LinearOrderedField F]

/-- Scalar polynomial evaluation (ascending coefficients `c₀ + x (c₁ + ...)`). -/
def polyEvalScalar : List F → F → F
  | [], _ => 0
  | c :: cs, x => c + x * polyEvalScalar cs x

/-- Matrix polynomial evaluation `c₀ I + A (c₁ I + ...)`. -/
def polyEvalMat {n : Nat} : List F → Mat n F → Mat n F
  | [], _ => matZero n
  | c :: cs, A => matAdd (matSmul c (matId n)) (matMul A (polyEvalMat cs A))

theorem polyEvalMat_nil {n : Nat} (A : Mat n F) : polyEvalMat [] A = matZero n := rfl

theorem polyEvalMat_cons {n : Nat} (c : F) (cs : List F) (A : Mat n F) :
    polyEvalMat (c :: cs) A = matAdd (matSmul c (matId n)) (matMul A (polyEvalMat cs A)) := rfl

/-- Exact synthetic division `(q(x) - q(λ₀)) / (x - λ₀)`. -/
def polyDivLinear : List F → F → List F
  | [], _ => []
  | _ :: cs, lam0 => polyEvalScalar cs lam0 :: polyDivLinear cs lam0

theorem matMul_comm_polyEvalMat {n : Nat} (A : Mat n F) (p : List F) :
    matMul A (polyEvalMat p A) = matMul (polyEvalMat p A) A := by
  induction p with
  | nil =>
    rw [polyEvalMat_nil, matMul_zero_right, matMul_zero_left]
  | cons c cs ih =>
    rw [polyEvalMat_cons, matMul_add_right, matMul_add_left,
        matMul_smul_right, matMul_smul_left, matMul_id_right, matMul_id_left,
        matMul_assoc A (polyEvalMat cs A) A, ← ih]

theorem polyEvalMat_comm {n : Nat} (A : Mat n F) (p q : List F) :
    matMul (polyEvalMat p A) (polyEvalMat q A) =
    matMul (polyEvalMat q A) (polyEvalMat p A) := by
  induction p with
  | nil =>
    rw [polyEvalMat_nil, matMul_zero_left, matMul_zero_right]
  | cons c cs ih =>
    rw [polyEvalMat_cons, matMul_add_left, matMul_add_right,
        matMul_smul_left, matMul_smul_right, matMul_id_left, matMul_id_right,
        matMul_assoc A (polyEvalMat cs A) (polyEvalMat q A), ih,
        ← matMul_assoc A (polyEvalMat q A) (polyEvalMat cs A),
        matMul_comm_polyEvalMat A q,
        matMul_assoc (polyEvalMat q A) A (polyEvalMat cs A)]

theorem polyEvalMat_factor_sub {n : Nat} (p : List F) (A : Mat n F) (lam0 : F) :
    polyEvalMat p A =
      matAdd (matSmul (polyEvalScalar p lam0) (matId n))
        (matMul (matSub A (matSmul lam0 (matId n))) (polyEvalMat (polyDivLinear p lam0) A)) := by
  induction p with
  | nil =>
    have hs : polyEvalScalar ([] : List F) lam0 = 0 := rfl
    have hd : polyDivLinear ([] : List F) lam0 = [] := rfl
    rw [polyEvalMat_nil, hs, hd, polyEvalMat_nil, matMul_zero_right]
    funext i j
    unfold matAdd matSmul matZero
    rw [zero_mul, lofAddZero]
  | cons c cs ih =>
    let s := polyEvalScalar cs lam0
    let R := polyEvalMat (polyDivLinear cs lam0) A
    let B := matSub A (matSmul lam0 (matId n))
    change matAdd (matSmul c (matId n)) (matMul A (polyEvalMat cs A)) =
      matAdd (matSmul (c + lam0 * s) (matId n))
        (matMul B (matAdd (matSmul s (matId n)) (matMul A R)))
    rw [ih]
    change matAdd (matSmul c (matId n)) (matMul A (matAdd (matSmul s (matId n)) (matMul B R))) =
      matAdd (matSmul (c + lam0 * s) (matId n))
        (matMul B (matAdd (matSmul s (matId n)) (matMul A R)))
    have hAB : matMul A B = matMul B A := by
      unfold B
      rw [matMul_sub_right, matMul_sub_left, matMul_smul_right, matMul_smul_left,
          matMul_id_right, matMul_id_left]
    have hABR : matMul A (matMul B R) = matMul B (matMul A R) := by
      rw [← matMul_assoc, hAB, matMul_assoc]
    rw [matMul_add_right, matMul_add_right, hABR]
    have hAs : matMul A (matSmul s (matId n)) =
        matAdd (matSmul (lam0 * s) (matId n)) (matMul B (matSmul s (matId n))) := by
      funext i j
      rw [matMul_smul_right, matMul_id_right, matMul_smul_right, matMul_id_right]
      unfold matAdd B matSub
      unfold matSmul
      rw [mul_sub, ← lofMulAssoc s lam0 (matId n i j), lofMulComm s lam0,
          lofAddComm (lam0 * s * matId n i j) _, sub_add_cancel]
    rw [hAs]
    funext i j
    unfold matAdd matSmul
    rw [lofRightDistrib c (lam0 * s) (matId n i j), lofAddAssoc, lofAddAssoc]

/-- Lagrange-Sylvester-Riesz polynomial spectral projection `P = q(λ₀)⁻¹ q(A₀)`. -/
def rieszPolyProj {n : Nat} (A0 : Mat n F) (lam0 : F) (q : List F) : Mat n F :=
  matSmul (polyEvalScalar q lam0)⁻¹ (polyEvalMat q A0)

/-- Complementary (residual) polynomial projection `Q = I - P`. -/
def rieszPolyResidualProj {n : Nat} (A0 : Mat n F) (lam0 : F) (q : List F) : Mat n F :=
  matSub (matId n) (rieszPolyProj A0 lam0 q)

/-- Kato polynomial reduced resolvent `S = - q(λ₀)⁻¹ r(A₀) Q`. -/
def rieszPolyReducedResolvent {n : Nat} (A0 : Mat n F) (lam0 : F) (q : List F) : Mat n F :=
  matSmul (-(polyEvalScalar q lam0)⁻¹)
    (matMul (polyEvalMat (polyDivLinear q lam0) A0) (rieszPolyResidualProj A0 lam0 q))

/-- **Theorem (Lagrange-Sylvester-Riesz Polynomial Construction).**
    Whenever `(A₀ - λ₀ I) q(A₀) = 0` and `q(λ₀) ≠ 0`, the polynomial operators `(P, Q, S)`
    satisfy all Riesz-Kato projection and reduced-resolvent identities. -/
theorem rieszPoly_kato_identities {n : Nat} (A0 : Mat n F) (lam0 : F) (q : List F)
    (hCH : matMul (matSub A0 (matSmul lam0 (matId n))) (polyEvalMat q A0) = matZero n)
    (hq : polyEvalScalar q lam0 ≠ 0) :
    let P := rieszPolyProj A0 lam0 q
    let Q := rieszPolyResidualProj A0 lam0 q
    let S := rieszPolyReducedResolvent A0 lam0 q
    let B := matSub A0 (matSmul lam0 (matId n))
    matMul P P = P ∧
    matMul Q Q = Q ∧
    matMul P Q = matZero n ∧
    matMul Q P = matZero n ∧
    matMul A0 P = matSmul lam0 P ∧
    matMul P A0 = matSmul lam0 P ∧
    matMul B S = Q ∧
    matMul S B = Q ∧
    matMul P S = matZero n ∧
    matMul S P = matZero n := by
  intro P Q S B
  let mu := polyEvalScalar q lam0
  let R := polyEvalMat (polyDivLinear q lam0) A0
  have hBP : matMul B P = matZero n := by
    unfold P rieszPolyProj
    rw [matMul_smul_right, hCH]
    funext i j
    exact mul_zero _
  have hPB : matMul P B = matZero n := by
    have hqB : matMul (polyEvalMat q A0) B = matMul B (polyEvalMat q A0) := by
      change matMul (polyEvalMat q A0) (matSub A0 (matSmul lam0 (matId n))) =
        matMul (matSub A0 (matSmul lam0 (matId n))) (polyEvalMat q A0)
      rw [matMul_sub_right, matMul_sub_left, matMul_smul_right, matMul_smul_left,
          matMul_id_right, matMul_id_left, ← matMul_comm_polyEvalMat]
    change matMul (matSmul mu⁻¹ (polyEvalMat q A0)) B = matZero n
    rw [matMul_smul_left, hqB, hCH]
    funext i j
    exact mul_zero _
  have hFactor : polyEvalMat q A0 = matAdd (matSmul mu (matId n)) (matMul B R) :=
    polyEvalMat_factor_sub q A0 lam0
  have hQ_eq : Q = matSmul (-mu⁻¹) (matMul B R) := by
    change matSub (matId n) (matSmul mu⁻¹ (polyEvalMat q A0)) = matSmul (-mu⁻¹) (matMul B R)
    rw [hFactor]
    funext i j
    unfold matSub matSmul matAdd
    rw [lofLeftDistrib, ← lofMulAssoc mu⁻¹ mu _, inv_mul_cancel hq, lofOneMul,
        neg_mul, lofSubEqAddNeg, neg_add_rev, ← lofAddAssoc, add_neg_cancel, lofZeroAdd]
  have hPP : matMul P P = P := by
    have hRB : matMul B R = matMul R B := by
      unfold B R
      rw [matMul_sub_left, matMul_sub_right, matMul_smul_left, matMul_smul_right,
          matMul_id_left, matMul_id_right, matMul_comm_polyEvalMat]
    calc
      matMul P P = matSmul mu⁻¹ (matMul (polyEvalMat q A0) P) := by
        change matMul (matSmul mu⁻¹ (polyEvalMat q A0)) P = _
        rw [matMul_smul_left]
      _ = matSmul mu⁻¹ (matAdd (matSmul mu P) (matMul R (matMul B P))) := by
        rw [hFactor, matMul_add_left, matMul_smul_left, matMul_id_left, hRB, matMul_assoc]
      _ = P := by
        rw [hBP, matMul_zero_right]
        funext i j
        unfold matSmul matAdd matZero
        rw [lofAddZero, ← lofMulAssoc, inv_mul_cancel hq, lofOneMul]
  have hPQ : matMul P Q = matZero n := by
    change matMul P (matSub (matId n) P) = matZero n
    rw [matMul_sub_right, matMul_id_right, hPP]
    funext i j
    exact sub_self _
  have hQP : matMul Q P = matZero n := by
    change matMul (matSub (matId n) P) P = matZero n
    rw [matMul_sub_left, matMul_id_left, hPP]
    funext i j
    exact sub_self _
  have hQQ : matMul Q Q = Q := by
    change matMul Q (matSub (matId n) P) = Q
    rw [matMul_sub_right, matMul_id_right, hQP]
    funext i j
    exact sub_zero _
  have hA0P : matMul A0 P = matSmul lam0 P := by
    have h1 : matSub (matMul A0 P) (matSmul lam0 P) = matZero n := by
      rw [← hBP]
      unfold B
      rw [matMul_sub_left, matMul_smul_left, matMul_id_left]
    funext i j
    exact sub_eq_zero.mp (congrFun (congrFun h1 i) j)
  have hPA0 : matMul P A0 = matSmul lam0 P := by
    have h1 : matSub (matMul P A0) (matSmul lam0 P) = matZero n := by
      rw [← hPB]
      unfold B
      rw [matMul_sub_right, matMul_smul_right, matMul_id_right]
    funext i j
    exact sub_eq_zero.mp (congrFun (congrFun h1 i) j)
  have hBS : matMul B S = Q := by
    change matMul B (matSmul (-mu⁻¹) (matMul R Q)) = Q
    rw [matMul_smul_right, ← matMul_assoc B R Q, ← matMul_smul_left (-mu⁻¹) (matMul B R) Q,
        ← hQ_eq, hQQ]
  have hRQ_comm : matMul R Q = matMul Q R := by
    change matMul R (matSub (matId n) (matSmul mu⁻¹ (polyEvalMat q A0))) =
      matMul (matSub (matId n) (matSmul mu⁻¹ (polyEvalMat q A0))) R
    rw [matMul_sub_right, matMul_sub_left, matMul_id_right, matMul_id_left,
        matMul_smul_right, matMul_smul_left, polyEvalMat_comm]
  have hBR_comm : matMul R B = matMul B R := by
    unfold B R
    rw [matMul_sub_right, matMul_sub_left, matMul_smul_right, matMul_smul_left,
        matMul_id_right, matMul_id_left, ← matMul_comm_polyEvalMat]
  have hQB_comm : matMul Q B = matMul B Q := by
    change matMul (matSub (matId n) P) B = matMul B (matSub (matId n) P)
    rw [matMul_sub_left (matId n) P B, matMul_id_left,
        matMul_sub_right B (matId n) P, matMul_id_right,
        hPB, hBP]
  have hSB : matMul S B = Q := by
    unfold S rieszPolyReducedResolvent
    change matMul (matSmul (-mu⁻¹) (matMul R Q)) B = Q
    rw [matMul_smul_left, matMul_assoc R Q B, hQB_comm, ← matMul_assoc R B Q,
        hBR_comm, ← matMul_smul_left (-mu⁻¹) (matMul B R) Q, ← hQ_eq, hQQ]
  have hPS : matMul P S = matZero n := by
    unfold S rieszPolyReducedResolvent
    change matMul P (matSmul (-mu⁻¹) (matMul R Q)) = matZero n
    rw [matMul_smul_right, hRQ_comm, ← matMul_assoc P Q R, hPQ, matMul_zero_left]
    funext i j
    exact mul_zero _
  have hSP : matMul S P = matZero n := by
    unfold S rieszPolyReducedResolvent
    change matMul (matSmul (-mu⁻¹) (matMul R Q)) P = matZero n
    rw [matMul_smul_left, matMul_assoc R Q P, hQP, matMul_zero_right]
    funext i j
    exact mul_zero _
  exact ⟨hPP, hQQ, hPQ, hQP, hA0P, hPA0, hBS, hSB, hPS, hSP⟩

end RieszPolynomialConstruction

section KatoSpectralData

variable {F : Type u} [LinearOrderedField F]

/-- Rank-one Riesz spectral eigenprojection `P = (v₀ w₀ᵀ) / (w₀ᵀ v₀)`. -/
def eigenProj {n : Nat} (v0 w0 : Vec n F) : Mat n F :=
  rankOneProj v0 w0 (vecDot w0 v0)

/-- Complementary (residual) projection `Q = I - P` onto `im(A₀ - λ₀ I) = ker(w₀ᵀ)`. -/
def residualProj {n : Nat} (v0 w0 : Vec n F) : Mat n F :=
  matSub (matId n) (eigenProj v0 w0)

/-- **Kato Spectral Data** for an algebraically simple eigenvalue `λ₀` of `A₀`:
    right eigenvector `v₀`, left eigenvector `w₀` with `w₀ᵀ v₀ ≠ 0`, and Kato reduced
    resolvent `S` inverting `A₀ - λ₀ I` on the complementary subspace `im(Q)`. -/
structure SimpleEigenvalueKatoData (n : Nat) (F : Type u) [LinearOrderedField F]
    (A0 : Mat n F) (lam0 : F) where
  v0 : Vec n F
  w0 : Vec n F
  S : Mat n F
  right_eig : matVec A0 v0 = vecSmul lam0 v0
  left_eig : matVec (matTranspose A0) w0 = vecSmul lam0 w0
  pair_ne_zero : vecDot w0 v0 ≠ 0
  shifted_mul_S : matMul (matSub A0 (matSmul lam0 (matId n))) S = residualProj v0 w0
  S_mul_shifted : matMul S (matSub A0 (matSmul lam0 (matId n))) = residualProj v0 w0
  P_mul_S : matMul (eigenProj v0 w0) S = matZero n
  S_mul_P : matMul S (eigenProj v0 w0) = matZero n

namespace SimpleEigenvalueKatoData

variable {n : Nat} {A0 : Mat n F} {lam0 : F}

def P (D : SimpleEigenvalueKatoData n F A0 lam0) : Mat n F :=
  eigenProj D.v0 D.w0

def Q (D : SimpleEigenvalueKatoData n F A0 lam0) : Mat n F :=
  residualProj D.v0 D.w0

theorem P_matVec (D : SimpleEigenvalueKatoData n F A0 lam0) (u : Vec n F) :
    matVec D.P u = vecSmul (vecDot D.w0 u / vecDot D.w0 D.v0) D.v0 := by
  funext i
  unfold P eigenProj rankOneProj matVec vecSmul vecDot
  have h1 : (fun j => ((D.v0 i * D.w0 j) / vecDot D.w0 D.v0) * u j) =
      (fun j => (D.v0 i / vecDot D.w0 D.v0) * (D.w0 j * u j)) := by
    funext j
    rw [lofDivEqMulInv, lofDivEqMulInv]
    calc
      ((D.v0 i * D.w0 j) * (vecDot D.w0 D.v0)⁻¹) * u j
        = (D.v0 i * (D.w0 j * (vecDot D.w0 D.v0)⁻¹)) * u j := by
          rw [lofMulAssoc (D.v0 i) (D.w0 j) _]
      _ = (D.v0 i * ((vecDot D.w0 D.v0)⁻¹ * D.w0 j)) * u j := by
        rw [lofMulComm (D.w0 j) _]
      _ = ((D.v0 i * (vecDot D.w0 D.v0)⁻¹) * D.w0 j) * u j := by
        rw [← lofMulAssoc (D.v0 i) _ _]
      _ = (D.v0 i * (vecDot D.w0 D.v0)⁻¹) * (D.w0 j * u j) := lofMulAssoc _ _ _
  change finSum n (fun j => ((D.v0 i * D.w0 j) / vecDot D.w0 D.v0) * u j) =
    (finSum n (fun j => D.w0 j * u j) / vecDot D.w0 D.v0) * D.v0 i
  rw [h1, ← finSum_mul_left, div_mul_eq_mul_div, div_mul_eq_mul_div, lofMulComm (D.v0 i) _]

theorem P_v0 (D : SimpleEigenvalueKatoData n F A0 lam0) :
    matVec D.P D.v0 = D.v0 := by
  rw [D.P_matVec, div_self D.pair_ne_zero]
  funext i
  exact lofOneMul _

theorem Q_v0 (D : SimpleEigenvalueKatoData n F A0 lam0) :
    matVec D.Q D.v0 = vecZero n := by
  change matVec (matSub (matId n) D.P) D.v0 = vecZero n
  rw [sub_matVec, matVec_id, D.P_v0, vecSub_self]

theorem S_v0 (D : SimpleEigenvalueKatoData n F A0 lam0) :
    matVec D.S D.v0 = vecZero n := by
  rw [← D.P_v0, matVec_matVec]
  unfold P
  rw [D.S_mul_P, zero_matVec]

theorem P_idem (D : SimpleEigenvalueKatoData n F A0 lam0) :
    matMul D.P D.P = D.P := by
  funext i j
  let ej : Vec n F := fun k => if k = j then 1 else 0
  have hv_vec : matVec (matMul D.P D.P) ej = matVec D.P ej := by
    rw [← matVec_matVec, D.P_matVec ej, matVec_smul, D.P_v0, ← D.P_matVec ej]
  have hv := congrFun hv_vec i
  unfold matVec ej at hv
  rw [finSum_eq_single n j _ (fun k hne => by rw [if_neg hne, mul_zero]),
      finSum_eq_single n j _ (fun k hne => by rw [if_neg hne, mul_zero])] at hv
  rw [if_pos rfl, lofMulOne, lofMulOne] at hv
  exact hv

theorem trace_P (D : SimpleEigenvalueKatoData n F A0 lam0) :
    matTrace D.P = 1 := by
  have h := matTrace_rankOneProj_mul D.v0 D.w0 (vecDot D.w0 D.v0) (matId n)
  rw [matMul_id_right, matVec_id, div_self D.pair_ne_zero] at h
  exact h

theorem Q_idem (D : SimpleEigenvalueKatoData n F A0 lam0) :
    matMul D.Q D.Q = D.Q := by
  unfold Q residualProj
  change matMul (matSub (matId n) D.P) (matSub (matId n) D.P) = matSub (matId n) D.P
  rw [matMul_sub_right, matMul_id_right, matMul_sub_left, matMul_id_left, D.P_idem]
  funext i j
  unfold matSub
  rw [sub_self, sub_zero]

theorem P_mul_Q (D : SimpleEigenvalueKatoData n F A0 lam0) :
    matMul D.P D.Q = matZero n := by
  unfold Q residualProj
  change matMul D.P (matSub (matId n) D.P) = matZero n
  rw [matMul_sub_right, matMul_id_right, D.P_idem]
  funext i j
  exact sub_self _

theorem Q_mul_P (D : SimpleEigenvalueKatoData n F A0 lam0) :
    matMul D.Q D.P = matZero n := by
  unfold Q residualProj
  change matMul (matSub (matId n) D.P) D.P = matZero n
  rw [matMul_sub_left, matMul_id_left, D.P_idem]
  funext i j
  exact sub_self _

theorem w0_dot_shifted (D : SimpleEigenvalueKatoData n F A0 lam0) (u : Vec n F) :
    vecDot D.w0 (matVec (matSub A0 (matSmul lam0 (matId n))) u) = 0 := by
  rw [sub_matVec, smul_matVec, matVec_id, vecDot_sub_right,
      vecDot_matVec, D.left_eig, vecDot_smul_right]
  unfold vecDot vecSmul
  have hassoc : (fun i => (lam0 * D.w0 i) * u i) = (fun i => lam0 * (D.w0 i * u i)) :=
    funext (fun i => lofMulAssoc lam0 (D.w0 i) (u i))
  rw [hassoc, ← finSum_mul_left]
  exact sub_self _

theorem w0_dot_Q (D : SimpleEigenvalueKatoData n F A0 lam0) (u : Vec n F) :
    vecDot D.w0 (matVec D.Q u) = 0 := by
  unfold Q residualProj
  change vecDot D.w0 (matVec (matSub (matId n) D.P) u) = 0
  rw [sub_matVec, matVec_id, D.P_matVec, vecDot_sub_right, vecDot_smul_right,
      div_mul_cancel _ D.pair_ne_zero, sub_self]

theorem Q_matVec_of_ortho (D : SimpleEigenvalueKatoData n F A0 lam0) {u : Vec n F}
    (hu : vecDot D.w0 u = 0) :
    matVec D.Q u = u := by
  unfold Q residualProj
  change matVec (matSub (matId n) D.P) u = u
  rw [sub_matVec, matVec_id, D.P_matVec, hu, zero_div]
  funext i
  unfold vecSub vecSmul
  rw [zero_mul, sub_zero]

theorem A0_mul_P (D : SimpleEigenvalueKatoData n F A0 lam0) :
    matMul A0 D.P = matSmul lam0 D.P := by
  funext i j
  unfold P eigenProj rankOneProj matMul matSmul
  have h1 : (fun k => A0 i k * ((D.v0 k * D.w0 j) / vecDot D.w0 D.v0)) =
      (fun k => (A0 i k * D.v0 k) * (D.w0 j / vecDot D.w0 D.v0)) := by
    funext k
    rw [lofDivEqMulInv, lofDivEqMulInv, lofMulAssoc (D.v0 k) _ _, lofMulAssoc (A0 i k) _ _]
  rw [h1, ← finSum_mul_right]
  have h2 : finSum n (fun k => A0 i k * D.v0 k) = lam0 * D.v0 i :=
    congrFun D.right_eig i
  dsimp only
  rw [h2, lofDivEqMulInv, lofDivEqMulInv, lofMulAssoc lam0 _ _, lofMulAssoc (D.v0 i) _ _]

theorem P_mul_A0 (D : SimpleEigenvalueKatoData n F A0 lam0) :
    matMul D.P A0 = matSmul lam0 D.P := by
  funext i j
  unfold P eigenProj rankOneProj matMul matSmul
  have h1 : (fun k => ((D.v0 i * D.w0 k) / vecDot D.w0 D.v0) * A0 k j) =
      (fun k => (D.v0 i / vecDot D.w0 D.v0) * (A0 k j * D.w0 k)) := by
    funext k
    rw [lofDivEqMulInv, lofDivEqMulInv]
    calc
      ((D.v0 i * D.w0 k) * (vecDot D.w0 D.v0)⁻¹) * A0 k j
        = (D.v0 i * (D.w0 k * (vecDot D.w0 D.v0)⁻¹)) * A0 k j := by
          rw [lofMulAssoc (D.v0 i) (D.w0 k) _]
      _ = (D.v0 i * ((vecDot D.w0 D.v0)⁻¹ * D.w0 k)) * A0 k j := by
        rw [lofMulComm (D.w0 k) _]
      _ = ((D.v0 i * (vecDot D.w0 D.v0)⁻¹) * D.w0 k) * A0 k j := by
        rw [← lofMulAssoc (D.v0 i) _ _]
      _ = (D.v0 i * (vecDot D.w0 D.v0)⁻¹) * (A0 k j * D.w0 k) := by
        rw [lofMulAssoc, lofMulComm (D.w0 k) (A0 k j)]
  rw [h1, ← finSum_mul_left]
  have h2 : finSum n (fun k => A0 k j * D.w0 k) = lam0 * D.w0 j :=
    congrFun D.left_eig j
  dsimp only
  rw [h2, lofDivEqMulInv, lofDivEqMulInv]
  calc
    (D.v0 i * (vecDot D.w0 D.v0)⁻¹) * (lam0 * D.w0 j)
      = ((D.v0 i * (vecDot D.w0 D.v0)⁻¹) * lam0) * D.w0 j := (lofMulAssoc _ _ _).symm
    _ = (lam0 * (D.v0 i * (vecDot D.w0 D.v0)⁻¹)) * D.w0 j := by rw [lofMulComm _ lam0]
    _ = lam0 * ((D.v0 i * D.w0 j) * (vecDot D.w0 D.v0)⁻¹) := by
      rw [lofMulAssoc lam0 _ _, lofMulAssoc (D.v0 i) _ _,
          lofMulComm (vecDot D.w0 D.v0)⁻¹ (D.w0 j), ← lofMulAssoc (D.v0 i) (D.w0 j) _]

/-- Uniqueness of the Kato reduced resolvent `S`. -/
theorem reducedResolvent_unique (D : SimpleEigenvalueKatoData n F A0 lam0)
    (S' : Mat n F)
    (h1 : matMul (matSub A0 (matSmul lam0 (matId n))) S' = D.Q)
    (h2 : matMul D.P S' = matZero n) :
    S' = D.S := by
  have hQS' : matMul D.Q S' = S' := by
    unfold Q residualProj
    change matMul (matSub (matId n) D.P) S' = S'
    rw [matMul_sub_left, matMul_id_left, h2]
    funext i j
    exact sub_zero _
  have hSQ : matMul D.S D.Q = D.S := by
    unfold Q residualProj
    change matMul D.S (matSub (matId n) D.P) = D.S
    rw [matMul_sub_right, matMul_id_right]
    unfold P
    rw [D.S_mul_P]
    funext i j
    exact sub_zero _
  calc
    S' = matMul D.Q S' := hQS'.symm
    _ = matMul (matMul D.S (matSub A0 (matSmul lam0 (matId n)))) S' := by
      unfold Q
      rw [D.S_mul_shifted]
    _ = matMul D.S (matMul (matSub A0 (matSmul lam0 (matId n))) S') := matMul_assoc _ _ _
    _ = matMul D.S D.Q := by rw [h1]
    _ = D.S := hSQ

/-! ### All-Orders Kato Perturbation Series Construction & Uniqueness -/

/-- History table for primitive-recursive construction of `(λ_k, v_k)` up to order `k`. -/
def katoHistory (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F) :
    Nat → (Nat → F × Vec n F)
  | 0 => fun _ => (lam0, D.v0)
  | k + 1 =>
    let prev := katoHistory D A1 k
    let vk := (prev k).2
    let lamNext := vecDot D.w0 (matVec A1 vk) / vecDot D.w0 D.v0
    let conv := vecSumRange 1 k (fun j => vecSmul (prev j).1 (matVec D.S (prev (k + 1 - j)).2))
    let vNext := vecAdd (vecNeg (matVec D.S (matVec A1 vk))) conv
    fun m => if m = k + 1 then (lamNext, vNext) else prev m

theorem katoHistory_stable (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F)
    {m k : Nat} (hmk : m ≤ k) :
    katoHistory D A1 k m = katoHistory D A1 m m := by
  induction k with
  | zero =>
    have hm0 : m = 0 := by omega
    rw [hm0]
  | succ r ih =>
    by_cases hmr : m = r + 1
    · rw [hmr]
    · have hle : m ≤ r := by omega
      conv => lhs; unfold katoHistory; dsimp only; rw [if_neg hmr]
      exact ih hle

/-- Exact `k`-th eigenvalue perturbation coefficient `λ_k`. -/
def katoLambda (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F) (k : Nat) : F :=
  (katoHistory D A1 k k).1

/-- Exact `k`-th normalized eigenvector perturbation coefficient `v_k`. -/
def katoVec (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F) (k : Nat) : Vec n F :=
  (katoHistory D A1 k k).2

theorem katoLambda_zero (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F) :
    D.katoLambda A1 0 = lam0 := rfl

theorem katoVec_zero (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F) :
    D.katoVec A1 0 = D.v0 := rfl

theorem katoLambda_succ (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F) (k : Nat) :
    D.katoLambda A1 (k + 1) = vecDot D.w0 (matVec A1 (D.katoVec A1 k)) / vecDot D.w0 D.v0 := by
  unfold katoLambda katoVec
  conv => lhs; unfold katoHistory; dsimp only; rw [if_pos rfl]

theorem katoVec_succ (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F) (k : Nat) :
    D.katoVec A1 (k + 1) =
      vecAdd (vecNeg (matVec D.S (matVec A1 (D.katoVec A1 k))))
        (vecSumRange 1 k (fun j =>
          vecSmul (D.katoLambda A1 j) (matVec D.S (D.katoVec A1 (k + 1 - j))))) := by
  unfold katoVec katoLambda
  conv => lhs; unfold katoHistory; dsimp only; rw [if_pos rfl]
  dsimp only
  apply congrArg (vecAdd _)
  apply vecSumRange_congr
  intro j hj1 hjk
  rw [katoHistory_stable D A1 (m := j) (k := k) (by omega),
      katoHistory_stable D A1 (m := k + 1 - j) (k := k) (by omega)]

/-- Normalization `w₀ᵀ v_k = 0` holds for every perturbation order `k ≥ 1`. -/
theorem katoVec_ortho (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F)
    {k : Nat} (hk : 1 ≤ k) :
    vecDot D.w0 (D.katoVec A1 k) = 0 := by
  have hwS : ∀ u : Vec n F, vecDot D.w0 (matVec D.S u) = 0 := by
    intro u
    have hP : matVec D.P (matVec D.S u) = vecZero n := by
      rw [matVec_matVec]
      unfold P
      rw [D.P_mul_S, zero_matVec]
    rw [D.P_matVec] at hP
    by_cases hdot : vecDot D.w0 (matVec D.S u) = 0
    · exact hdot
    · exfalso
      have hdiv : vecDot D.w0 (matVec D.S u) / vecDot D.w0 D.v0 ≠ 0 := by
        rw [lofDivEqMulInv]
        exact mul_ne_zero hdot (inv_ne_zero D.pair_ne_zero)
      have hv0_zero : D.v0 = vecZero n := by
        funext i
        have hi := congrFun hP i
        unfold vecSmul vecZero at hi
        rcases mul_eq_zero.mp hi with hc | hvi
        · exact False.elim (hdiv hc)
        · exact hvi
      have hpz : vecDot D.w0 D.v0 = 0 := by
        rw [hv0_zero, vecDot_zero_right]
      exact D.pair_ne_zero hpz
  cases k with
  | zero => omega
  | succ m =>
    rw [D.katoVec_succ A1 m, vecDot_add_right, ← matVec_neg, hwS, lofZeroAdd,
        vecDot_vecSumRange]
    have h0 : sumRange 1 m (fun j => vecDot D.w0 (vecSmul (D.katoLambda A1 j)
        (matVec D.S (D.katoVec A1 (m + 1 - j))))) = sumRange 1 m (fun _ => 0) := by
      apply sumRange_congr
      intro j _ _
      rw [vecDot_smul_right, hwS, mul_zero]
    rw [h0, sumRange_zero_fn]

theorem P_katoVec (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F)
    {k : Nat} (hk : 1 ≤ k) :
    matVec D.P (D.katoVec A1 k) = vecZero n := by
  rw [D.P_matVec, D.katoVec_ortho A1 hk, zero_div]
  funext i
  exact zero_mul _

theorem Q_katoVec (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F)
    {k : Nat} (hk : 1 ≤ k) :
    matVec D.Q (D.katoVec A1 k) = D.katoVec A1 k :=
  D.Q_matVec_of_ortho (D.katoVec_ortho A1 hk)

/-- **Theorem (All-Orders Kato Formal Power Series Eigenvalue Equation).**
    For every perturbation matrix `A₁` and every order `k ≥ 0`, `(λ_k, v_k)` satisfies
    the exact degree-`k` formal power series identity for `(A₀ + ε A₁) v(ε) = λ(ε) v(ε)`:
      `A₀ v_{k+1} + A₁ v_k = ∑_{j=0}^{k+1} λ_j v_{k+1-j}`. -/
theorem kato_power_series_eq (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F) (k : Nat) :
    vecAdd (matVec A0 (D.katoVec A1 (k + 1))) (matVec A1 (D.katoVec A1 k)) =
      vecSumRange 0 (k + 2) (fun j =>
        vecSmul (D.katoLambda A1 j) (D.katoVec A1 (k + 1 - j))) := by
  let B := matSub A0 (matSmul lam0 (matId n))
  have hBv : matVec B (D.katoVec A1 (k + 1)) =
      vecAdd (vecSub (vecSmul (D.katoLambda A1 (k + 1)) D.v0) (matVec A1 (D.katoVec A1 k)))
        (vecSumRange 1 k (fun j =>
          vecSmul (D.katoLambda A1 j) (D.katoVec A1 (k + 1 - j)))) := by
    rw [D.katoVec_succ A1 k, matVec_add, matVec_neg, matVec_matVec]
    unfold B
    rw [D.shifted_mul_S, matVec_vecSumRange]
    have hterm1 : vecNeg (matVec (residualProj D.v0 D.w0) (matVec A1 (D.katoVec A1 k))) =
        vecSub (vecSmul (D.katoLambda A1 (k + 1)) D.v0) (matVec A1 (D.katoVec A1 k)) := by
      unfold residualProj
      rw [sub_matVec, matVec_id]
      change vecNeg (vecSub (matVec A1 (D.katoVec A1 k)) (matVec D.P (matVec A1 (D.katoVec A1 k)))) = _
      rw [D.P_matVec, ← D.katoLambda_succ A1 k]
      funext i
      unfold vecNeg vecSub
      exact neg_sub _ _
    have hterm2 : vecSumRange 1 k (fun j =>
          matVec (matSub A0 (matSmul lam0 (matId n)))
            (vecSmul (D.katoLambda A1 j) (matVec D.S (D.katoVec A1 (k + 1 - j))))) =
        vecSumRange 1 k (fun j =>
          vecSmul (D.katoLambda A1 j) (D.katoVec A1 (k + 1 - j))) := by
      apply vecSumRange_congr
      intro j hj1 hjk
      rw [matVec_smul, matVec_matVec, D.shifted_mul_S]
      change vecSmul (D.katoLambda A1 j) (matVec D.Q (D.katoVec A1 (k + 1 - j))) = _
      rw [D.Q_katoVec A1 (by omega)]
    rw [hterm1, hterm2]
  funext i
  have hi := congrFun hBv i
  unfold B at hi
  rw [sub_matVec, smul_matVec, matVec_id] at hi
  unfold vecSub vecAdd vecSmul at hi
  rw [vecSumRange_eval]
  unfold vecAdd vecSmul
  rw [sumRange_head 0 (k + 1), sumRange_shift 0 (k + 1)]
  have hsplit : sumRange 0 (k + 1) (fun j => D.katoLambda A1 (j + 1) * D.katoVec A1 (k + 1 - (j + 1)) i) =
      sumRange 1 k (fun j => D.katoLambda A1 j * D.katoVec A1 (k + 1 - j) i) +
      D.katoLambda A1 (k + 1) * D.v0 i := by
    rw [sumRange_succ 0 k]
    congr 1
    · exact (sumRange_shift 0 k (fun j => D.katoLambda A1 j * D.katoVec A1 (k + 1 - j) i)).symm
    · have hsub : k + 1 - (0 + k + 1) = 0 := by omega
      have h0k : 0 + k + 1 = k + 1 := by omega
      rw [hsub, h0k, D.katoVec_zero]
  rw [hsplit]
  have hsub0 : k + 1 - 0 = k + 1 := by omega
  rw [hsub0, D.katoLambda_zero]
  rw [vecSumRange_eval] at hi
  have hi2 : matVec A0 (D.katoVec A1 (k + 1)) i + matVec A1 (D.katoVec A1 k) i =
      lam0 * D.katoVec A1 (k + 1) i +
      ((D.katoLambda A1 (k + 1) * D.v0 i - matVec A1 (D.katoVec A1 k) i) +
        sumRange 1 k (fun j => D.katoLambda A1 j * D.katoVec A1 (k + 1 - j) i)) +
      matVec A1 (D.katoVec A1 k) i := by
    have hadd := congrArg (fun x => x + lam0 * D.katoVec A1 (k + 1) i + matVec A1 (D.katoVec A1 k) i) hi
    dsimp only at hadd
    rw [sub_add_cancel] at hadd
    rw [hadd]
    rw [lofAddComm _ (lam0 * D.katoVec A1 (k + 1) i)]
  rw [hi2, lofAddAssoc]
  apply congrArg (fun x => lam0 * D.katoVec A1 (k + 1) i + x)
  calc
    ((D.katoLambda A1 (k + 1) * D.v0 i - matVec A1 (D.katoVec A1 k) i) +
        sumRange 1 k (fun j => D.katoLambda A1 j * D.katoVec A1 (k + 1 - j) i)) +
      matVec A1 (D.katoVec A1 k) i
      = sumRange 1 k (fun j => D.katoLambda A1 j * D.katoVec A1 (k + 1 - j) i) +
        ((D.katoLambda A1 (k + 1) * D.v0 i - matVec A1 (D.katoVec A1 k) i) +
          matVec A1 (D.katoVec A1 k) i) := by
        rw [lofAddComm (D.katoLambda A1 (k + 1) * D.v0 i - _) _, lofAddAssoc]
    _ = sumRange 1 k (fun j => D.katoLambda A1 j * D.katoVec A1 (k + 1 - j) i) +
        D.katoLambda A1 (k + 1) * D.v0 i := by
        rw [sub_add_cancel]

/-- **Theorem (Uniqueness of the Normalized Kato Formal Power Series).**
    Any sequence `(lamSeq, vecSeq)` with `(lamSeq 0, vecSeq 0) = (λ₀, v₀)`, `w₀ᵀ vecSeq k = 0`
    for `k ≥ 1`, and satisfying the formal power series eigenvalue equation at all orders
    coincides identically with `(katoLambda, katoVec)` at every order `k ≥ 0`. -/
theorem kato_power_series_unique (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F)
    (lamSeq : Nat → F) (vecSeq : Nat → Vec n F)
    (h0_lam : lamSeq 0 = lam0)
    (h0_vec : vecSeq 0 = D.v0)
    (hortho : ∀ k, 1 ≤ k → vecDot D.w0 (vecSeq k) = 0)
    (heq : ∀ k, vecAdd (matVec A0 (vecSeq (k + 1))) (matVec A1 (vecSeq k)) =
      vecSumRange 0 (k + 2) (fun j => vecSmul (lamSeq j) (vecSeq (k + 1 - j)))) :
    ∀ k, lamSeq k = D.katoLambda A1 k ∧ vecSeq k = D.katoVec A1 k := by
  have hstrong : ∀ K m, m ≤ K → lamSeq m = D.katoLambda A1 m ∧ vecSeq m = D.katoVec A1 m := by
    intro K
    induction K with
    | zero =>
      intro m hm
      have hm0 : m = 0 := by omega
      rw [hm0]
      exact ⟨h0_lam, h0_vec⟩
    | succ r ih =>
      intro m hm
      by_cases hmr : m ≤ r
      · exact ih m hmr
      · have hmeq : m = r + 1 := by omega
        rw [hmeq]
        have hstep := heq r
        -- Rewrite RHS of `hstep` into `lam0 • vecSeq(r+1) + middle + lamSeq(r+1) • v0`
        have hrhs : vecSumRange 0 (r + 2) (fun j => vecSmul (lamSeq j) (vecSeq (r + 1 - j))) =
            vecAdd (vecSmul lam0 (vecSeq (r + 1)))
              (vecAdd (vecSumRange 1 r (fun j =>
                  vecSmul (D.katoLambda A1 j) (D.katoVec A1 (r + 1 - j))))
                (vecSmul (lamSeq (r + 1)) D.v0)) := by
          funext i
          rw [vecSumRange_eval]
          unfold vecAdd vecSmul
          rw [vecSumRange_eval, sumRange_head 0 (r + 1), sumRange_shift 0 (r + 1),
              sumRange_succ 0 r, ← sumRange_shift 0 r
                (fun j => lamSeq j * vecSeq (r + 1 - j) i)]
          have hsub0 : r + 1 - 0 = r + 1 := by omega
          have hsubEnd : r + 1 - (0 + r + 1) = 0 := by omega
          have h0r : 0 + r + 1 = r + 1 := by omega
          rw [hsub0, h0_lam, hsubEnd, h0r, h0_vec]
          congr 1
          congr 1
          apply sumRange_congr
          intro j hj1 hjr
          rw [(ih j (by omega)).1, (ih (r + 1 - j) (by omega)).2]
        rw [hrhs, (ih r (by omega)).2] at hstep
        have hB : matVec (matSub A0 (matSmul lam0 (matId n))) (vecSeq (r + 1)) =
            vecSub
              (vecAdd (vecSumRange 1 r (fun j =>
                  vecSmul (D.katoLambda A1 j) (D.katoVec A1 (r + 1 - j))))
                (vecSmul (lamSeq (r + 1)) D.v0))
              (matVec A1 (D.katoVec A1 r)) := by
          funext i
          have hi := congrFun hstep i
          rw [sub_matVec, smul_matVec, matVec_id]
          unfold vecSub vecAdd vecSmul at hi ⊢
          have h1 : matVec A0 (vecSeq (r + 1)) i =
              (lam0 * vecSeq (r + 1) i +
                (vecSumRange 1 r (fun j => vecSmul (D.katoLambda A1 j) (D.katoVec A1 (r + 1 - j))) i +
                  lamSeq (r + 1) * D.v0 i)) - matVec A1 (D.katoVec A1 r) i := by
            have ha := congrArg (fun x => x - matVec A1 (D.katoVec A1 r) i) hi
            dsimp only at ha
            rw [add_sub_cancel] at ha
            exact ha
          rw [h1]
          calc
            ((lam0 * vecSeq (r + 1) i +
                (vecSumRange 1 r (fun j => vecSmul (D.katoLambda A1 j) (D.katoVec A1 (r + 1 - j))) i +
                  lamSeq (r + 1) * D.v0 i)) - matVec A1 (D.katoVec A1 r) i) - lam0 * vecSeq (r + 1) i
              = ((vecSumRange 1 r (fun j => vecSmul (D.katoLambda A1 j) (D.katoVec A1 (r + 1 - j))) i +
                  lamSeq (r + 1) * D.v0 i) + lam0 * vecSeq (r + 1) i) - lam0 * vecSeq (r + 1) i -
                matVec A1 (D.katoVec A1 r) i := by
                rw [lofAddComm (lam0 * vecSeq (r + 1) i) _, lofSubEqAddNeg, lofSubEqAddNeg,
                    lofSubEqAddNeg, lofAddAssoc, lofAddComm (-matVec A1 (D.katoVec A1 r) i) _,
                    ← lofAddAssoc, ← lofSubEqAddNeg _ (lam0 * vecSeq (r + 1) i)]
            _ = (vecSumRange 1 r (fun j => vecSmul (D.katoLambda A1 j) (D.katoVec A1 (r + 1 - j))) i +
                  lamSeq (r + 1) * D.v0 i) - matVec A1 (D.katoVec A1 r) i := by
                rw [add_sub_cancel]
        -- 1. Extract `lamSeq (r + 1) = D.katoLambda A1 (r + 1)` by dotting with `w₀`
        have hlam_eq : lamSeq (r + 1) = D.katoLambda A1 (r + 1) := by
          have hdot := congrArg (vecDot D.w0) hB
          rw [D.w0_dot_shifted, vecDot_sub_right, vecDot_add_right,
              vecDot_vecSumRange, vecDot_smul_right] at hdot
          have hsum0 : sumRange 1 r (fun j => vecDot D.w0
              (vecSmul (D.katoLambda A1 j) (D.katoVec A1 (r + 1 - j)))) = 0 := by
            have hc : sumRange 1 r (fun j => vecDot D.w0
                (vecSmul (D.katoLambda A1 j) (D.katoVec A1 (r + 1 - j)))) =
                sumRange 1 r (fun _ => 0) := by
              apply sumRange_congr
              intro j hj1 hjr
              rw [vecDot_smul_right, D.katoVec_ortho A1 (by omega), mul_zero]
            rw [hc, sumRange_zero_fn]
          rw [hsum0, lofZeroAdd] at hdot
          have heq_mul : lamSeq (r + 1) * vecDot D.w0 D.v0 =
              vecDot D.w0 (matVec A1 (D.katoVec A1 r)) :=
            sub_eq_zero.mp hdot.symm
          rw [D.katoLambda_succ A1 r]
          exact ((div_eq_iff D.pair_ne_zero).mpr heq_mul.symm).symm
        -- 2. Extract `vecSeq (r + 1) = D.katoVec A1 (r + 1)` by applying `S`
        have hvec_eq : vecSeq (r + 1) = D.katoVec A1 (r + 1) := by
          have hS := congrArg (matVec D.S) hB
          rw [matVec_matVec, D.S_mul_shifted] at hS
          change matVec D.Q (vecSeq (r + 1)) = _ at hS
          rw [D.Q_matVec_of_ortho (hortho (r + 1) (by omega)),
              matVec_sub, matVec_add, matVec_smul, D.S_v0,
              matVec_vecSumRange] at hS
          have hsv0 : vecSmul (lamSeq (r + 1)) (vecZero n) = vecZero n :=
            funext (fun _ => mul_zero _)
          rw [hsv0, vecAdd_zero] at hS
          rw [hS, D.katoVec_succ A1 r]
          funext i
          unfold vecSub vecAdd vecNeg
          rw [lofSubEqAddNeg, lofAddComm]
          congr 1
          rw [vecSumRange_eval, vecSumRange_eval]
          apply sumRange_congr
          intro j _ _
          rw [matVec_smul]
        exact ⟨hlam_eq, hvec_eq⟩
  intro k
  exact hstrong k k (Nat.le_refl k)

/-! ### Closed-Form First- and Second-Order Kato Perturbation Formulas -/

/-- **Kato First-Order Eigenvalue Formula:**
    `λ₁ = (w₀ᵀ A₁ v₀)/(w₀ᵀ v₀) = tr(P A₁) = tr(P A₁ P)` (governed by the eigenprojection `P`). -/
theorem kato_first_order_eigenvalue (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F) :
    D.katoLambda A1 1 = vecDot D.w0 (matVec A1 D.v0) / vecDot D.w0 D.v0 ∧
    D.katoLambda A1 1 = matTrace (matMul D.P A1) ∧
    D.katoLambda A1 1 = matTrace (matMul (matMul D.P A1) D.P) := by
  have h1 : D.katoLambda A1 1 = vecDot D.w0 (matVec A1 D.v0) / vecDot D.w0 D.v0 := by
    rw [D.katoLambda_succ A1 0, D.katoVec_zero]
  have h2 : matTrace (matMul D.P A1) = vecDot D.w0 (matVec A1 D.v0) / vecDot D.w0 D.v0 := by
    unfold P eigenProj
    exact matTrace_rankOneProj_mul D.v0 D.w0 (vecDot D.w0 D.v0) A1
  have h3 : matTrace (matMul (matMul D.P A1) D.P) = matTrace (matMul D.P A1) := by
    rw [matTrace_comm (matMul D.P A1) D.P, ← matMul_assoc, D.P_idem]
  exact ⟨h1, h1.trans h2.symm, (h1.trans h2.symm).trans h3.symm⟩

/-- **Kato First-Order Eigenvector Formula:**
    `v₁ = - S A₁ v₀` (governed by the reduced resolvent `S`). -/
theorem kato_first_order_eigenvector (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F) :
    D.katoVec A1 1 = vecNeg (matVec D.S (matVec A1 D.v0)) := by
  rw [D.katoVec_succ A1 0, D.katoVec_zero]
  unfold vecSumRange
  exact vecAdd_zero _

/-- **Kato Second-Order Eigenvalue Formula:**
    `λ₂ = - (w₀ᵀ A₁ S A₁ v₀)/(w₀ᵀ v₀) = - tr(P A₁ S A₁)` (governed by `P` and `S`). -/
theorem kato_second_order_eigenvalue (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F) :
    D.katoLambda A1 2 =
      - (vecDot D.w0 (matVec A1 (matVec D.S (matVec A1 D.v0))) / vecDot D.w0 D.v0) ∧
    D.katoLambda A1 2 = - matTrace (matMul (matMul (matMul D.P A1) D.S) A1) := by
  have h1 : D.katoLambda A1 2 =
      - (vecDot D.w0 (matVec A1 (matVec D.S (matVec A1 D.v0))) / vecDot D.w0 D.v0) := by
    rw [D.katoLambda_succ A1 1, D.kato_first_order_eigenvector A1, matVec_neg]
    have hneg : vecDot D.w0 (vecNeg (matVec A1 (matVec D.S (matVec A1 D.v0)))) =
        - vecDot D.w0 (matVec A1 (matVec D.S (matVec A1 D.v0))) := by
      unfold vecDot vecNeg
      have hf : (fun i => D.w0 i * - matVec A1 (matVec D.S (matVec A1 D.v0)) i) =
          (fun i => - (D.w0 i * matVec A1 (matVec D.S (matVec A1 D.v0)) i)) :=
        funext (fun i => mul_neg _ _)
      rw [hf, finSum_neg]
    rw [hneg, neg_div]
  have h2 : matTrace (matMul (matMul (matMul D.P A1) D.S) A1) =
      vecDot D.w0 (matVec A1 (matVec D.S (matVec A1 D.v0))) / vecDot D.w0 D.v0 := by
    rw [matMul_assoc D.P A1 D.S, matMul_assoc D.P (matMul A1 D.S) A1]
    unfold P eigenProj
    rw [matTrace_rankOneProj_mul, ← matVec_matVec, ← matVec_matVec]
  exact ⟨h1, h1.trans (congrArg Neg.neg h2.symm)⟩

/-- First-order Kato eigenprojection perturbation `P₁ = - P A₁ S - S A₁ P`. -/
def katoProjFirstOrder (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F) : Mat n F :=
  matNeg (matAdd (matMul (matMul D.P A1) D.S) (matMul (matMul D.S A1) D.P))

/-- `P₁ = - P A₁ S - S A₁ P` satisfies the linearized idempotence `P P₁ + P₁ P = P₁`
    and linearized spectral commutation `A₀ P₁ + A₁ P = P A₁ + P₁ A₀`. -/
theorem katoProjFirstOrder_properties (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F) :
    let P1 := D.katoProjFirstOrder A1
    matAdd (matMul D.P P1) (matMul P1 D.P) = P1 ∧
    matAdd (matMul A0 P1) (matMul A1 D.P) = matAdd (matMul D.P A1) (matMul P1 A0) := by
  intro P1
  have hnegMulL : ∀ X Y : Mat n F, matMul X (matNeg Y) = matNeg (matMul X Y) := by
    intro X Y
    funext i j
    unfold matMul matNeg
    have hf : (fun k => X i k * - Y k j) = (fun k => - (X i k * Y k j)) :=
      funext (fun _ => mul_neg _ _)
    rw [hf, finSum_neg]
  have hnegMulR : ∀ X Y : Mat n F, matMul (matNeg X) Y = matNeg (matMul X Y) := by
    intro X Y
    funext i j
    unfold matMul matNeg
    have hf : (fun k => - X i k * Y k j) = (fun k => - (X i k * Y k j)) :=
      funext (fun _ => neg_mul _ _)
    rw [hf, finSum_neg]
  have hPP1 : matMul D.P P1 = matNeg (matMul (matMul D.P A1) D.S) := by
    unfold P1 katoProjFirstOrder
    rw [hnegMulL, matMul_add_right,
        ← matMul_assoc D.P (matMul D.P A1) D.S, ← matMul_assoc D.P D.P A1, D.P_idem,
        ← matMul_assoc D.P (matMul D.S A1) D.P, ← matMul_assoc D.P D.S A1]
    have hPS : matMul D.P D.S = matZero n := D.P_mul_S
    rw [hPS, matMul_zero_left, matMul_zero_left]
    funext i j
    unfold matNeg matAdd matZero
    rw [lofAddZero]
  have hP1P : matMul P1 D.P = matNeg (matMul (matMul D.S A1) D.P) := by
    unfold P1 katoProjFirstOrder
    rw [hnegMulR, matMul_add_left, matMul_assoc (matMul D.P A1) D.S D.P,
        matMul_assoc (matMul D.S A1) D.P D.P, D.P_idem]
    have hSP : matMul D.S D.P = matZero n := D.S_mul_P
    rw [hSP, matMul_zero_right]
    funext i j
    unfold matNeg matAdd matZero
    rw [lofZeroAdd]
  refine ⟨?_, ?_⟩
  · rw [hPP1, hP1P]
    funext i j
    unfold P1 katoProjFirstOrder matAdd matNeg
    exact (neg_add_rev _ _).symm
  · let B := matSub A0 (matSmul lam0 (matId n))
    have hBP1_sub : matSub (matMul B P1) (matMul P1 B) =
        matSub (matMul D.P A1) (matMul A1 D.P) := by
      have hBP : matMul B D.P = matZero n := by
        unfold B
        rw [matMul_sub_left, matMul_smul_left, matMul_id_left, D.A0_mul_P]
        funext i j
        exact sub_self _
      have hPB : matMul D.P B = matZero n := by
        unfold B
        rw [matMul_sub_right, matMul_smul_right, matMul_id_right, D.P_mul_A0]
        funext i j
        exact sub_self _
      have hBP1 : matMul B P1 = matNeg (matMul (matMul D.Q A1) D.P) := by
        unfold P1 katoProjFirstOrder
        rw [hnegMulL, matMul_add_right, ← matMul_assoc B (matMul D.P A1) D.S,
            ← matMul_assoc B D.P A1, hBP, matMul_zero_left, matMul_zero_left,
            ← matMul_assoc B (matMul D.S A1) D.P, ← matMul_assoc B D.S A1]
        have hBS : matMul B D.S = D.Q := D.shifted_mul_S
        rw [hBS]
        funext i j
        unfold matNeg matAdd matZero
        rw [lofZeroAdd]
      have hP1B : matMul P1 B = matNeg (matMul (matMul D.P A1) D.Q) := by
        unfold P1 katoProjFirstOrder
        rw [hnegMulR, matMul_add_left, matMul_assoc (matMul D.P A1) D.S B,
            matMul_assoc (matMul D.S A1) D.P B, hPB, matMul_zero_right]
        have hSB : matMul D.S B = D.Q := D.S_mul_shifted
        rw [hSB]
        funext i j
        unfold matNeg matAdd matZero
        rw [lofAddZero]
      rw [hBP1, hP1B]
      unfold Q residualProj
      change matSub (matNeg (matMul (matMul (matSub (matId n) D.P) A1) D.P))
          (matNeg (matMul (matMul D.P A1) (matSub (matId n) D.P))) = _
      rw [matMul_sub_left (matId n) D.P A1, matMul_id_left,
          matMul_sub_left A1 (matMul D.P A1) D.P,
          matMul_sub_right (matMul D.P A1) (matId n) D.P, matMul_id_right]
      funext i j
      unfold matSub matNeg
      let x := matMul A1 D.P i j
      let y := matMul D.P A1 i j
      let z := matMul (matMul D.P A1) D.P i j
      change - (x - z) - - (y - z) = y - x
      rw [neg_sub, neg_sub, lofSubEqAddNeg (z - x) (z - y), neg_sub]
      calc
        (z - x) + (y - z) = y + (-z + (z - x)) := by
          rw [lofAddComm (z - x) (y - z), lofSubEqAddNeg y z, lofAddAssoc]
        _ = y + ((-z + z) + -x) := by
          rw [lofSubEqAddNeg z x, ← lofAddAssoc (-z) z (-x)]
        _ = y - x := by
          rw [lofNegAddCancel, lofZeroAdd, ← lofSubEqAddNeg]
    have hexpand : matSub (matMul B P1) (matMul P1 B) =
        matSub (matMul A0 P1) (matMul P1 A0) := by
      unfold B
      rw [matMul_sub_left, matMul_smul_left, matMul_id_left,
          matMul_sub_right, matMul_smul_right, matMul_id_right]
      funext i j
      unfold matSub matSmul
      let u := matMul A0 P1 i j
      let v := matMul P1 A0 i j
      let w := lam0 * P1 i j
      change (u - w) - (v - w) = u - v
      rw [lofSubEqAddNeg (u - w) (v - w), neg_sub]
      calc
        (u - w) + (w - v) = u + (-w + (w - v)) := by
          rw [lofSubEqAddNeg u w, lofAddAssoc]
        _ = u + ((-w + w) + -v) := by
          rw [lofSubEqAddNeg w v, ← lofAddAssoc (-w) w (-v)]
        _ = u - v := by
          rw [lofNegAddCancel, lofZeroAdd, ← lofSubEqAddNeg]
    rw [hexpand] at hBP1_sub
    funext i j
    have hij := congrFun (congrFun hBP1_sub i) j
    unfold matSub at hij
    unfold matAdd
    let u := matMul A0 P1 i j
    let v := matMul P1 A0 i j
    let x := matMul A1 D.P i j
    let y := matMul D.P A1 i j
    change u - v = y - x at hij
    change u + x = y + v
    have h1 := congrArg (fun t => t + v + x) hij
    dsimp only at h1
    rw [sub_add_cancel] at h1
    rw [h1]
    calc
      (y - x + v) + x = y + (-x + x) + v := by
        rw [lofSubEqAddNeg y x, lofAddAssoc (y + -x) v x, lofAddComm v x,
            ← lofAddAssoc (y + -x) x v, lofAddAssoc y (-x) x]
      _ = y + v := by rw [lofNegAddCancel, lofAddZero]

/-! ### Explicit Cauchy-Kato Analytic Convergence Majorant & Tail Rate -/

/-- Natural-number square `(natCastF m)²` in `F`. -/
def sqNatF (m : Nat) : F := natCastF m * natCastF m

theorem sqNatF_pos {m : Nat} (hm : 1 ≤ m) : (0 : F) < sqNatF m := by
  unfold sqNatF
  have hp : (0 : F) < natCastF m := natCastF_pos_of_pos (by omega)
  exact LinearOrderedField.mul_pos hp hp

theorem sqNatF_ne_zero {m : Nat} (hm : 1 ≤ m) : (sqNatF m : F) ≠ 0 :=
  ne_of_gt (sqNatF_pos hm)

theorem inv_sqNatF_succ_le_diff (m : Nat) (hm : 1 ≤ m) :
    (sqNatF (m + 1) : F)⁻¹ ≤ (natCastF m : F)⁻¹ - (natCastF (m + 1) : F)⁻¹ := by
  let a : F := natCastF m
  let b : F := natCastF (m + 1)
  have ha : 0 < a := natCastF_pos_of_pos (by omega)
  have hb : 0 < b := natCastF_pos_of_pos (by omega)
  have hab_le : a ≤ b := natCastF_le_of_le (by omega)
  have hab_pos : 0 < a * b := LinearOrderedField.mul_pos ha hb
  have hprod_le : a * b ≤ b * b := mul_le_mul_of_nonneg_right hab_le (le_of_lt hb)
  have hinv_le : (b * b)⁻¹ ≤ (a * b)⁻¹ := inv_le_inv_of_pos hab_pos hprod_le
  have hdiff : (a * b)⁻¹ = a⁻¹ - b⁻¹ := by
    have hb_sub_a : b - a = 1 := by
      unfold b a
      rw [natCastF_succ, lofAddComm, add_sub_cancel]
    calc
      (a * b)⁻¹ = 1 * (a⁻¹ * b⁻¹) := by
        rw [inv_mul_distrib (ne_of_gt ha) (ne_of_gt hb), lofOneMul]
      _ = (b - a) * (a⁻¹ * b⁻¹) := by rw [hb_sub_a]
      _ = b * (a⁻¹ * b⁻¹) - a * (a⁻¹ * b⁻¹) := sub_mul b a _
      _ = a⁻¹ - b⁻¹ := by
        congr 1
        · rw [lofMulComm a⁻¹ b⁻¹, ← lofMulAssoc b b⁻¹ a⁻¹,
              lofMulInvCancel (ne_of_gt hb), lofOneMul]
        · rw [← lofMulAssoc a a⁻¹ b⁻¹, lofMulInvCancel (ne_of_gt ha), lofOneMul]
  rw [← hdiff]
  exact hinv_le

theorem sumRange_inv_sqNatF_le_two (k : Nat) :
    sumRange 1 k (fun j => (sqNatF j : F)⁻¹) ≤ twoF := by
  cases k with
  | zero =>
    rw [sumRange_zero]
    exact le_of_lt twoF_pos
  | succ m =>
    have htel : sumRange 1 (m + 1) (fun j => (sqNatF j : F)⁻¹) ≤
        twoF - (natCastF (m + 1) : F)⁻¹ := by
      induction m with
      | zero =>
        rw [sumRange_succ, sumRange_zero, lofZeroAdd]
        have h1 : (sqNatF 1 : F)⁻¹ = 1 := by
          unfold sqNatF
          rw [natCastF_one, lofOneMul, inv_one]
        have h2 : (twoF : F) - (natCastF 1 : F)⁻¹ = 1 := by
          unfold twoF
          rw [natCastF_one, inv_one, add_sub_cancel]
        rw [h1, h2]
        exact LinearOrderedField.le_refl 1
      | succ r ih =>
        rw [sumRange_succ]
        have he : 1 + (r + 1) = (r + 1) + 1 := by omega
        rw [he]
        have hstep := inv_sqNatF_succ_le_diff (F := F) (r + 1) (by omega)
        have hsum := add_le_add ih hstep
        have hrhs : (twoF - (natCastF (r + 1) : F)⁻¹) +
            ((natCastF (r + 1) : F)⁻¹ - (natCastF (r + 1 + 1) : F)⁻¹) =
            twoF - (natCastF (r + 1 + 1) : F)⁻¹ := by
          let x := (natCastF (r + 1) : F)⁻¹
          let y := (natCastF (r + 1 + 1) : F)⁻¹
          change (twoF - x) + (x - y) = twoF - y
          calc
            (twoF - x) + (x - y) = twoF + (-x + (x + -y)) := by
              rw [lofSubEqAddNeg, lofSubEqAddNeg, lofAddAssoc]
            _ = twoF + ((-x + x) + -y) := by rw [← lofAddAssoc (-x) x (-y)]
            _ = twoF - y := by rw [lofNegAddCancel, lofZeroAdd, ← lofSubEqAddNeg]
        rw [hrhs] at hsum
        exact hsum
    have hpos : (0 : F) ≤ (natCastF (m + 1) : F)⁻¹ :=
      inv_nonneg_of_nonneg (natCastF_nonneg (m + 1))
    have hsub_le : (twoF : F) - (natCastF (m + 1) : F)⁻¹ ≤ twoF := by
      have h2 := LinearOrderedField.add_le_add_left (neg_le_neg hpos) twoF
      rw [neg_zero, lofAddZero, ← lofSubEqAddNeg] at h2
      exact h2
    exact LinearOrderedField.le_trans htel hsub_le

theorem inv_sqNatF_le_four_succ (k : Nat) (hk : 1 ≤ k) :
    (sqNatF k : F)⁻¹ ≤ fourF * (sqNatF (k + 1) : F)⁻¹ := by
  have hk_le : natCastF (k + 1) ≤ (twoF : F) * natCastF k := by
    rw [twoF_mul, natCastF_succ, ← natCastF_one]
    exact LinearOrderedField.add_le_add_left (natCastF_le_of_le (F := F) hk) (natCastF k)
  have h0 : (0 : F) ≤ natCastF (k + 1) := natCastF_nonneg (k + 1)
  have hsq : sqNatF (k + 1) ≤ (fourF : F) * sqNatF k := by
    have hm := mul_le_mul hk_le hk_le h0
      (mul_nonneg (le_of_lt twoF_pos) (natCastF_nonneg k))
    have hr : ((twoF : F) * natCastF k) * ((twoF : F) * natCastF k) =
        (fourF : F) * sqNatF k := by
      unfold sqNatF
      rw [fourF_eq_two_mul_two]
      calc
        (twoF * natCastF k) * (twoF * natCastF k)
          = twoF * (natCastF k * (twoF * natCastF k)) := lofMulAssoc _ _ _
        _ = twoF * (twoF * (natCastF k * natCastF k)) := by
          rw [← lofMulAssoc (natCastF k) twoF _, lofMulComm (natCastF k) twoF, lofMulAssoc]
        _ = (twoF * twoF) * (natCastF k * natCastF k) := (lofMulAssoc _ _ _).symm
    rw [hr] at hm
    exact hm
  have hinv := inv_le_inv_of_pos (sqNatF_pos (F := F) (by omega)) hsq
  have hm2 := mul_le_mul_of_nonneg_left hinv (le_of_lt (fourF_pos (F := F)))
  rw [inv_mul_distrib (fourF_ne_zero (F := F)) (sqNatF_ne_zero hk),
      ← lofMulAssoc, lofMulInvCancel fourF_ne_zero, lofOneMul] at hm2
  exact hm2

theorem sq_sum_le_two_add_sq (u v : F) :
    (u + v) * (u + v) ≤ (twoF : F) * (u * u + v * v) := by
  have h2ab := two_mul_le_sq_add_sq u v
  have hexp1 : (u + v) * (u + v) = (u * u + v * v) + (twoF : F) * (u * v) := by
    rw [lofRightDistrib, lofLeftDistrib, lofLeftDistrib, lofMulComm v u, twoF_mul]
    rw [lofAddAssoc (u * u) (u * v) (u * v + v * v)]
    rw [← lofAddAssoc (u * v) (u * v) (v * v)]
    rw [lofAddComm (u * v + u * v) (v * v)]
    rw [← lofAddAssoc (u * u) (v * v) _]
  rw [hexp1, twoF_mul (u * u + v * v)]
  exact LinearOrderedField.add_le_add_left h2ab (u * u + v * v)

theorem conv_inv_sqNatF_le_eight (k : Nat) :
    sumRange 1 k (fun j => (sqNatF j : F)⁻¹ * (sqNatF (k + 1 - j) : F)⁻¹) ≤
      eightF * (sqNatF (k + 1) : F)⁻¹ := by
  have hterm : ∀ j, 1 ≤ j → j < 1 + k →
      (sqNatF j : F)⁻¹ * (sqNatF (k + 1 - j) : F)⁻¹ ≤
        ((twoF : F) * (sqNatF (k + 1) : F)⁻¹) *
          ((sqNatF j : F)⁻¹ + (sqNatF (k + 1 - j) : F)⁻¹) := by
    intro j hj1 hjk
    let a : F := natCastF j
    let b : F := natCastF (k + 1 - j)
    let s : F := natCastF (k + 1)
    have ha : a ≠ 0 := ne_of_gt (natCastF_pos_of_pos (by omega))
    have hb : b ≠ 0 := ne_of_gt (natCastF_pos_of_pos (by omega))
    have hs : s ≠ 0 := ne_of_gt (natCastF_pos_of_pos (by omega))
    have hab_eq : a + b = s := by
      unfold a b s
      rw [← natCastF_add]
      have hn : j + (k + 1 - j) = k + 1 := by omega
      rw [hn]
    have huv : a⁻¹ * b⁻¹ = s⁻¹ * (a⁻¹ + b⁻¹) := by
      have h1 : s * (a⁻¹ * b⁻¹) = b⁻¹ + a⁻¹ := by
        rw [← hab_eq, lofRightDistrib]
        congr 1
        · rw [← lofMulAssoc a a⁻¹ b⁻¹, lofMulInvCancel ha, lofOneMul]
        · rw [lofMulComm a⁻¹ b⁻¹, ← lofMulAssoc b b⁻¹ a⁻¹, lofMulInvCancel hb, lofOneMul]
      rw [lofAddComm b⁻¹ a⁻¹] at h1
      rw [← h1, ← lofMulAssoc, inv_mul_cancel hs, lofOneMul]
    have hsq_lhs : (sqNatF j : F)⁻¹ * (sqNatF (k + 1 - j) : F)⁻¹ =
        (a⁻¹ * b⁻¹) * (a⁻¹ * b⁻¹) := by
      unfold sqNatF
      change (a * a)⁻¹ * (b * b)⁻¹ = (a⁻¹ * b⁻¹) * (a⁻¹ * b⁻¹)
      rw [inv_mul_distrib ha ha, inv_mul_distrib hb hb]
      calc
        (a⁻¹ * a⁻¹) * (b⁻¹ * b⁻¹) = a⁻¹ * (a⁻¹ * (b⁻¹ * b⁻¹)) := lofMulAssoc _ _ _
        _ = a⁻¹ * (b⁻¹ * (a⁻¹ * b⁻¹)) := by
          congr 1
          conv => lhs; rw [← lofMulAssoc a⁻¹ b⁻¹ b⁻¹, lofMulComm a⁻¹ b⁻¹, lofMulAssoc b⁻¹ a⁻¹ b⁻¹]
        _ = (a⁻¹ * b⁻¹) * (a⁻¹ * b⁻¹) := (lofMulAssoc _ _ _).symm
    have hs2 : (sqNatF (k + 1) : F)⁻¹ = s⁻¹ * s⁻¹ := by
      unfold sqNatF
      exact inv_mul_distrib hs hs
    rw [hsq_lhs, huv, hs2]
    have hmid : (s⁻¹ * (a⁻¹ + b⁻¹)) * (s⁻¹ * (a⁻¹ + b⁻¹)) =
        (s⁻¹ * s⁻¹) * ((a⁻¹ + b⁻¹) * (a⁻¹ + b⁻¹)) := by
      calc
        (s⁻¹ * (a⁻¹ + b⁻¹)) * (s⁻¹ * (a⁻¹ + b⁻¹))
          = s⁻¹ * ((a⁻¹ + b⁻¹) * (s⁻¹ * (a⁻¹ + b⁻¹))) := lofMulAssoc _ _ _
        _ = s⁻¹ * (s⁻¹ * ((a⁻¹ + b⁻¹) * (a⁻¹ + b⁻¹))) := by
          rw [← lofMulAssoc (a⁻¹ + b⁻¹) s⁻¹ _, lofMulComm (a⁻¹ + b⁻¹) s⁻¹, lofMulAssoc]
        _ = (s⁻¹ * s⁻¹) * ((a⁻¹ + b⁻¹) * (a⁻¹ + b⁻¹)) := (lofMulAssoc _ _ _).symm
    rw [hmid]
    have hcs := sq_sum_le_two_add_sq a⁻¹ b⁻¹
    have hs2_nn : 0 ≤ s⁻¹ * s⁻¹ := sq_nonneg s⁻¹
    have hm := mul_le_mul_of_nonneg_left hcs hs2_nn
    have hr : (s⁻¹ * s⁻¹) * ((twoF : F) * (a⁻¹ * a⁻¹ + b⁻¹ * b⁻¹)) =
        ((twoF : F) * (s⁻¹ * s⁻¹)) * ((sqNatF j : F)⁻¹ + (sqNatF (k + 1 - j) : F)⁻¹) := by
      unfold sqNatF
      change (s⁻¹ * s⁻¹) * (twoF * (a⁻¹ * a⁻¹ + b⁻¹ * b⁻¹)) =
        (twoF * (s⁻¹ * s⁻¹)) * ((a * a)⁻¹ + (b * b)⁻¹)
      rw [inv_mul_distrib ha ha, inv_mul_distrib hb hb,
          ← lofMulAssoc (s⁻¹ * s⁻¹) twoF _, lofMulComm (s⁻¹ * s⁻¹) twoF]
    rw [hr] at hm
    exact hm
  have hsum1 := sumRange_le_sumRange 1 k hterm
  rw [← sumRange_mul_left, sumRange_add,
      sumRange_one_reflect k (fun j => (sqNatF j : F)⁻¹), ← twoF_mul] at hsum1
  have hc_nn : 0 ≤ (twoF : F) * (sqNatF (k + 1) : F)⁻¹ :=
    mul_nonneg (le_of_lt twoF_pos)
      (inv_nonneg_of_nonneg (le_of_lt (sqNatF_pos (by omega))))
  have hbnd : (twoF : F) * sumRange 1 k (fun j => (sqNatF j : F)⁻¹) ≤ fourF := by
    rw [fourF_eq_two_mul_two]
    exact mul_le_mul_of_nonneg_left (sumRange_inv_sqNatF_le_two k) (le_of_lt twoF_pos)
  have hsum2 := mul_le_mul_of_nonneg_left hbnd hc_nn
  have hr8 : ((twoF : F) * (sqNatF (k + 1) : F)⁻¹) * fourF =
      eightF * (sqNatF (k + 1) : F)⁻¹ := by
    rw [lofMulAssoc, lofMulComm _ fourF, ← lofMulAssoc, lofMulComm twoF fourF]
    have h24 : (fourF : F) * twoF = eightF := by
      rw [lofMulComm, eightF_eq_two_mul_four]
    rw [h24]
  rw [hr8] at hsum2
  exact LinearOrderedField.le_trans hsum1 hsum2

/-- Explicit Kato majorant constants `(α, β, σ, ρ, R₀)` for `(D, A₁)`. -/
noncomputable def katoAlpha (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F) : F :=
  (vecNorm1 D.w0 / absF (vecDot D.w0 D.v0)) * matNormSum A1

noncomputable def katoBeta (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F) : F :=
  matNormSum (matMul D.S A1)

noncomputable def katoSigma (D : SimpleEigenvalueKatoData n F A0 lam0) : F :=
  matNormSum D.S

noncomputable def katoRho (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F) : F :=
  fourF * D.katoBeta A1 + eightF * (D.katoAlpha A1 * D.katoSigma * vecNorm1 D.v0) + 1

noncomputable def katoRadius (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F) : F :=
  (D.katoRho A1)⁻¹

theorem katoAlpha_nonneg (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F) :
    0 ≤ D.katoAlpha A1 := by
  unfold katoAlpha
  exact mul_nonneg
    (div_nonneg (vecNorm1_nonneg D.w0) (le_of_lt (absF_pos_of_ne_zero D.pair_ne_zero)))
    (matNormSum_nonneg A1)

theorem katoRho_pos (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F) :
    0 < D.katoRho A1 := by
  unfold katoRho
  have h1 : 0 ≤ fourF * D.katoBeta A1 :=
    mul_nonneg (le_of_lt fourF_pos) (matNormSum_nonneg _)
  have h2 : 0 ≤ eightF * (D.katoAlpha A1 * D.katoSigma * vecNorm1 D.v0) :=
    mul_nonneg (le_of_lt eightF_pos)
      (mul_nonneg (mul_nonneg (D.katoAlpha_nonneg A1) (matNormSum_nonneg D.S))
        (vecNorm1_nonneg D.v0))
  have h12 : 0 ≤ fourF * D.katoBeta A1 + eightF * (D.katoAlpha A1 * D.katoSigma * vecNorm1 D.v0) := by
    have h := add_le_add h1 h2
    rw [lofAddZero] at h
    exact h
  have hp := add_lt_add_of_lt_of_le (LinearOrderedField.zero_lt_one (F := F)) h12
  rw [lofAddZero, lofAddComm] at hp
  exact hp

theorem katoRadius_pos (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F) :
    0 < D.katoRadius A1 :=
  inv_pos_of_pos (D.katoRho_pos A1)

theorem absF_katoLambda_succ_le (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F) (k : Nat) :
    absF (D.katoLambda A1 (k + 1)) ≤ D.katoAlpha A1 * vecNorm1 (D.katoVec A1 k) := by
  rw [D.katoLambda_succ A1 k, absF_div]
  have hd_pos : 0 < absF (vecDot D.w0 D.v0) := absF_pos_of_ne_zero D.pair_ne_zero
  have hdot : absF (vecDot D.w0 (matVec A1 (D.katoVec A1 k))) ≤
      (vecNorm1 D.w0 * matNormSum A1) * vecNorm1 (D.katoVec A1 k) := by
    have h1 := absF_vecDot_le D.w0 (matVec A1 (D.katoVec A1 k))
    have h2 := mul_le_mul_of_nonneg_left (vecNorm1_matVec_le A1 (D.katoVec A1 k))
      (vecNorm1_nonneg D.w0)
    rw [← lofMulAssoc] at h2
    exact LinearOrderedField.le_trans h1 h2
  have hdiv := div_le_div_of_nonneg_right hdot (le_of_lt hd_pos)
  unfold katoAlpha
  have hr : ((vecNorm1 D.w0 * matNormSum A1) * vecNorm1 (D.katoVec A1 k)) /
      absF (vecDot D.w0 D.v0) =
      ((vecNorm1 D.w0 / absF (vecDot D.w0 D.v0)) * matNormSum A1) *
        vecNorm1 (D.katoVec A1 k) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  rw [hr] at hdiv
  exact hdiv

/-- **Theorem (Cauchy-Kato Analytic Convergence Majorant Bound).**
    Around every algebraically simple eigenvalue `λ₀` of `A₀`, there exists an explicit
    positive analytic convergence radius `R₀ = (katoRho D A₁)⁻¹ > 0` such that for all `k ≥ 0`:
      `‖v_k‖₁ ≤ ‖v₀‖₁ · (k + 1)⁻² · ρ^k`,
    and for all `k ≥ 1`:
      `|λ_k| ≤ α ‖v₀‖₁ · k⁻² · ρ^(k-1)`. -/
theorem kato_analytic_majorant_bound (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F) :
    0 < D.katoRadius A1 ∧
    (∀ k : Nat,
      vecNorm1 (D.katoVec A1 k) ≤
        (vecNorm1 D.v0 * (sqNatF (k + 1) : F)⁻¹) * powF (D.katoRho A1) k) ∧
    (∀ k : Nat, 1 ≤ k →
      absF (D.katoLambda A1 k) ≤
        (D.katoAlpha A1 * vecNorm1 D.v0 * (sqNatF k : F)⁻¹) * powF (D.katoRho A1) (k - 1)) := by
  have hstrong : ∀ K m : Nat, m ≤ K →
      vecNorm1 (D.katoVec A1 m) ≤
        (vecNorm1 D.v0 * (sqNatF (m + 1) : F)⁻¹) * powF (D.katoRho A1) m := by
    intro K
    induction K with
    | zero =>
      intro m hm
      have hm0 : m = 0 := by omega
      rw [hm0, D.katoVec_zero, powF_zero, lofMulOne]
      have hsq1 : (sqNatF 1 : F)⁻¹ = 1 := by
        unfold sqNatF
        rw [natCastF_one, lofOneMul, inv_one]
      rw [hsq1, lofMulOne]
      exact LinearOrderedField.le_refl _
    | succ r ih =>
      intro m hm
      by_cases hmr : m ≤ r
      · exact ih m hmr
      · have hmeq : m = r + 1 := by omega
        rw [hmeq]
        rw [D.katoVec_succ A1 r]
        have htri := vecNorm1_add_le
          (vecNeg (matVec D.S (matVec A1 (D.katoVec A1 r))))
          (vecSumRange 1 r (fun j =>
            vecSmul (D.katoLambda A1 j) (matVec D.S (D.katoVec A1 (r + 1 - j)))))
        conv at htri => rhs; arg 1; rw [vecNorm1_neg, matVec_matVec]
        -- Bound first term `‖S A₁ v_r‖₁`
        have ht1 : vecNorm1 (matVec (matMul D.S A1) (D.katoVec A1 r)) ≤
            (fourF * D.katoBeta A1) *
              ((vecNorm1 D.v0 * (sqNatF (r + 2) : F)⁻¹) * powF (D.katoRho A1) r) := by
          have hb1 := vecNorm1_matVec_le (matMul D.S A1) (D.katoVec A1 r)
          have hb2 := mul_le_mul_of_nonneg_left (ih r (Nat.le_refl r))
            (matNormSum_nonneg (matMul D.S A1))
          have hb3 := LinearOrderedField.le_trans hb1 hb2
          have hsq4 := inv_sqNatF_le_four_succ (F := F) (r + 1) (by omega)
          have hnonneg_fac : 0 ≤ D.katoBeta A1 * vecNorm1 D.v0 * powF (D.katoRho A1) r :=
            mul_nonneg (mul_nonneg (matNormSum_nonneg (matMul D.S A1)) (vecNorm1_nonneg D.v0))
              (powF_nonneg (le_of_lt (D.katoRho_pos A1)) r)
          have hm4 := mul_le_mul_of_nonneg_left hsq4 hnonneg_fac
          have hleft_eq : D.katoBeta A1 *
              ((vecNorm1 D.v0 * (sqNatF (r + 1) : F)⁻¹) * powF (D.katoRho A1) r) =
              (D.katoBeta A1 * vecNorm1 D.v0 * powF (D.katoRho A1) r) *
                (sqNatF (r + 1) : F)⁻¹ := by
            calc
              D.katoBeta A1 * ((vecNorm1 D.v0 * (sqNatF (r + 1) : F)⁻¹) * powF (D.katoRho A1) r)
                = (D.katoBeta A1 * vecNorm1 D.v0) *
                    ((sqNatF (r + 1) : F)⁻¹ * powF (D.katoRho A1) r) := by
                  rw [lofMulAssoc (vecNorm1 D.v0) _ _, ← lofMulAssoc (D.katoBeta A1) _ _]
              _ = (D.katoBeta A1 * vecNorm1 D.v0 * powF (D.katoRho A1) r) *
                    (sqNatF (r + 1) : F)⁻¹ := by
                  rw [lofMulComm (sqNatF (r + 1) : F)⁻¹ _, ← lofMulAssoc]
          have hright_clean : (D.katoBeta A1 * vecNorm1 D.v0 * powF (D.katoRho A1) r) *
              (fourF * (sqNatF (r + 2) : F)⁻¹) =
              (fourF * D.katoBeta A1) *
                ((vecNorm1 D.v0 * (sqNatF (r + 2) : F)⁻¹) * powF (D.katoRho A1) r) := by
            let b := D.katoBeta A1
            let v := vecNorm1 D.v0
            let p := powF (D.katoRho A1) r
            let q := (sqNatF (r + 2) : F)⁻¹
            change (b * v * p) * (fourF * q) = (fourF * b) * ((v * q) * p)
            calc
              (b * v * p) * (fourF * q)
                = ((b * v * p) * fourF) * q := (lofMulAssoc _ _ _).symm
              _ = (fourF * (b * v * p)) * q := by rw [lofMulComm _ fourF]
              _ = ((fourF * b) * (v * p)) * q := by
                rw [lofMulAssoc b v p, ← lofMulAssoc fourF b (v * p)]
              _ = (fourF * b) * ((v * p) * q) := lofMulAssoc _ _ _
              _ = (fourF * b) * ((v * q) * p) := by
                rw [lofMulAssoc v p q, lofMulComm p q, ← lofMulAssoc v q p]
          unfold katoBeta at hleft_eq
          rw [hleft_eq] at hb3
          exact LinearOrderedField.le_trans hb3 (hright_clean ▸ hm4)
        -- Bound second term (convolution sum)
        have ht2 : vecNorm1 (vecSumRange 1 r (fun j =>
              vecSmul (D.katoLambda A1 j) (matVec D.S (D.katoVec A1 (r + 1 - j))))) ≤
            (eightF * (D.katoAlpha A1 * D.katoSigma * vecNorm1 D.v0)) *
              ((vecNorm1 D.v0 * (sqNatF (r + 2) : F)⁻¹) * powF (D.katoRho A1) r) := by
          have hs1 := vecNorm1_vecSumRange_le 1 r (fun j =>
            vecSmul (D.katoLambda A1 j) (matVec D.S (D.katoVec A1 (r + 1 - j))))
          let C0 := (D.katoAlpha A1 * D.katoSigma * vecNorm1 D.v0) *
              (vecNorm1 D.v0 * powF (D.katoRho A1) r)
          have hC0_nn : 0 ≤ C0 :=
            mul_nonneg
              (mul_nonneg (mul_nonneg (D.katoAlpha_nonneg A1) (matNormSum_nonneg D.S))
                (vecNorm1_nonneg D.v0))
              (mul_nonneg (vecNorm1_nonneg D.v0) (powF_nonneg (le_of_lt (D.katoRho_pos A1)) r))
          have hterm_j : ∀ j, 1 ≤ j → j < 1 + r →
              vecNorm1 (vecSmul (D.katoLambda A1 j) (matVec D.S (D.katoVec A1 (r + 1 - j)))) ≤
                C0 * ((sqNatF j : F)⁻¹ * (sqNatF (r + 2 - j) : F)⁻¹) := by
            intro j hj1 hjr
            rw [vecNorm1_smul]
            have hj_pred : j = (j - 1) + 1 := by omega
            have hlam_j : absF (D.katoLambda A1 j) ≤
                D.katoAlpha A1 *
                  ((vecNorm1 D.v0 * (sqNatF j : F)⁻¹) * powF (D.katoRho A1) (j - 1)) := by
              conv => lhs; rw [hj_pred]
              have hl := D.absF_katoLambda_succ_le A1 (j - 1)
              have hv_prev := ih (j - 1) (by omega)
              have hj_add : j - 1 + 1 = j := by omega
              rw [hj_add] at hv_prev
              have hm := mul_le_mul_of_nonneg_left hv_prev (D.katoAlpha_nonneg A1)
              exact LinearOrderedField.le_trans hl hm
            have hSv : vecNorm1 (matVec D.S (D.katoVec A1 (r + 1 - j))) ≤
                D.katoSigma *
                  ((vecNorm1 D.v0 * (sqNatF (r + 2 - j) : F)⁻¹) *
                    powF (D.katoRho A1) (r + 1 - j)) := by
              have hs_le := vecNorm1_matVec_le D.S (D.katoVec A1 (r + 1 - j))
              have hv_le := mul_le_mul_of_nonneg_left (ih (r + 1 - j) (by omega))
                (matNormSum_nonneg D.S)
              have hsub2 : r + 1 - j + 1 = r + 2 - j := by omega
              rw [hsub2] at hv_le
              exact LinearOrderedField.le_trans hs_le hv_le
            have hprod := mul_le_mul hlam_j hSv (vecNorm1_nonneg _)
              (mul_nonneg (D.katoAlpha_nonneg A1)
                (mul_nonneg
                  (mul_nonneg (vecNorm1_nonneg D.v0)
                    (inv_nonneg_of_nonneg (le_of_lt (sqNatF_pos (by omega)))))
                  (powF_nonneg (le_of_lt (D.katoRho_pos A1)) (j - 1))))
            have hpow_comb : powF (D.katoRho A1) (j - 1) * powF (D.katoRho A1) (r + 1 - j) =
                powF (D.katoRho A1) r := by
              rw [← powF_add]
              have hn : (j - 1) + (r + 1 - j) = r := by omega
              rw [hn]
            have halg :
                (D.katoAlpha A1 * ((vecNorm1 D.v0 * (sqNatF j : F)⁻¹) *
                    powF (D.katoRho A1) (j - 1))) *
                  (D.katoSigma * ((vecNorm1 D.v0 * (sqNatF (r + 2 - j) : F)⁻¹) *
                    powF (D.katoRho A1) (r + 1 - j))) =
                C0 * ((sqNatF j : F)⁻¹ * (sqNatF (r + 2 - j) : F)⁻¹) := by
              unfold C0
              let al := D.katoAlpha A1
              let sg := D.katoSigma
              let v := vecNorm1 D.v0
              let q1 := (sqNatF j : F)⁻¹
              let q2 := (sqNatF (r + 2 - j) : F)⁻¹
              let p1 := powF (D.katoRho A1) (j - 1)
              let p2 := powF (D.katoRho A1) (r + 1 - j)
              rw [← hpow_comb]
              change (al * ((v * q1) * p1)) * (sg * ((v * q2) * p2)) =
                ((al * sg * v) * (v * (p1 * p2))) * (q1 * q2)
              calc
                (al * ((v * q1) * p1)) * (sg * ((v * q2) * p2))
                  = (al * sg) * (((v * q1) * p1) * ((v * q2) * p2)) := by
                    rw [lofMulAssoc al _ _, ← lofMulAssoc ((v * q1) * p1) sg _,
                        lofMulComm ((v * q1) * p1) sg, lofMulAssoc sg _ _, ← lofMulAssoc al sg _]
                _ = (al * sg) * ((v * v) * ((p1 * p2) * (q1 * q2))) := by
                    congr 1
                    calc
                      ((v * q1) * p1) * ((v * q2) * p2)
                        = (v * (q1 * p1)) * (v * (q2 * p2)) := by
                          rw [lofMulAssoc v q1 p1, lofMulAssoc v q2 p2]
                      _ = (v * v) * ((q1 * p1) * (q2 * p2)) := by
                          rw [lofMulAssoc v (q1 * p1) _, ← lofMulAssoc (q1 * p1) v _,
                              lofMulComm (q1 * p1) v, lofMulAssoc v _ _, ← lofMulAssoc v v _]
                      _ = (v * v) * ((p1 * p2) * (q1 * q2)) := by
                          congr 1
                          rw [lofMulComm q1 p1, lofMulAssoc p1 q1 (q2 * p2),
                              ← lofMulAssoc q1 q2 p2, lofMulComm (q1 * q2) p2,
                              ← lofMulAssoc p1 p2 (q1 * q2)]
                _ = ((al * sg * v) * (v * (p1 * p2))) * (q1 * q2) := by
                    rw [← lofMulAssoc (v * v) (p1 * p2) (q1 * q2),
                        lofMulAssoc v v (p1 * p2), ← lofMulAssoc (al * sg) _ (q1 * q2),
                        ← lofMulAssoc (al * sg) v (v * (p1 * p2))]
            exact halg ▸ hprod
          have hs2 := sumRange_le_sumRange 1 r hterm_j
          rw [← sumRange_mul_left] at hs2
          have hextend : sumRange 1 r (fun j => (sqNatF j : F)⁻¹ * (sqNatF (r + 2 - j) : F)⁻¹) ≤
              sumRange 1 (r + 1) (fun j => (sqNatF j : F)⁻¹ * (sqNatF (r + 2 - j) : F)⁻¹) := by
            rw [sumRange_succ 1 r]
            have hlast_nn : 0 ≤ (sqNatF (1 + r) : F)⁻¹ * (sqNatF (r + 2 - (1 + r)) : F)⁻¹ :=
              mul_nonneg (inv_nonneg_of_nonneg (le_of_lt (sqNatF_pos (by omega))))
                (inv_nonneg_of_nonneg (le_of_lt (sqNatF_pos (by omega))))
            have h := LinearOrderedField.add_le_add_left hlast_nn
              (sumRange 1 r (fun j => (sqNatF j : F)⁻¹ * (sqNatF (r + 2 - j) : F)⁻¹))
            rw [lofAddZero] at h
            exact h
          have hconv8 := conv_inv_sqNatF_le_eight (F := F) (r + 1)
          have hsum_le8 := LinearOrderedField.le_trans hextend hconv8
          have hm8 := mul_le_mul_of_nonneg_left hsum_le8 hC0_nn
          have hfin_eq : C0 * (eightF * (sqNatF (r + 2) : F)⁻¹) =
              (eightF * (D.katoAlpha A1 * D.katoSigma * vecNorm1 D.v0)) *
                ((vecNorm1 D.v0 * (sqNatF (r + 2) : F)⁻¹) * powF (D.katoRho A1) r) := by
            unfold C0
            let A := D.katoAlpha A1 * D.katoSigma * vecNorm1 D.v0
            let v := vecNorm1 D.v0
            let p := powF (D.katoRho A1) r
            let q := (sqNatF (r + 2) : F)⁻¹
            change (A * (v * p)) * (eightF * q) = (eightF * A) * ((v * q) * p)
            calc
              (A * (v * p)) * (eightF * q)
                = ((A * (v * p)) * eightF) * q := (lofMulAssoc _ _ _).symm
              _ = (eightF * (A * (v * p))) * q := by rw [lofMulComm _ eightF]
              _ = ((eightF * A) * (v * p)) * q := by rw [← lofMulAssoc eightF A _]
              _ = (eightF * A) * ((v * p) * q) := lofMulAssoc _ _ _
              _ = (eightF * A) * ((v * q) * p) := by
                rw [lofMulAssoc v p q, lofMulComm p q, ← lofMulAssoc v q p]
          exact LinearOrderedField.le_trans hs1
            (LinearOrderedField.le_trans hs2 (hfin_eq ▸ hm8))
        -- Combine `ht1` and `ht2` with `4 β + 8 α σ ‖v₀‖₁ ≤ ρ`
        have hcomb := LinearOrderedField.le_trans htri (add_le_add ht1 ht2)
        rw [← lofRightDistrib] at hcomb
        have hrho_ge : fourF * D.katoBeta A1 +
            eightF * (D.katoAlpha A1 * D.katoSigma * vecNorm1 D.v0) ≤ D.katoRho A1 := by
          unfold katoRho
          have h1 := LinearOrderedField.add_le_add_left (one_nonneg (F := F))
            (fourF * D.katoBeta A1 + eightF * (D.katoAlpha A1 * D.katoSigma * vecNorm1 D.v0))
          rw [lofAddZero] at h1
          exact h1
        have hw_nn : 0 ≤ (vecNorm1 D.v0 * (sqNatF (r + 2) : F)⁻¹) * powF (D.katoRho A1) r :=
          mul_nonneg
            (mul_nonneg (vecNorm1_nonneg D.v0)
              (inv_nonneg_of_nonneg (le_of_lt (sqNatF_pos (by omega)))))
            (powF_nonneg (le_of_lt (D.katoRho_pos A1)) r)
        have hfin := mul_le_mul_of_nonneg_right hrho_ge hw_nn
        have hr_pow : D.katoRho A1 *
            ((vecNorm1 D.v0 * (sqNatF (r + 2) : F)⁻¹) * powF (D.katoRho A1) r) =
            (vecNorm1 D.v0 * (sqNatF (r + 1 + 1) : F)⁻¹) * powF (D.katoRho A1) (r + 1) := by
          have hr2 : r + 1 + 1 = r + 2 := by omega
          rw [hr2, powF_succ, lofMulComm (D.katoRho A1) _, lofMulAssoc]
        exact LinearOrderedField.le_trans hcomb (hr_pow ▸ hfin)
  refine ⟨D.katoRadius_pos A1, ?_, ?_⟩
  · intro k
    exact hstrong k k (Nat.le_refl k)
  · intro k hk
    have hk_eq : k = (k - 1) + 1 := by omega
    conv => lhs; rw [hk_eq]
    have hl := D.absF_katoLambda_succ_le A1 (k - 1)
    have hv := hstrong (k - 1) (k - 1) (Nat.le_refl _)
    have hk_add : k - 1 + 1 = k := by omega
    rw [hk_add] at hv
    have hm := mul_le_mul_of_nonneg_left hv (D.katoAlpha_nonneg A1)
    have hassoc : D.katoAlpha A1 *
        ((vecNorm1 D.v0 * (sqNatF k : F)⁻¹) * powF (D.katoRho A1) (k - 1)) =
        (D.katoAlpha A1 * vecNorm1 D.v0 * (sqNatF k : F)⁻¹) *
          powF (D.katoRho A1) (k - 1) := by
      rw [← lofMulAssoc, ← lofMulAssoc]
    exact LinearOrderedField.le_trans hl (hassoc ▸ hm)

/-- **Theorem (Explicit `O(1 / N)` Cauchy Tail Convergence Rate on `|ε| ≤ R₀`).**
    For every `ε ∈ F` inside the closed analytic convergence disk `|ε| ≤ katoRadius D A₁`
    and every truncation threshold `N ≥ 1`, the partial sums of `∑ λ_k ε^k` satisfy the
    uniform Cauchy tail bound:
      `|∑_{k = N+1}^{N+len} λ_k ε^k| ≤ (α ‖v₀‖₁ R₀) · N⁻¹`. -/
theorem kato_partial_sum_cauchy (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F)
    (eps : F) (heps : absF eps ≤ D.katoRadius A1)
    {N : Nat} (hN : 1 ≤ N) (len : Nat) :
    absF (sumRange (N + 1) len (fun k => D.katoLambda A1 k * powF eps k)) ≤
      (D.katoAlpha A1 * vecNorm1 D.v0 * D.katoRadius A1) * (natCastF N : F)⁻¹ := by
  have hmaj := (D.kato_analytic_majorant_bound A1).2.2
  have htri := absF_sumRange_le (N + 1) len (fun k => D.katoLambda A1 k * powF eps k)
  let C := D.katoAlpha A1 * vecNorm1 D.v0 * D.katoRadius A1
  have hC_nn : 0 ≤ C :=
    mul_nonneg (mul_nonneg (D.katoAlpha_nonneg A1) (vecNorm1_nonneg D.v0))
      (le_of_lt (D.katoRadius_pos A1))
  have hterm : ∀ k, N + 1 ≤ k → k < (N + 1) + len →
      absF (D.katoLambda A1 k * powF eps k) ≤
        C * ((natCastF (k - 1) : F)⁻¹ - (natCastF k : F)⁻¹) := by
    intro k hk1 _
    rw [absF_mul, absF_powF]
    have hlk := hmaj k (by omega)
    have hpow_le : powF (absF eps) k ≤ powF (D.katoRadius A1) k :=
      powF_le_powF (absF_nonneg eps) heps k
    have hm1 := mul_le_mul hlk hpow_le (powF_nonneg (absF_nonneg eps) k)
      (mul_nonneg
        (mul_nonneg (mul_nonneg (D.katoAlpha_nonneg A1) (vecNorm1_nonneg D.v0))
          (inv_nonneg_of_nonneg (le_of_lt (sqNatF_pos (by omega)))))
        (powF_nonneg (le_of_lt (D.katoRho_pos A1)) (k - 1)))
    have hk_eq : k = (k - 1) + 1 := by omega
    have hrad_cancel : powF (D.katoRho A1) (k - 1) * powF (D.katoRadius A1) k =
        D.katoRadius A1 := by
      unfold katoRadius
      conv => lhs; arg 2; rw [hk_eq, powF_succ]
      rw [← lofMulAssoc, powF_mul_inv_cancel (ne_of_gt (D.katoRho_pos A1)), lofOneMul]
    have hsimp : ((D.katoAlpha A1 * vecNorm1 D.v0 * (sqNatF k : F)⁻¹) *
        powF (D.katoRho A1) (k - 1)) * powF (D.katoRadius A1) k =
        C * (sqNatF k : F)⁻¹ := by
      rw [lofMulAssoc _ (powF _ _) _, hrad_cancel]
      unfold C
      rw [lofMulAssoc (D.katoAlpha A1 * vecNorm1 D.v0) (sqNatF k : F)⁻¹ _,
          lofMulComm (sqNatF k : F)⁻¹ _, ← lofMulAssoc]
    rw [hsimp] at hm1
    have hsq_diff : (sqNatF k : F)⁻¹ ≤ (natCastF (k - 1) : F)⁻¹ - (natCastF k : F)⁻¹ := by
      have h := inv_sqNatF_succ_le_diff (F := F) (k - 1) (by omega)
      rw [← hk_eq] at h
      exact h
    exact LinearOrderedField.le_trans hm1 (mul_le_mul_of_nonneg_left hsq_diff hC_nn)
  have hs2 := sumRange_le_sumRange (N + 1) len hterm
  rw [← sumRange_mul_left] at hs2
  have hshift_tel : sumRange (N + 1) len (fun k => (natCastF (k - 1) : F)⁻¹ - (natCastF k : F)⁻¹) =
      (natCastF N : F)⁻¹ - (natCastF (N + len) : F)⁻¹ := by
    rw [sumRange_shift N len]
    have hcongr : sumRange N len (fun j =>
        (natCastF (j + 1 - 1) : F)⁻¹ - (natCastF (j + 1) : F)⁻¹) =
        sumRange N len (fun j => (natCastF j : F)⁻¹ - (natCastF (j + 1) : F)⁻¹) := by
      apply sumRange_congr
      intro j _ _
      have he : j + 1 - 1 = j := by omega
      rw [he]
    rw [hcongr]
    exact sumRange_telescoping N len (fun j => (natCastF j : F)⁻¹)
  rw [hshift_tel] at hs2
  have hsub_le : (natCastF N : F)⁻¹ - (natCastF (N + len) : F)⁻¹ ≤ (natCastF N : F)⁻¹ := by
    have hpos : (0 : F) ≤ (natCastF (N + len) : F)⁻¹ :=
      inv_nonneg_of_nonneg (natCastF_nonneg (N + len))
    have h2 := LinearOrderedField.add_le_add_left (neg_le_neg hpos) (natCastF N : F)⁻¹
    rw [neg_zero, lofAddZero, ← lofSubEqAddNeg] at h2
    exact h2
  exact LinearOrderedField.le_trans htri
    (LinearOrderedField.le_trans hs2 (mul_le_mul_of_nonneg_left hsub_le hC_nn))

end SimpleEigenvalueKatoData

end KatoSpectralData

end Conjecture00000007179
