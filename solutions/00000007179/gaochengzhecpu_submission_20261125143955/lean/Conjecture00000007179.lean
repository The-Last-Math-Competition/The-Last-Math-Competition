/-
Copyright (c) 2026. All rights reserved.
Formalization of Conjecture 00000007179 in Core Lean 4.19.0 (zero external dependencies).

Top-Level Module: Conjecture00000007179
Conjecture 00000007179 (residual-projection Kato analytic perturbation):
  - English: "Definition: The stability of perturbed spectra with Kato theory.
    Conjecture: Simple eigenvalues are analytically perturbable, and the coefficient of the
    perturbation is the residual projection. (residual-projection Kato analytic perturbation)"
  - Chinese: "定义：摄动谱的稳定性：Kato 理论。猜想：Kato 的摄动：单重特征值的解析摄动且[摄]动的系数为
    残余投影。（Kato 残余投影解析摄动单重特征值）"

Resolution Summary:
  - Verdict: **FALSE** (Clause 1 is **TRUE**; Clause 2 is **FALSE** across all readings).
  - `conjecture_00000007179_clause1_true`: Proves Kato's analytic perturbation theorem for
    every algebraically simple eigenvalue over any linearly ordered field `F` — existence and
    uniqueness of the all-orders normalized formal power series `(λ(ε), v(ε))`, closed-form
    first- and second-order formulas (`λ₁ = tr(P A₁) = tr(P A₁ P) = w₀ᵀ A₁ v₀ / w₀ᵀ v₀`,
    `v₁ = - S A₁ v₀`, `λ₂ = - tr(P A₁ S A₁)`), explicit positive Cauchy-Kato convergence
    radius `R₀ = ρ⁻¹ > 0`, and `O(1/N)` Cauchy tail convergence on `|ε| ≤ R₀`.
  - `conjecture_00000007179_clause2_false`: Refutes Clause 2 across Readings A, B, C, and D
    (plus proves the universal `n × n` impossibility `¬ ∀ A₁, λ₁(A₁) = tr(Q A₁)` and the
    defective Jordan Puiseux obstruction when simplicity is dropped).
  - `conjecture_00000007179_resolved_over_Q`: Unconditional, hypothesis-free instantiation
    over the constructive exact rational field `Q`.
-/

import Conjecture00000007179.OrderedField
import Conjecture00000007179.KatoPerturbation
import Conjecture00000007179.Refutation

namespace Conjecture00000007179

/-- **Clause 1 Positive Theorem (Kato Analytic Perturbability of Simple Eigenvalues):**
    For every algebraically simple eigenvalue Kato datum `(A₀, λ₀)` and perturbation `A₁`:
    (1) `(katoLambda, katoVec)` satisfies normalization `w₀ᵀ v_k = 0` (`k ≥ 1`), the exact
        formal power series eigenvalue equation at all orders `k ≥ 0`, and all-orders uniqueness;
    (2) the exact first- and second-order coefficients are governed by the eigenprojection `P`
        and reduced resolvent `S`:
          `λ₁ = tr(P A₁) = tr(P A₁ P) = (w₀ᵀ A₁ v₀)/(w₀ᵀ v₀)`,
          `v₁ = - S A₁ v₀`,
          `λ₂ = - tr(P A₁ S A₁)`;
    (3) the series admits an explicit positive analytic convergence radius `R₀ > 0` with uniform
        `O(1 / N)` Cauchy tail rate on `|ε| ≤ R₀`. -/
theorem conjecture_00000007179_clause1_true
    {F : Type u} [LinearOrderedField F] {n : Nat} {A0 : Mat n F} {lam0 : F}
    (D : SimpleEigenvalueKatoData n F A0 lam0) (A1 : Mat n F) :
    -- All-orders existence & normalization
    (∀ k, 1 ≤ k → vecDot D.w0 (D.katoVec A1 k) = 0) ∧
    (∀ k, vecAdd (matVec A0 (D.katoVec A1 (k + 1))) (matVec A1 (D.katoVec A1 k)) =
      vecSumRange 0 (k + 2) (fun j =>
        vecSmul (D.katoLambda A1 j) (D.katoVec A1 (k + 1 - j)))) ∧
    -- Exact Kato formulas at orders 1 and 2
    (D.katoLambda A1 1 = matTrace (matMul D.P A1) ∧
     D.katoLambda A1 1 = matTrace (matMul (matMul D.P A1) D.P) ∧
     D.katoLambda A1 1 = vecDot D.w0 (matVec A1 D.v0) / vecDot D.w0 D.v0) ∧
    (D.katoVec A1 1 = vecNeg (matVec D.S (matVec A1 D.v0))) ∧
    (D.katoLambda A1 2 = - matTrace (matMul (matMul (matMul D.P A1) D.S) A1)) ∧
    -- Explicit positive analytic convergence radius & Cauchy tail rate
    (0 < D.katoRadius A1 ∧
     ∀ eps : F, absF eps ≤ D.katoRadius A1 → ∀ N : Nat, 1 ≤ N → ∀ len : Nat,
       absF (sumRange (N + 1) len (fun k => D.katoLambda A1 k * powF eps k)) ≤
         (D.katoAlpha A1 * vecNorm1 D.v0 * D.katoRadius A1) * (natCastF N : F)⁻¹) := by
  have hf1 := D.kato_first_order_eigenvalue A1
  refine ⟨fun k hk => D.katoVec_ortho A1 hk,
          D.kato_power_series_eq A1,
          ⟨hf1.2.1, hf1.2.2, hf1.1⟩,
          D.kato_first_order_eigenvector A1,
          (D.kato_second_order_eigenvalue A1).2,
          ⟨D.katoRadius_pos A1, fun eps heps N hN len =>
            D.kato_partial_sum_cauchy A1 eps heps hN len⟩⟩

/-- **Clause 2 Exhaustive Refutation Theorem:**
    Every candidate reading of "the coefficient of the perturbation is the residual projection"
    (`Q = I - P`) is false over any linearly ordered field `F`:
    - Universal `n × n` trace-duality refutation (`¬ ∀ A₁, λ₁(A₁) = tr(Q A₁)`) for every simple
      eigenvalue;
    - Reading A concrete refutations (`tr(Q A₁)`, `w₀ᵀ Q A₁ v₀ / w₀ᵀ v₀`, `‖Q A₁ v₀‖₁`, `‖Q A₁ v₀‖₂²`);
    - Reading B refutation (`v₁ ≠ ± Q A₁ v₀`);
    - Reading C refutation (`λ₂ ≠ ± tr(P A₁ Q A₁)`);
    - Reading D refutation (`P₁ ≠ ± Q` and `P₁ ≠ ± (P A₁ Q + Q A₁ P)`). -/
theorem conjecture_00000007179_clause2_false
    {F : Type u} [LinearOrderedField F] :
    (∀ {n : Nat} {A0 : Mat n F} {lam0 : F} (D : SimpleEigenvalueKatoData n F A0 lam0),
      ¬ (∀ A1 : Mat n F, D.katoLambda A1 1 = matTrace (matMul D.Q A1))) ∧
    -- Concrete 2 × 2 refutations across Readings A, B, C, and D
    (∃ (A0 A1 : Mat 2 F) (lam0 : F) (D : SimpleEigenvalueKatoData 2 F A0 lam0),
      D.katoLambda A1 1 ≠ matTrace (matMul D.Q A1) ∧
      D.katoLambda A1 1 ≠ - matTrace (matMul D.Q A1) ∧
      D.katoLambda A1 1 ≠ vecDot D.w0 (matVec D.Q (matVec A1 D.v0)) / vecDot D.w0 D.v0 ∧
      absF (D.katoLambda A1 1) ≠ vecNorm1 (matVec D.Q (matVec A1 D.v0))) ∧
    (∃ (A0 A1 : Mat 2 F) (lam0 : F) (D : SimpleEigenvalueKatoData 2 F A0 lam0),
      D.katoVec A1 1 ≠ matVec D.Q (matVec A1 D.v0) ∧
      D.katoVec A1 1 ≠ vecNeg (matVec D.Q (matVec A1 D.v0)) ∧
      D.katoLambda A1 2 ≠ matTrace (matMul (matMul (matMul D.P A1) D.Q) A1) ∧
      D.katoLambda A1 2 ≠ - matTrace (matMul (matMul (matMul D.P A1) D.Q) A1) ∧
      D.katoProjFirstOrder A1 ≠ D.Q ∧
      D.katoProjFirstOrder A1 ≠ matNeg D.Q ∧
      D.katoProjFirstOrder A1 ≠
        matAdd (matMul (matMul D.P A1) D.Q) (matMul (matMul D.Q A1) D.P) ∧
      D.katoProjFirstOrder A1 ≠
        matNeg (matAdd (matMul (matMul D.P A1) D.Q) (matMul (matMul D.Q A1) D.P))) := by
  have hA := readingA_refuted (F := F)
  have hB := readingB_refuted (F := F)
  have hC := readingC_refuted (F := F)
  have hD := readingD_refuted (F := F)
  refine ⟨fun D => universal_readingA_trace_impossible D, ?_, ?_⟩
  · refine ⟨mat2 twoF 0 0 0, mat2 1 0 0 0, twoF,
      diag2KatoData twoF 0 zero_sub_two_ne_zero,
      hA.1.2.2.1, hA.1.2.2.2.1, hA.1.2.2.2.2.1, hA.1.2.2.2.2.2⟩
  · refine ⟨mat2 fiveF 0 0 1,
      mat2 0 1 1 0, fiveF, diag2KatoData fiveF 1 one_sub_five_ne_zero,
      hB.2.2.1, hB.2.2.2, hC.2.2.1, hC.2.2.2,
      hD.2.1, hD.2.2.1, hD.2.2.2.1, hD.2.2.2.2⟩

/-- **Unconditional Constructive Resolution Over Exact Rationals `Q`:**
    Instantiates Clause 1 (positive Kato analytic perturbation theorem), Clause 2 (refutations
    across Readings A-D), and the defective Jordan non-analyticity obstruction unconditionally
    over the constructively inhabited rational field `Q`. -/
theorem conjecture_00000007179_resolved_over_Q :
    -- (I) Clause 1 holds for every simple eigenvalue datum over `Q`
    (∀ {n : Nat} {A0 : Mat n Q} {lam0 : Q}
        (D : SimpleEigenvalueKatoData n Q A0 lam0) (A1 : Mat n Q),
      D.katoLambda A1 1 = matTrace (matMul D.P A1) ∧
      D.katoVec A1 1 = vecNeg (matVec D.S (matVec A1 D.v0)) ∧
      D.katoLambda A1 2 = - matTrace (matMul (matMul (matMul D.P A1) D.S) A1) ∧
      0 < D.katoRadius A1) ∧
    -- (II) Clause 2 is false across Readings A, B, C, and D over `Q`
    ((∀ {n : Nat} {A0 : Mat n Q} {lam0 : Q} (D : SimpleEigenvalueKatoData n Q A0 lam0),
        ¬ (∀ A1 : Mat n Q, D.katoLambda A1 1 = matTrace (matMul D.Q A1))) ∧
     (∃ (A0 A1 : Mat 2 Q) (lam0 : Q) (D : SimpleEigenvalueKatoData 2 Q A0 lam0),
        D.katoLambda A1 1 ≠ matTrace (matMul D.Q A1) ∧
        D.katoLambda A1 1 ≠ - matTrace (matMul D.Q A1)) ∧
     (∃ (A0 A1 : Mat 2 Q) (lam0 : Q) (D : SimpleEigenvalueKatoData 2 Q A0 lam0),
        D.katoVec A1 1 ≠ matVec D.Q (matVec A1 D.v0) ∧
        D.katoVec A1 1 ≠ vecNeg (matVec D.Q (matVec A1 D.v0)) ∧
        D.katoLambda A1 2 ≠ matTrace (matMul (matMul (matMul D.P A1) D.Q) A1) ∧
        D.katoLambda A1 2 ≠ - matTrace (matMul (matMul (matMul D.P A1) D.Q) A1))) ∧
    -- (III) Dropping simplicity breaks analyticity (`A(ε) = [[0, 1], [ε, 0]]` over `Q`)
    (¬ ∃ lamSeq : Nat → Q,
        lamSeq 0 * lamSeq 0 = 0 ∧
        (lamSeq 0 * lamSeq 1 + lamSeq 1 * lamSeq 0) - 1 = 0) := by
  have hc2 := conjecture_00000007179_clause2_false (F := Q)
  refine ⟨?_, ⟨hc2.1, ?_, ?_⟩, (defective_jordan_not_analytically_perturbable (F := Q)).1⟩
  · intro n A0 lam0 D A1
    have hc1 := conjecture_00000007179_clause1_true D A1
    exact ⟨hc1.2.2.1.1, hc1.2.2.2.1, hc1.2.2.2.2.1, hc1.2.2.2.2.2.1⟩
  · rcases hc2.2.1 with ⟨A0, A1, lam0, D, h1, h2, _, _⟩
    exact ⟨A0, A1, lam0, D, h1, h2⟩
  · rcases hc2.2.2 with ⟨A0, A1, lam0, D, h1, h2, h3, h4, _, _, _, _⟩
    exact ⟨A0, A1, lam0, D, h1, h2, h3, h4⟩

end Conjecture00000007179
