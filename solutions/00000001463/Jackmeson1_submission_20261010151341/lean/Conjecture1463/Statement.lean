import Mathlib

/-! Formal statement for Conjecture1463: definitions only, ending in `Claim`. Split verbatim from the marked block of `Basic.lean`. -/

-- STATEMENT BEGIN
namespace C1463

open Filter Topology ENNReal

/-- "projection constant" of `E` inside a superspace `X` via an isometric copy `j`:
the infimum of `‖P‖` over bounded linear projections `P` of `X` onto `j(E)`
(`P` is the identity on `j(E)` and has range inside `j(E)`). -/
noncomputable def relProj (𝕜 : Type) [RCLike 𝕜] {E X : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (j : E →ₗᵢ[𝕜] X) : ℝ :=
  ⨅ P : {P : X →L[𝕜] X // (∀ y, P (j y) = j y) ∧ ∀ x, ∃ y, P x = j y}, ‖P.1‖

/-- "the (absolute) projection constant" `λ(E)`: the supremum, over all Banach spaces `X`
(of the base universe) containing an isometric copy `j(E)` of `E`, of the least norm of a projection
of `X` onto `j(E)`. -/
noncomputable def absProj (𝕜 : Type) [RCLike 𝕜] (E : Type) [NormedAddCommGroup E] [NormedSpace 𝕜 E] : ℝ :=
  sSup {r | ∃ (X : Type) (_ : NormedAddCommGroup X) (_ : NormedSpace 𝕜 X) (_ : CompleteSpace X)
    (j : E →ₗᵢ[𝕜] X), r = relProj 𝕜 j}

/-- "the projection constant of `ℓ_p^n`" (`p ∈ [1,∞]`, `ℓ_p^n = 𝕜^n` with the `p`-norm). -/
noncomputable def lam (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) : ℝ :=
  absProj 𝕜 (PiLp p fun _ : Fin n => 𝕜)

/-- "the supremum of the projection constants of `ℓ_p^n` over `p ∈ [1, ∞]`". -/
noncomputable def supLam (𝕜 : Type) [RCLike 𝕜] (n : ℕ) : ℝ :=
  sSup {r | ∃ (p : ℝ≥0∞) (h : 1 ≤ p), r = @lam 𝕜 _ p ⟨h⟩ n}

/-- "the supremum ... is `c√n` uniformly (explicit `c`), attained asymptotically by both `ℓ₁ⁿ` and
`ℓ∞ⁿ`": for one real constant `c`, `sup_p λ(ℓ_p^n) = c√n` for all `n ≥ 1` and
`λ(ℓ₁ⁿ) / (c√n) → 1` and `λ(ℓ∞ⁿ) / (c√n) → 1`. -/
def ConjSharp (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∃ c : ℝ, (∀ n : ℕ, 1 ≤ n → supLam 𝕜 n = c * Real.sqrt n) ∧
    Tendsto (fun n : ℕ => lam 𝕜 1 n / (c * Real.sqrt n)) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ => lam 𝕜 ∞ n / (c * Real.sqrt n)) atTop (𝓝 1)

/-- Weaker "order of magnitude" reading of "attained asymptotically by `ℓ∞ⁿ`":
`λ(ℓ∞ⁿ) ≥ κ√n` for some `κ > 0` and all `n ≥ 1`. -/
def ConjOrder (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ n : ℕ, 1 ≤ n → κ * Real.sqrt n ≤ lam 𝕜 ∞ n

/-- What this package proves, for real and complex scalars and both readings. -/
def Claim : Prop :=
  ¬ ConjSharp ℝ ∧ ¬ ConjSharp ℂ ∧ ¬ ConjOrder ℝ ∧ ¬ ConjOrder ℂ

end C1463
-- STATEMENT END
