import Mathlib

/-! Formal statement for Conjecture6680: definitions only, ending in `Claim`. Split verbatim from the marked block of `Basic.lean`. -/

-- STATEMENT BEGIN
namespace C6680

open Finset

/-- "transport problem": marginals `μ` (on `Fin m`), `ν` (on `Fin n`) are probability vectors. -/
def IsProb {k : ℕ} (μ : Fin k → ℝ) : Prop := (∀ i, 0 ≤ μ i) ∧ ∑ i, μ i = 1

/-- Transport plans (couplings): nonnegative matrices with row sums `μ` and column sums `ν`. -/
def IsCoupling {m n : ℕ} (μ : Fin m → ℝ) (ν : Fin n → ℝ) (π : Fin m → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ π i j) ∧ (∀ i, ∑ j, π i j = μ i) ∧ (∀ j, ∑ i, π i j = ν j)

/-- Transport cost of a plan: `∑ c i j * π i j`. -/
def planCost {m n : ℕ} (c π : Fin m → Fin n → ℝ) : ℝ := ∑ i, ∑ j, c i j * π i j

/-- "the optimal value": the infimum of the transport cost over all couplings. -/
noncomputable def optValue {m n : ℕ} (μ : Fin m → ℝ) (ν : Fin n → ℝ) (c : Fin m → Fin n → ℝ) : ℝ :=
  sInf {t | ∃ π, IsCoupling μ ν π ∧ planCost c π = t}

/-- An optimal transport plan: a coupling of minimal cost. -/
def IsOptPlan {m n : ℕ} (μ : Fin m → ℝ) (ν : Fin n → ℝ) (c π : Fin m → Fin n → ℝ) : Prop :=
  IsCoupling μ ν π ∧ ∀ ρ, IsCoupling μ ν ρ → planCost c π ≤ planCost c ρ

/-- Kantorovich dual feasibility: potentials `(u, v)` with `u i + v j ≤ c i j`. -/
def IsDualFeasible {m n : ℕ} (c : Fin m → Fin n → ℝ) (p : (Fin m → ℝ) × (Fin n → ℝ)) : Prop :=
  ∀ i j, p.1 i + p.2 j ≤ c i j

/-- Dual objective `∑ μ i u i + ∑ ν j v j`. -/
def dualObj {m n : ℕ} (μ : Fin m → ℝ) (ν : Fin n → ℝ) (p : (Fin m → ℝ) × (Fin n → ℝ)) : ℝ :=
  ∑ i, μ i * p.1 i + ∑ j, ν j * p.2 j

/-- An optimal dual solution: a feasible pair maximising the dual objective. -/
def IsDualOpt {m n : ℕ} (μ : Fin m → ℝ) (ν : Fin n → ℝ) (c : Fin m → Fin n → ℝ)
    (p : (Fin m → ℝ) × (Fin n → ℝ)) : Prop :=
  IsDualFeasible c p ∧ ∀ q, IsDualFeasible c q → dualObj μ ν q ≤ dualObj μ ν p

/-- No duality gap: some optimal dual solution attains the primal optimal value. -/
def StrongDuality {m n : ℕ} (μ : Fin m → ℝ) (ν : Fin n → ℝ) (c : Fin m → Fin n → ℝ) : Prop :=
  ∃ p, IsDualOpt μ ν c p ∧ dualObj μ ν p = optValue μ ν c

/-- "dual structure" (layer 2): the optimal dual solution is unique up to the additive gauge
`(u, v) ↦ (u + t, v - t)`, which leaves every constraint and the objective unchanged. -/
def DualUniqueModGauge {m n : ℕ} (μ : Fin m → ℝ) (ν : Fin n → ℝ) (c : Fin m → Fin n → ℝ) : Prop :=
  ∃ p, IsDualOpt μ ν c p ∧ ∀ q, IsDualOpt μ ν c q →
    ∃ t : ℝ, q.1 = (fun i => p.1 i + t) ∧ q.2 = (fun j => p.2 j - t)

/-- "support" (primal reading): the supports of optimal plans, as a family of subsets. -/
def optSuppFamily {m n : ℕ} (μ : Fin m → ℝ) (ν : Fin n → ℝ) (c : Fin m → Fin n → ℝ) :
    Set (Set (Fin m × Fin n)) :=
  {S | ∃ π, IsOptPlan μ ν c π ∧ S = {ij | π ij.1 ij.2 ≠ 0}}

/-- "support" (cost reading): the support of the cost matrix. -/
def costSupp {m n : ℕ} (c : Fin m → Fin n → ℝ) : Set (Fin m × Fin n) := {ij | c ij.1 ij.2 ≠ 0}

/-- Two transport problems (same marginals) with the same optimal value, no duality gap, and
dual structures that differ (unique mod gauge for one, not for the other). -/
def SameValueDualDiffers {m n : ℕ} (μ : Fin m → ℝ) (ν : Fin n → ℝ) (c₁ c₂ : Fin m → Fin n → ℝ) : Prop :=
  optValue μ ν c₁ = optValue μ ν c₂ ∧ StrongDuality μ ν c₁ ∧ StrongDuality μ ν c₂ ∧
    (DualUniqueModGauge μ ν c₁ ∧ ¬ DualUniqueModGauge μ ν c₂)

/-- Reading A: separation by different families of optimal-plan supports. -/
def ConjectureA : Prop :=
  ∃ (m n : ℕ) (μ : Fin m → ℝ) (ν : Fin n → ℝ) (c₁ c₂ : Fin m → Fin n → ℝ),
    IsProb μ ∧ IsProb ν ∧ SameValueDualDiffers μ ν c₁ c₂ ∧
      optSuppFamily μ ν c₁ ≠ optSuppFamily μ ν c₂

/-- Reading B: separation by different cost supports (an explicit degenerate cost pair). -/
def ConjectureB : Prop :=
  ∃ (m n : ℕ) (μ : Fin m → ℝ) (ν : Fin n → ℝ) (c₁ c₂ : Fin m → Fin n → ℝ),
    IsProb μ ∧ IsProb ν ∧ SameValueDualDiffers μ ν c₁ c₂ ∧ costSupp c₁ ≠ costSupp c₂

/-- What this package proves: both readings hold (witnessed by one pair). -/
def Claim : Prop := ConjectureA ∧ ConjectureB

end C6680
-- STATEMENT END
