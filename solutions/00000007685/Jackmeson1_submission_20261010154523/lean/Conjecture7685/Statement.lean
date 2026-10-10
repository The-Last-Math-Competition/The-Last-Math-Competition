import Mathlib

/-! Formal statement for Conjecture7685: definitions only, ending in `Claim`. Split verbatim from the marked block of `Basic.lean`. -/

-- STATEMENT BEGIN
namespace C7685

open Filter Topology

/-- "theta_3(w) = Σ q^{n²} w^n" (bilateral series over `n : ℤ`). -/
noncomputable def theta (q w : ℝ) : ℝ := ∑' n : ℤ, q ^ (n ^ 2) * w ^ n

/-- "the theta quotient T(z) = theta_3(z q) / theta_3(z)". -/
noncomputable def T (q z : ℝ) : ℝ := theta q (z * q) / theta q z

/-- "J_q = ∫_0^1 T(z) d_q z" with the Jackson measure `(1-q) Σ_{n ≥ 0} z q^n f(z q^n)` at `z = 1`. -/
noncomputable def J (q : ℝ) : ℝ := (1 - q) * ∑' n : ℕ, q ^ n * T q (q ^ n)

/-- The claimed leading coefficient `Γ(1/4)^2 / (2 π^{3/2})`. -/
noncomputable def c : ℝ := Real.Gamma (1 / 4) ^ 2 / (2 * Real.pi ^ ((3 : ℝ) / 2))

/-- "J_q is transcendental when q ∈ (0,1) is algebraic". -/
def TranscConj : Prop :=
  ∀ q : ℝ, 0 < q → q < 1 → IsAlgebraic ℚ q → Transcendental ℚ (J q)

/-- "the leading coefficient of the Puiseux expansion of J_q in q-1 is c": for some real exponent
`α`, `J_q = L (1-q)^α (1 + o(1))` as `q → 1⁻`, with `|L| = c`.  The absolute value makes the
choice of branch / sign of `(q-1)^α` irrelevant, so this is weaker than the conjecture. -/
def LeadCoeffConj : Prop :=
  ∃ α L : ℝ, Tendsto (fun q => J q / (1 - q) ^ α) (𝓝[<] 1) (𝓝 L) ∧ |L| = c

/-- The conjecture as written. -/
def Conjecture : Prop := TranscConj ∧ LeadCoeffConj

/-- What this package proves: the second conjunct fails, hence the conjecture is false. -/
def Claim : Prop := ¬ Conjecture

end C7685
-- STATEMENT END
