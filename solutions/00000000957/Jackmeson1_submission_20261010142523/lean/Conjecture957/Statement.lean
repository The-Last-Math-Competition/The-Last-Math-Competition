import Mathlib

/-! Formal statement for Conjecture957: definitions only, ending in `Claim`. Split verbatim from the marked block of `Basic.lean`. -/

-- STATEMENT BEGIN
namespace C957

/-- Ambient space R^d. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- "frame": N unit-norm vectors of R^d (the standard setting of the frame potential). -/
abbrev UnitTuples (d N : ℕ) := {Φ : Fin N → E d // ∀ i, ‖Φ i‖ = 1}

/-- "frame potential FP": `FP(Φ) = ∑_{i,j} |⟨φ_i, φ_j⟩|²`. -/
noncomputable def FP {d N : ℕ} (Φ : UnitTuples d N) : ℝ :=
  ∑ i, ∑ j, (inner ℝ (Φ.1 i) (Φ.1 j)) ^ 2

/-- "frame": the vectors span, i.e. a lower frame bound `A‖x‖² ≤ ∑ |⟨x, φ_i⟩|²` with `A > 0`. -/
def IsFrame {d N : ℕ} (Φ : UnitTuples d N) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ x : E d, A * ‖x‖ ^ 2 ≤ ∑ i, (inner ℝ x (Φ.1 i)) ^ 2

/-- "r-fold repetition of an orthogonal basis": there is an orthonormal basis `e` of R^d and an
assignment `f` of each of the N vectors to a basis vector, each basis vector used exactly `r`
times, with `φ_i = ± e_{f i}` (signs allowed, which only makes this notion more generous). -/
def IsRepeatedONB {d N : ℕ} (r : ℕ) (Φ : UnitTuples d N) : Prop :=
  ∃ (e : Fin d → E d) (f : Fin N → Fin d) (s : Fin N → ℝ),
    Orthonormal ℝ e ∧ (∀ k, Fintype.card {i // f i = k} = r) ∧
    ∀ i, (s i = 1 ∨ s i = -1) ∧ Φ.1 i = s i • e (f i)

/-- "Local minima of FP occur at r-fold repetitions of orthogonal bases for frames of redundancy r;
and the classification of minima is complete at integer redundancy": for every dimension `d`
and integer redundancy `r` (so `N = r d` vectors), every frame that is a local minimum of FP on
the unit-norm N-tuples is an r-fold repetition of an orthonormal basis. -/
def Conjecture : Prop :=
  ∀ d r : ℕ, 0 < d → 0 < r → ∀ Φ : UnitTuples d (r * d),
    IsFrame Φ → IsLocalMin FP Φ → IsRepeatedONB r Φ

/-- What this package proves. -/
def Claim : Prop := ¬ Conjecture

end C957
-- STATEMENT END
