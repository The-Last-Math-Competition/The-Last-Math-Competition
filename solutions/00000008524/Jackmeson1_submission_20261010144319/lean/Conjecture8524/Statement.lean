import Mathlib

/-! Formal statement for Conjecture8524: definitions only, ending in `Claim`. Split verbatim from the marked block of `Basic.lean`. -/

-- STATEMENT BEGIN
namespace C8524

open MvPolynomial

/-- Variables `y_{j,θ}` of the differential polynomial ring `Q{y_1..y_n}` with `m` commuting
derivations: `θ : Fin m → ℕ` is the multi-index of the derivative `δ^θ y_j`. -/
abbrev Var (n m : ℕ) := Fin n × (Fin m → ℕ)

/-- "the differential polynomial ring `Q{y_1,...,y_n}`" in `n` indeterminates, `m` derivations. -/
abbrev DRing (n m : ℕ) := MvPolynomial (Var n m) ℚ

/-- The `k`-th derivation: `δ_k (y_{j,θ}) = y_{j,θ+e_k}`. -/
noncomputable def delta {n m : ℕ} (k : Fin m) : Derivation ℚ (DRing n m) (DRing n m) :=
  mkDerivation ℚ (fun v : Var n m => X (v.1, v.2 + Pi.single k 1))

/-- "differential ideal": an ideal stable under every derivation. -/
def IsDiffIdeal {n m : ℕ} (I : Ideal (DRing n m)) : Prop := ∀ (k : Fin m) (p : DRing n m),
  p ∈ I → delta k p ∈ I

/-- The order `|θ|` of a derivative variable. -/
def ord {n m : ℕ} (v : Var n m) : ℕ := ∑ k, v.2 k

/-- Variables of order at most `t` (a finite set of variables). -/
abbrev Low (n m t : ℕ) := {v : Var n m // ord v ≤ t}

/-- The coordinate ring of the order-`t` truncation of the differential variety of `I`:
`Q[y_{j,θ} : |θ| ≤ t] / (I ∩ Q[y_{j,θ} : |θ| ≤ t])`. -/
abbrev Trunc {n m : ℕ} (I : Ideal (DRing n m)) (t : ℕ) :=
  MvPolynomial (Low n m t) ℚ ⧸ I.comap (rename (Subtype.val : Low n m t → Var n m)).toRingHom

/-- Kolchin's dimension function: `ω_I(t)` = Krull dimension of the order-`t` truncation
(equals the transcendence degree of `Q(η_{j,θ} : |θ| ≤ t)` for a prime `I` with generic zero `η`). -/
noncomputable def omega {n m : ℕ} (I : Ideal (DRing n m)) (t : ℕ) : WithBot ℕ∞ :=
  ringKrullDim (Trunc I t)

/-- "`P` is the differential dimension polynomial of `I`": `P ∈ Q[X]` and `ω_I(t) = P(t)` for all
large `t`. -/
def IsDimPoly {n m : ℕ} (I : Ideal (DRing n m)) (P : Polynomial ℚ) : Prop :=
  ∃ N : ℕ, ∀ t ≥ N, ∃ d : ℕ, omega I t = (d : ℕ∞) ∧ P.eval (t : ℚ) = d

/-- The conjecture, for a reading `N n m` of "the number of variables" (with the same number
`N` in "degree is the number of variables" and "integral multiple of `1/N!`"): every proper
differential ideal has a dimension polynomial with rational coefficients, of degree `N`, whose
leading coefficient is an integral multiple of `1/N!`. -/
def Conjecture (N : ℕ → ℕ → ℕ) : Prop := ∀ (n m : ℕ) (I : Ideal (DRing n m)),
  IsDiffIdeal I → I ≠ ⊤ → ∃ P : Polynomial ℚ, IsDimPoly I P ∧ P.natDegree = N n m ∧
    ∃ z : ℤ, P.leadingCoeff = z / (N n m).factorial

/-- What this package proves: both readings (number of derivations `m`; number of
indeterminates `n`) fail. -/
def Claim : Prop := ¬ Conjecture (fun _ m => m) ∧ ¬ Conjecture (fun n _ => n)

end C8524
-- STATEMENT END
