import Std

namespace Tlmc7674

abbrev Fraction := Nat × Nat

def fracLt (x y : Fraction) : Prop := x.1 * y.2 < y.1 * x.2

def zeroQ : Fraction := (0, 1)
def half : Fraction := (1, 2)
def oneQ : Fraction := (1, 1)

theorem half_positive : fracLt zeroQ half := by simp [fracLt, zeroQ, half]

theorem half_lt_one : fracLt half oneQ := by simp [fracLt, half, oneQ]

/-- Every strictly increasing logarithm normalized by `log 1 = zero` sends
`1/2` to a negative value.  This abstracts exactly the two standard real-log
facts used by the counterexample, without postulating an axiom. -/
theorem log_half_negative {β : Type} [LT β]
    (log : Fraction → β) (zero : β)
    (hstrict : ∀ a b : Fraction, fracLt a b → log a < log b)
    (hlogOne : log oneQ = zero) : log half < zero := by
  have h := hstrict half oneQ half_lt_one
  rw [hlogOne] at h
  exact h

/-- A nonnegative `kappa` cannot equal `log(1/2)`. -/
theorem kappa_not_log_half {β : Type} [LT β]
    (log : Fraction → β) (zero kappa : β)
    (hstrict : ∀ a b : Fraction, fracLt a b → log a < log b)
    (hlogOne : log oneQ = zero) (hkappa : ¬ kappa < zero) :
    kappa ≠ log half := by
  intro h
  have hneg : log half < zero := log_half_negative log zero hstrict hlogOne
  apply hkappa
  simpa [h] using hneg

/-- Logical packaging of the contradiction for every standard logarithm. -/
theorem no_conjectured_kappa_at_half {β : Type} [LT β]
    (log : Fraction → β) (zero : β)
    (hstrict : ∀ a b : Fraction, fracLt a b → log a < log b)
    (hlogOne : log oneQ = zero) :
    ¬ ∃ kappa : β, (¬ kappa < zero) ∧ kappa = log half := by
  rintro ⟨kappa, hkappa, hEq⟩
  exact kappa_not_log_half log zero kappa hstrict hlogOne hkappa hEq

end Tlmc7674
