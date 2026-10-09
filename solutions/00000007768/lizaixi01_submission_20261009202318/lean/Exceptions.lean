import ConjugacyCore
import Mathlib.RingTheory.Polynomial.Chebyshev

open Polynomial

set_option autoImplicit false
set_option maxSynthPendingDepth 3
noncomputable section
namespace TLMC7768

def Exceptional (p : ℂ[X]) : Prop :=
  ∃ d : ℕ, AffineConjugate p (X ^ d) ∨
    AffineConjugate p (Polynomial.Chebyshev.T ℂ (d : ℤ)) ∨
    AffineConjugate p (-Polynomial.Chebyshev.T ℂ (d : ℤ))

theorem not_conjugate_power (d : ℕ) : ¬ AffineConjugate candidate (X ^ d) := by
  intro h
  have hd : d = 2 := by simpa using conjugate_degree (X ^ d) h
  subst d
  exact not_conjugate_square h

theorem not_conjugate_chebyshev (d : ℕ) :
    ¬ AffineConjugate candidate (Polynomial.Chebyshev.T ℂ (d : ℤ)) := by
  intro h
  have hd : d = 2 := by
    simpa using conjugate_degree (Polynomial.Chebyshev.T ℂ (d : ℤ)) h
  subst d
  apply not_conjugate_cheb_two_positive
  simpa [Polynomial.Chebyshev.T_two] using h

theorem not_conjugate_negative_chebyshev (d : ℕ) :
    ¬ AffineConjugate candidate (-Polynomial.Chebyshev.T ℂ (d : ℤ)) := by
  intro h
  have hd : d = 2 := by
    simpa using conjugate_degree (-Polynomial.Chebyshev.T ℂ (d : ℤ)) h
  subst d
  apply not_conjugate_cheb_two_negative
  simpa [Polynomial.Chebyshev.T_two] using h

theorem candidate_not_exceptional : ¬ Exceptional candidate := by
  rintro ⟨d, hp | hc | hn⟩
  · exact not_conjugate_power d hp
  · exact not_conjugate_chebyshev d hc
  · exact not_conjugate_negative_chebyshev d hn

end TLMC7768
