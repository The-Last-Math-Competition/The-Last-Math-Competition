import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers

/-! Conjecture 00000003898: a p-Eisenstein polynomial over Z_p cannot
have leading coefficient of p-adic valuation 1. -/
namespace EisensteinLeading
open Polynomial
variable (p : ℕ) [Fact p.Prime]

theorem leading_valuation_ne_one (E : Polynomial ℤ_[p])
    (hE : E.IsEisensteinAt (Ideal.span {(p : ℤ_[p])})) :
    E.leadingCoeff.valuation ≠ 1 := by
  intro hv
  have hn : E.leadingCoeff ≠ 0 := by
    intro hz
    simp [hz] at hv
  have hm := (PadicInt.mem_span_pow_iff_le_valuation E.leadingCoeff hn 1).2 (by omega)
  exact hE.leading (by simpa using hm)

theorem conjecture_false :
    ¬ ∃ E : Polynomial ℤ_[p],
      E.IsEisensteinAt (Ideal.span {(p : ℤ_[p])}) ∧ E.leadingCoeff.valuation = 1 := by
  rintro ⟨E, he, hv⟩
  exact leading_valuation_ne_one p E he hv

#print axioms conjecture_false
end EisensteinLeading
