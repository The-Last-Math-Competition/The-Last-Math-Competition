import Init.Data.Int.DivMod.Lemmas
import Init.Data.Int.Order

namespace PseudoAnosovUnitCounterexample

/-- The arithmetic certificate obtained when an algebraic unit is a rational integer:
its reciprocal is again a rational algebraic integer, hence an integer. -/
def IntegerUnitCertificate (n : Int) : Prop :=
  ∃ m : Int, n * m = 1

/-- An integer with an integer multiplicative inverse is `1` or `-1`. -/
theorem integer_unit_is_one_or_neg_one {n : Int}
    (h : IntegerUnitCertificate n) : n = 1 ∨ n = -1 := by
  rcases h with ⟨m, hm⟩
  by_cases hn : 0 ≤ n
  · exact Or.inl (Int.eq_one_of_mul_eq_one_right hn hm)
  · have hnlt : n < 0 := Int.lt_of_not_ge hn
    have hneg_nonneg : 0 ≤ -n := Int.neg_nonneg_of_nonpos (Int.le_of_lt hnlt)
    have hneg_mul : (-n) * (-m) = 1 := by
      rw [Int.neg_mul_neg]
      exact hm
    have hneg_eq : -n = 1 := Int.eq_one_of_mul_eq_one_right hneg_nonneg hneg_mul
    exact Or.inr (by simpa using congrArg (fun z : Int => -z) hneg_eq)

theorem two_has_no_integer_unit_certificate : ¬ IntegerUnitCertificate 2 := by
  intro h
  rcases integer_unit_is_one_or_neg_one h with h2 | h2
  · exact (by decide : (2 : Int) ≠ 1) h2
  · exact (by decide : (2 : Int) ≠ -1) h2

/-- The explicit bridge parameter used in the written proof. For actual pseudo-Anosov
maps, the cited algebraic-unit theorem and rational-integrality fact provide it. -/
theorem no_stretch_factor_two_of_unit_bridge
    (Witness : Type)
    (stretchFactorIsTwo : Witness → Prop)
    (unitBridge : ∀ w : Witness, stretchFactorIsTwo w → IntegerUnitCertificate 2) :
    ¬ ∃ w : Witness, stretchFactorIsTwo w := by
  rintro ⟨w, hw⟩
  apply two_has_no_integer_unit_certificate
  exact unitBridge w hw

#print axioms integer_unit_is_one_or_neg_one
#print axioms two_has_no_integer_unit_certificate
#print axioms no_stretch_factor_two_of_unit_bridge

end PseudoAnosovUnitCounterexample
