import QOnePresentation
import ModThree
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Data.ZMod.Basic

noncomputable section

namespace Gaussian7686

open Polynomial

abbrev ModThreeQuotient := Polynomial (ZMod 3) ⧸
  Ideal.span ({X - C (1 : ZMod 3)} : Set (Polynomial (ZMod 3)))

def modularClass (n : ℕ) : ModThreeQuotient :=
  Ideal.Quotient.mk _ (C (coefficientSequence n : ZMod 3))

theorem modularClass_eq_iff (m n : ℕ) : modularClass m = modularClass n ↔
    coefficientSequence m % 3 = coefficientSequence n % 3 := by
  constructor
  · intro h
    have he := congrArg (Polynomial.quotientSpanXSubCAlgEquiv (1 : ZMod 3)) h
    have hc : (coefficientSequence m : ZMod 3) = (coefficientSequence n : ZMod 3) := by
      simpa [modularClass] using he
    exact (ZMod.natCast_eq_natCast_iff' _ _ 3).mp hc
  · intro h
    apply (Polynomial.quotientSpanXSubCAlgEquiv (1 : ZMod 3)).injective
    simpa [modularClass] using (ZMod.natCast_eq_natCast_iff' _ _ 3).mpr h

theorem modularClass_not_eventuallyPeriodic : ¬ EventuallyPeriodic modularClass := by
  rintro ⟨T, hT, N, hN⟩
  apply ModThree7686.centralBinom_mod_three_not_eventually_periodic
  refine ⟨T, hT, N, ?_⟩
  intro n hn
  have h := (modularClass_eq_iff (n + T) n).mp (hN n hn)
  simpa only [coefficientSequence_eq_centralBinom] using h

theorem reducedGaussian_eval_one (n : ℕ) :
    ((gaussian (2 * n) n).map (Nat.castRingHom (ZMod 3))).eval 1 =
      (Nat.centralBinom n : ZMod 3) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_one]
  rw [gaussian_eval_one, Nat.centralBinom_eq_two_mul_choose]
  rfl

def reducedGaussianClass (n : ℕ) : ModThreeQuotient :=
  Ideal.Quotient.mk _ ((gaussian (2 * n) n).map (Nat.castRingHom (ZMod 3)))

theorem reducedGaussianClass_eq_modularClass (n : ℕ) :
    reducedGaussianClass n = modularClass n := by
  apply (Polynomial.quotientSpanXSubCAlgEquiv (1 : ZMod 3)).injective
  simp only [reducedGaussianClass, modularClass,
    Polynomial.quotientSpanXSubCAlgEquiv_mk, Polynomial.eval_C]
  rw [reducedGaussian_eval_one, coefficientSequence_eq_centralBinom]

theorem reducedGaussianClass_not_eventuallyPeriodic :
    ¬ EventuallyPeriodic reducedGaussianClass := by
  rintro ⟨T, hT, N, hN⟩
  apply modularClass_not_eventuallyPeriodic
  refine ⟨T, hT, N, ?_⟩
  intro n hn
  have h := hN n hn
  simpa only [reducedGaussianClass_eq_modularClass] using h

theorem source_k_one_not_periodic :
    ¬ EventuallyPeriodic constantClass ∧ ¬ EventuallyPeriodic modularClass :=
  ⟨constantClass_not_eventuallyPeriodic, modularClass_not_eventuallyPeriodic⟩

end Gaussian7686
