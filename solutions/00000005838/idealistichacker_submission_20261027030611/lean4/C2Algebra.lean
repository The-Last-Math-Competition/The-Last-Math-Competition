import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Data.ZMod.Basic

/-! A conditional group-algebra core, not a formalization of character blocks. -/

namespace C2Algebra5838

abbrev C2 := Multiplicative (ZMod 2)

def s : C2 := Multiplicative.ofAdd (1 : ZMod 2)

theorem s_ne_one : s ≠ (1 : C2) := by decide

theorem s_mul_s : s * s = (1 : C2) := by decide

theorem element_cases : ∀ g : C2, g = 1 ∨ g = s := by
  change ∀ g : Fin 2, g = 0 ∨ g = 1
  decide

section Coefficients

variable {K : Type*} [Semiring K]

theorem coeff_decomposition (e : MonoidAlgebra K C2) :
    e = MonoidAlgebra.single 1 (e.coeff 1) + MonoidAlgebra.single s (e.coeff s) := by
  classical
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  rcases element_cases g with rfl | rfl
  · simp [s_ne_one]
  · simp [Ne.symm s_ne_one]

end Coefficients

section CharacteristicTwo

variable {K : Type*} [CommSemiring K] [CharP K 2]

theorem two_coeff_square (a b : K) :
    (MonoidAlgebra.single 1 a + MonoidAlgebra.single s b) *
        (MonoidAlgebra.single 1 a + MonoidAlgebra.single s b) =
      MonoidAlgebra.single 1 (a * a + b * b) := by
  classical
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  rcases element_cases g with rfl | rfl
  · simp [add_mul, mul_add, s_mul_s, s_ne_one]
  · simp [mul_add, s_mul_s, Ne.symm s_ne_one,
      mul_comm, CharTwo.add_self_eq_zero]

theorem square_formula (e : MonoidAlgebra K C2) :
    e * e = MonoidAlgebra.single 1
      (e.coeff 1 * e.coeff 1 + e.coeff s * e.coeff s) := by
  calc
    e * e =
        (MonoidAlgebra.single 1 (e.coeff 1) + MonoidAlgebra.single s (e.coeff s)) *
          (MonoidAlgebra.single 1 (e.coeff 1) + MonoidAlgebra.single s (e.coeff s)) :=
      congrArg (fun x : MonoidAlgebra K C2 => x * x) (coeff_decomposition e)
    _ = _ := two_coeff_square (e.coeff 1) (e.coeff s)

theorem coeff_square_s (e : MonoidAlgebra K C2) : (e * e).coeff s = 0 := by
  classical
  rw [square_formula]
  simp [Ne.symm s_ne_one]

theorem coeff_square_one (e : MonoidAlgebra K C2) :
    (e * e).coeff 1 = e.coeff 1 * e.coeff 1 + e.coeff s * e.coeff s := by
  classical
  rw [square_formula]
  simp

theorem idempotent_coeff_s_zero (e : MonoidAlgebra K C2) (he : IsIdempotentElem e) :
    e.coeff s = 0 := by
  calc
    e.coeff s = (e * e).coeff s :=
      congrArg (fun x : MonoidAlgebra K C2 => x.coeff s) he.eq.symm
    _ = 0 := coeff_square_s e

end CharacteristicTwo

section Field

variable {K : Type*} [Field K] [CharP K 2]

theorem char2idempotent_only_zero_one (e : MonoidAlgebra K C2)
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hb : e.coeff s = 0 := idempotent_coeff_s_zero e he
  have ha : e.coeff 1 * e.coeff 1 = e.coeff 1 := by
    have h := congrArg (fun x : MonoidAlgebra K C2 => x.coeff 1) he.eq
    rw [coeff_square_one, hb, mul_zero, add_zero] at h
    exact h
  have hz : e.coeff 1 * (e.coeff 1 - 1) = 0 := by
    rw [mul_sub, mul_one, ha, sub_self]
  rcases mul_eq_zero.mp hz with ha0 | ha1
  · left
    rw [coeff_decomposition e, hb, ha0]
    simp
  · right
    have haone : e.coeff 1 = 1 := sub_eq_zero.mp ha1
    rw [coeff_decomposition e, hb, haone]
    simp [MonoidAlgebra.one_def]

omit [CharP K 2] in
theorem principal_one_nonzero : (1 : MonoidAlgebra K C2) ≠ 0 := one_ne_zero

end Field

end C2Algebra5838
