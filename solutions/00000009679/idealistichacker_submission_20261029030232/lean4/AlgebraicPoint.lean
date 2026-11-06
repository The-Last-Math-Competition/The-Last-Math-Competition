import Mathlib.NumberTheory.Real.Irrational
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Tactic

namespace ModularValue9679

noncomputable def point : Complex := (Real.sqrt 2 : Complex) + Complex.I

theorem point_re : point.re = Real.sqrt 2 := by simp [point]

theorem point_im : point.im = 1 := by simp [point]

theorem point_im_pos : 0 < point.im := by simp [point_im]

theorem point_sq_re : (point ^ 2).re = 1 := by
  simp only [pow_two, Complex.mul_re, point_re, point_im]
  nlinarith [Real.sq_sqrt (show LE.le (0 : Real) 2 by norm_num)]

theorem point_sq_im : (point ^ 2).im = 2 * Real.sqrt 2 := by
  simp only [pow_two, Complex.mul_im, point_re, point_im]
  ring

theorem point_algebraic : IsAlgebraic Rat point := by
  have hs : (Real.sqrt 2 : Complex) ^ 2 = 2 := by
    exact_mod_cast (Real.sq_sqrt (show LE.le (0 : Real) 2 by norm_num))
  have hx : IsAlgebraic Rat ((Real.sqrt 2 : Complex) ^ 2) := by
    rw [hs]
    exact isAlgebraic_natCast 2
  have hi : IsAlgebraic Rat (Complex.I ^ 2) := by
    simpa using (isAlgebraic_intCast (R := Rat) (A := Complex) (-1))
  exact (IsAlgebraic.of_pow (by decide : 0 < (2 : Nat)) hx).add
    (IsAlgebraic.of_pow (by decide : 0 < (2 : Nat)) hi)

theorem quadratic_relation_trivial (a b c : Rat)
    (h : (a : Complex) * point ^ 2 + (b : Complex) * point + (c : Complex) = 0) :
    And (a = 0) (And (b = 0) (c = 0)) := by
  have him : (a : Real) * (2 * Real.sqrt 2) + (b : Real) = 0 := by
    have hi := congrArg Complex.im h
    simpa [Complex.mul_im, point_sq_im, point_im] using hi
  have ha : a = 0 := by
    by_contra ha
    have haR : Not ((a : Real) = 0) := by exact_mod_cast ha
    have hq : Real.sqrt 2 = ((-b / (2 * a) : Rat) : Real) := by
      push_cast
      apply (eq_div_iff (mul_ne_zero (by norm_num : Not ((2 : Real) = 0)) haR)).2
      nlinarith [him]
    exact irrational_sqrt_two.ne_rat (-b / (2 * a)) hq
  have hb : b = 0 := by
    have hbR : (b : Real) = 0 := by simpa [ha] using him
    exact_mod_cast hbR
  have hc : c = 0 := by
    have hcC : (c : Complex) = 0 := by simpa [ha, hb] using h
    exact_mod_cast hcC
  exact And.intro ha (And.intro hb hc)

theorem point_triple_independent :
    LinearIndependent Rat ![(1 : Complex), point, point ^ 2] := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  have hs : (g 0 : Complex) + (g 1 : Complex) * point +
      (g 2 : Complex) * point ^ 2 = 0 := by
    simpa [Fin.sum_univ_three, Algebra.smul_def] using hg
  have hr : (g 2 : Complex) * point ^ 2 + (g 1 : Complex) * point +
      (g 0 : Complex) = 0 := by linear_combination hs
  have hcoef := quadratic_relation_trivial _ _ _ hr
  have h2 := hcoef.1
  have h1 := hcoef.2.1
  have h0 := hcoef.2.2
  fin_cases i <;> assumption

theorem point_not_mem_quadratic (K : IntermediateField Rat Complex)
    (hK : Module.finrank Rat K = 2) : Not (K.carrier point) := by
  intro hp
  let t : K := Subtype.mk point hp
  let v : Fin 3 -> K := ![1, t, t ^ 2]
  have hcomp : (fun i => (v i : Complex)) = ![1, point, point ^ 2] := by
    funext i
    fin_cases i <;> rfl
  have hv : LinearIndependent Rat v := by
    apply LinearIndependent.of_comp K.val.toLinearMap
    change LinearIndependent Rat (fun i => (v i : Complex))
    rw [hcomp]
    exact point_triple_independent
  let : FiniteDimensional Rat K := FiniteDimensional.of_finrank_pos (by omega)
  have hcard := hv.fintype_card_le_finrank
  norm_num [hK] at hcard

end ModularValue9679

#check ModularValue9679.point_re
#print axioms ModularValue9679.point_re
#check ModularValue9679.point_im
#print axioms ModularValue9679.point_im
#check ModularValue9679.point_im_pos
#print axioms ModularValue9679.point_im_pos
#check ModularValue9679.point_sq_re
#print axioms ModularValue9679.point_sq_re
#check ModularValue9679.point_sq_im
#print axioms ModularValue9679.point_sq_im
#check ModularValue9679.point_algebraic
#print axioms ModularValue9679.point_algebraic
#check ModularValue9679.quadratic_relation_trivial
#print axioms ModularValue9679.quadratic_relation_trivial
#check ModularValue9679.point_triple_independent
#print axioms ModularValue9679.point_triple_independent
#check ModularValue9679.point_not_mem_quadratic
#print axioms ModularValue9679.point_not_mem_quadratic
