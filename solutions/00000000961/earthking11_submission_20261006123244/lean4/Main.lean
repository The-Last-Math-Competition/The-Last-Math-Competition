import Std

/-!
Conjecture 00000000961 says that the ratio of the third free cumulant to the
third classical cumulant is sqrt(2).  Up to order three, the classical and
free moment-cumulant formulae coincide:
  kappa_3 = r_3 = m3 - 3*m2*m1 + 2*m1^3.
For the centered two-point law P(X=-1)=2/3, P(X=2)=1/3, its first three
moments are (0,2,2), hence both cumulants are 2 and the ratio is 1.
-/

namespace Tlmc961

structure Moments3 where
  m1 : Int
  m2 : Int
  m3 : Int

def classicalThird (m : Moments3) : Int :=
  m.m3 - 3 * m.m2 * m.m1 + 2 * m.m1 ^ 3

/-- Noncrossing and ordinary set partitions agree through order three. -/
def freeThird (m : Moments3) : Int :=
  m.m3 - 3 * m.m2 * m.m1 + 2 * m.m1 ^ 3

def witnessMoments : Moments3 := ⟨0, 2, 2⟩

theorem witness_is_centered_two_point_law :
    2 * (-1 : Int) + 1 * 2 = 3 * witnessMoments.m1 /\
    2 * (-1 : Int) ^ 2 + 1 * 2 ^ 2 = 3 * witnessMoments.m2 /\
    2 * (-1 : Int) ^ 3 + 1 * 2 ^ 3 = 3 * witnessMoments.m3 := by
  decide

theorem cumulants_equal_two :
    classicalThird witnessMoments = 2 /\ freeThird witnessMoments = 2 := by
  decide

/-- If two positive numbers had ratio sqrt(2), their squares would differ by
a factor of two.  Here both are 2, so that necessary identity is false. -/
theorem counterexample :
    not (freeThird witnessMoments * freeThird witnessMoments =
      2 * (classicalThird witnessMoments * classicalThird witnessMoments)) := by
  decide

#print axioms Tlmc961.counterexample
#print axioms Tlmc961.witness_is_centered_two_point_law

end Tlmc961
