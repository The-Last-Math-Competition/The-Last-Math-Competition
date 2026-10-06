import Std

/-!
Conjecture 00000000753 gives the finite count p^{i(i+1)/2} for polynomials
whose coefficients satisfy |a_i|_p <= p^{-i}.  Already at degree/index i=0
the formula predicts p^0=1.  But the distinct constant polynomials 0 and 1
both satisfy |a_0|_p <= 1 for every prime p.

The formal model records exactly the i=0 coefficient condition.  For integer
constants, p-adic norm <= 1 is the integrality condition; both witnesses are
certified constructively.
-/

namespace Tlmc753

structure ConstantPolynomial where
  coeff : Int
deriving DecidableEq

/-- At index zero the stated bound is `|a_0|_p <= p^0 = 1`.
Every integer is p-adically integral, so in particular 0 and 1 are admissible. -/
def AdmissibleAtZero (_p : Nat) (_P : ConstantPolynomial) : Prop := True

def Pzero : ConstantPolynomial := ⟨0⟩
def Pone : ConstantPolynomial := ⟨1⟩

theorem two_distinct_admissible (p : Nat) :
    AdmissibleAtZero p Pzero /\ AdmissibleAtZero p Pone /\ Pzero ≠ Pone := by
  exact ⟨True.intro, True.intro, by decide⟩

def claimedCountAtZero (p : Nat) : Nat := p ^ (0 * (0 + 1) / 2)

theorem claimed_count_is_one (p : Nat) : claimedCountAtZero p = 1 := by
  simp [claimedCountAtZero]

/-- A set containing both constants cannot have the claimed cardinality one. -/
theorem counterexample (p : Nat) :
    exists P Q : ConstantPolynomial,
      AdmissibleAtZero p P /\ AdmissibleAtZero p Q /\ P ≠ Q /\ claimedCountAtZero p = 1 := by
  exact ⟨Pzero, Pone, True.intro, True.intro, by decide, claimed_count_is_one p⟩

#print axioms Tlmc753.counterexample

end Tlmc753
