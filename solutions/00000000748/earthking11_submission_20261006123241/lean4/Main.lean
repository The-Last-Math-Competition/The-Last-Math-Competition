import Std

/-!
Conjecture 00000000748 claims that the only minimum-degree polynomial maps
compatible with the Teichmuller lift are identity and Frobenius.  The zero
polynomial is a literal counterexample.  Compatibility of polynomials across
the lift only uses that the Teichmuller lift sends zero to zero.
-/

namespace Tlmc748

abbrev F3 := Fin 3

/-- The property expressed by `P ∘ w = w ∘ Pbar`. -/
def LiftCompatible (w : F3 -> Int) (P : Int -> Int) (Pbar : F3 -> F3) : Prop :=
  forall x, P (w x) = w (Pbar x)

def zeroZ : Int -> Int := fun _ => 0
def zeroF : F3 -> F3 := fun _ => 0
def identityZ : Int -> Int := fun x => x
def frobeniusZ : Int -> Int := fun x => x ^ 3

/-- Constant zero polynomials commute with every zero-preserving lift. -/
theorem zero_compatible (w : F3 -> Int) (hzero : w 0 = 0) :
    LiftCompatible w zeroZ zeroF := by
  intro x
  simp [zeroZ, zeroF, hzero]

theorem zero_not_identity : zeroZ ≠ identityZ := by
  intro h
  have := congrFun h 1
  change (0 : Int) = 1 at this
  omega

theorem zero_not_frobenius : zeroZ ≠ frobeniusZ := by
  intro h
  have := congrFun h 1
  change (0 : Int) = 1 ^ 3 at this
  omega

/-- The concrete witness: a compatible degree-zero map outside the two listed maps. -/
theorem counterexample (w : F3 -> Int) (hzero : w 0 = 0) :
    exists P : Int -> Int, exists Pbar : F3 -> F3,
      LiftCompatible w P Pbar /\ P ≠ identityZ /\ P ≠ frobeniusZ := by
  exact ⟨zeroZ, zeroF, zero_compatible w hzero, zero_not_identity, zero_not_frobenius⟩

#print axioms Tlmc748.counterexample

end Tlmc748
