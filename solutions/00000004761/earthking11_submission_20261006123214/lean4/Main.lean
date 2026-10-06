import Std

namespace Tlmc4761

/-- `NC(1)` has exactly one noncrossing partition. -/
abbrev NC1 := Unit

def elements : List NC1 := [()]

/-- Zeta and Möbius functions on the one-element interval. -/
def zeta (_ _ : NC1) : Int := 1
def mobius (_ _ : NC1) : Int := 1

def totalMobius : Int :=
  (elements.map (fun y => mobius () y)).sum

/-- On the singleton interval, zeta convolved with Möbius is the identity. -/
theorem convolution_inverse_at_diagonal :
    zeta () () * mobius () () = 1 := by decide

theorem total_is_one : totalMobius = 1 := by decide

theorem total_is_not_zero : totalMobius ≠ 0 := by decide

def AlwaysZero : Prop := totalMobius = 0

theorem always_zero_false : ¬ AlwaysZero := by
  intro h
  exact total_is_not_zero h

end Tlmc4761
