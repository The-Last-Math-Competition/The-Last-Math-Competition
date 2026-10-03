import Lean

/-! Conjecture 996 explicitly gives the two rational dimensions and their ratio.
Its numerical equality is false, in either order of the ratio. -/
namespace Conjecture996
open Std.Internal

def firstDimension : Rat := (4 : Rat) / 3
def secondDimension : Rat := (7 : Rat) / 4
def claimedRatio : Rat := (7 : Rat) / 9

def StatedRatio : Prop := firstDimension / secondDimension = claimedRatio

theorem firstDimension_positive : firstDimension > 0 := by decide
theorem secondDimension_positive : secondDimension > 0 := by decide
theorem exact_ratio : firstDimension / secondDimension = (16 : Rat) / 21 := by decide
theorem reverse_ratio : secondDimension / firstDimension = (21 : Rat) / 16 := by decide

/-- Negates exactly the rational equality asserted in the source. -/
theorem conjecture996_false : ¬ StatedRatio := by unfold StatedRatio; decide

/-- Reading 'ratio between' in the opposite order does not fix the equality. -/
theorem reversed_claim_also_false : secondDimension / firstDimension ≠ claimedRatio := by decide

#print axioms exact_ratio
#print axioms reverse_ratio
#print axioms conjecture996_false
#print axioms reversed_claim_also_false
end Conjecture996
