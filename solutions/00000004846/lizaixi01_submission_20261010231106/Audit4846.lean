import Coarse4846

set_option pp.universes true
set_option pp.explicit false
namespace Coordinate4846
theorem checkedOriginal4846Type :
  Function.Injective inclusion ∧ inclusion.range=H ∧
  (∀ u : G, ∃ w : List GLetter, eval gletter w=u) ∧
  (∀ u : G, u∈H → ∃ w : List HLetter, eval hletter w=u) ∧
  (∀ n : ℕ, ∃ u : G, u∈H ∧ gLength u≤n ∧ hLength u=distortion n) ∧
  CoarseEquivalent distortion threeHalves ∧
  (∀ k : ℕ, 0<k → ¬ CoarseEquivalent distortion (fun n => n^k)) :=
  original4846_counterexample
end Coordinate4846
#print Coordinate4846.checkedOriginal4846Type
#print axioms Coordinate4846.checkedOriginal4846Type
#print axioms Coordinate4846.original4846_counterexample
#print axioms Coordinate4846.ambient_bounds
#print axioms Coordinate4846.intrinsic_constructive_upper
#print axioms Coordinate4846.distortion_attained
#print axioms Coordinate4846.integer_exclusion
#print Coordinate4846.product
#print Coordinate4846.inverse
#print Coordinate4846.H
#print Coordinate4846.Heisenberg.product
#print Coordinate4846.inclusion
#print Coordinate4846.gletter
#print Coordinate4846.hletter
#print Coordinate4846.wordLength
#print Coordinate4846.hball
#print Coordinate4846.distortion
#print Coordinate4846.CoarseLE
#print Coordinate4846.threeHalves
#check Coordinate4846.threeHalves_characterization
#check Coordinate4846.distortion_lower_all_radii
#check Coordinate4846.distortion_upper_square
#check Coordinate4846.distortion_equiv_threeHalves
#check Coordinate4846.integer_exclusion
