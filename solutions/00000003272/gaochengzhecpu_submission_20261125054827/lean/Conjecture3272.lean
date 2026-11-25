import Std

namespace Conjecture3272

def eulerCharacteristic (cellDimensions : List Nat) : Int :=
  (cellDimensions.map fun d => if d % 2 = 0 then 1 else -1).sum

def productCellDimensions (left right : List Nat) : List Nat :=
  left.flatMap fun d => right.map fun e => d + e

def cpTwoCellDimensions : List Nat := [0, 2, 4]

def sphereCellDimensions : List Nat := [0, 2]

def productEulerCharacteristic : Int :=
  eulerCharacteristic (productCellDimensions cpTwoCellDimensions sphereCellDimensions)

theorem product_euler_even :
    productEulerCharacteristic = 6 ∧ productEulerCharacteristic % 2 = 0 := by decide

/-- Isomorphism classes of real bundles over the projective line.
    The coefficient of w₂ in H²(CP¹; F₂) takes values in Fin 2.
    Because H¹(CP¹; F₂) vanishes, the degree-two Whitney rule is additive. -/
structure BundleClasses (Bundle : Type) where
  directSum : Bundle → Bundle → Bundle
  trivial : Nat → Bundle
  rank : Bundle → Nat
  secondSW : Bundle → Fin 2
  whitney : ∀ a b, secondSW (directSum a b) = secondSW a + secondSW b
  trivialSW : ∀ n, secondSW (trivial n) = 0
  aboveRank : ∀ b, rank b < 2 → secondSW b = 0

/-- An immersion into R⁷ supplies a rank-one normal bundle even after
    pulling its tangent-normal splitting back to CP¹. -/
def HasNormalLineSplitting {Bundle : Type} (bundles : BundleClasses Bundle)
    (restrictedTangent : Bundle) : Prop :=
  ∃ normal, bundles.rank normal = 1 ∧
    bundles.directSum restrictedTangent normal = bundles.trivial 7

theorem restricted_tangent_sw_nonzero {Bundle : Type} (bundles : BundleClasses Bundle)
    (restrictedTangent cpTwoTangent hyperplane : Bundle)
    (productRestriction : restrictedTangent = bundles.directSum cpTwoTangent (bundles.trivial 2))
    (eulerSequence : bundles.directSum cpTwoTangent (bundles.trivial 2) =
      bundles.directSum (bundles.directSum hyperplane hyperplane) hyperplane)
    (hyperplaneGenerator : bundles.secondSW hyperplane = 1) :
    bundles.secondSW restrictedTangent = 1 := by
  rw [productRestriction, eulerSequence, bundles.whitney, bundles.whitney, hyperplaneGenerator]
  decide

theorem even_euler_without_normal_splitting {Bundle : Type} (bundles : BundleClasses Bundle)
    (restrictedTangent cpTwoTangent hyperplane : Bundle)
    (productRestriction : restrictedTangent = bundles.directSum cpTwoTangent (bundles.trivial 2))
    (eulerSequence : bundles.directSum cpTwoTangent (bundles.trivial 2) =
      bundles.directSum (bundles.directSum hyperplane hyperplane) hyperplane)
    (hyperplaneGenerator : bundles.secondSW hyperplane = 1) :
    productEulerCharacteristic % 2 = 0 ∧
      ¬ HasNormalLineSplitting bundles restrictedTangent := by
  refine ⟨product_euler_even.2, ?_⟩
  intro ⟨normal, normalRank, splitting⟩
  have normalSW : bundles.secondSW normal = 0 :=
    bundles.aboveRank normal (by rw [normalRank]; decide)
  have tangentSW := restricted_tangent_sw_nonzero bundles restrictedTangent cpTwoTangent
    hyperplane productRestriction eulerSequence hyperplaneGenerator
  have equalClasses := congrArg bundles.secondSW splitting
  rw [bundles.whitney, bundles.trivialSW, tangentSW, normalSW] at equalClasses
  exact (by decide : (1 : Fin 2) + 0 ≠ 0) equalClasses

end Conjecture3272

#print axioms Conjecture3272.product_euler_even
#print axioms Conjecture3272.restricted_tangent_sw_nonzero
#print axioms Conjecture3272.even_euler_without_normal_splitting
