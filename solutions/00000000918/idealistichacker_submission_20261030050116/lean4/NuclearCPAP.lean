import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

namespace Quasitrace918

open scoped CStarAlgebra

structure FiniteCStarModel where
  carrier : Type
  [instCStar : CStarAlgebra carrier]
  [instOrder : PartialOrder carrier]
  [instStarOrder : StarOrderedRing carrier]
  [instFinite : FiniteDimensional ℂ carrier]

attribute [instance] FiniteCStarModel.instCStar FiniteCStarModel.instOrder
  FiniteCStarModel.instStarOrder FiniteCStarModel.instFinite

def CPC {A B : Type} [CStarAlgebra A] [CStarAlgebra B]
    [PartialOrder A] [PartialOrder B] [StarOrderedRing A] [StarOrderedRing B]
    (φ : A →CP B) : Prop :=
  ∀ a, ‖φ a‖ ≤ ‖a‖

-- The full finite-set/epsilon c.p.c. approximation property, not a dimension test.
def HasCPAP (A : Type) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] : Prop :=
  ∀ (s : Finset A) (ε : ℝ), 0 < ε →
    ∃ (F : FiniteCStarModel) (φ : A →CP F.carrier) (ψ : F.carrier →CP A),
      CPC φ ∧ CPC ψ ∧ ∀ a ∈ s, ‖ψ (φ a) - a‖ < ε

variable (A : Type) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

noncomputable def identityCP : A →CP A :=
  CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (StarAlgHom.id ℂ A)

theorem identityCP_apply (a : A) : identityCP A a = a := rfl

theorem identityCP_cpc : CPC (identityCP A) := by
  intro a
  exact le_rfl

theorem identityCP_matrix_nonneg (k : Nat) (M : CStarMatrix (Fin k) (Fin k) A)
    (hM : 0 ≤ M) : 0 ≤ M.map (identityCP A) :=
  (identityCP A).map_cstarMatrix_nonneg M hM

def finiteModel [FiniteDimensional ℂ A] : FiniteCStarModel where
  carrier := A
  instCStar := inferInstance
  instOrder := inferInstance
  instStarOrder := inferInstance
  instFinite := inferInstance

theorem finite_dimensional_hasCPAP [FiniteDimensional ℂ A] : HasCPAP A := by
  intro s ε hε
  refine ⟨finiteModel A, identityCP A, identityCP A, identityCP_cpc A, identityCP_cpc A, ?_⟩
  intro a _
  change ‖a - a‖ < ε
  simpa only [sub_self, norm_zero] using hε

theorem exact_cpc_factorization [FiniteDimensional ℂ A] :
    ∃ (F : FiniteCStarModel) (φ : A →CP F.carrier) (ψ : F.carrier →CP A),
      CPC φ ∧ CPC ψ ∧ ∀ a, ψ (φ a) = a := by
  exact ⟨finiteModel A, identityCP A, identityCP A, identityCP_cpc A,
    identityCP_cpc A, fun _ => rfl⟩

end Quasitrace918

#check Quasitrace918.identityCP_apply
#print axioms Quasitrace918.identityCP_apply
#check Quasitrace918.identityCP_cpc
#print axioms Quasitrace918.identityCP_cpc
#check Quasitrace918.identityCP_matrix_nonneg
#print axioms Quasitrace918.identityCP_matrix_nonneg
#check Quasitrace918.finite_dimensional_hasCPAP
#print axioms Quasitrace918.finite_dimensional_hasCPAP
#check Quasitrace918.exact_cpc_factorization
#print axioms Quasitrace918.exact_cpc_factorization
#print Quasitrace918.HasCPAP
#print axioms Quasitrace918.HasCPAP
#print axioms Quasitrace918.identityCP
#print axioms Quasitrace918.finiteModel
