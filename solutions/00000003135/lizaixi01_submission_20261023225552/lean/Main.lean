import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ByContra

open scoped Manifold ContDiff
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace TLMC3135

abbrev G := Multiplicative (ZMod 2)
abbrev E := Fin 0 → ℝ
abbrev model := modelWithCornersSelf ℝ E

instance groupTopology : TopologicalSpace G := ⊥
instance groupDiscrete : DiscreteTopology G := ⟨rfl⟩
instance groupCharts : ChartedSpace E G := ChartedSpace.ofDiscreteTopology
instance groupManifold (n : ℕ∞ω) : IsManifold model n G := IsManifold.of_discreteTopology _
instance smoothGroup (n : ℕ∞ω) : LieGroup model n G where
  contMDiff_mul := contMDiff_of_discreteTopology
  contMDiff_inv := contMDiff_of_discreteTopology

theorem finite_group_card : Fintype.card G = 2 := by decide

theorem group_nilpotent : Group.IsNilpotent G := inferInstance

theorem group_hausdorff : T2Space G := inferInstance
theorem group_second_countable : SecondCountableTopology G := inferInstance
theorem group_compact : CompactSpace G := inferInstance
theorem model_finrank : Module.finrank ℝ E = 0 := by simp

abbrev Lie := GroupLieAlgebra model G

instance lieUnique : Unique Lie := by
  unfold Lie GroupLieAlgebra TangentSpace
  infer_instance

theorem lie_eq_zero (v : Lie) : v = 0 := Subsingleton.elim _ _

instance lieFiniteDimensional : FiniteDimensional ℝ Lie := inferInstance

theorem lie_finrank : Module.finrank ℝ Lie = 0 :=
  Module.finrank_eq_zero_of_subsingleton ℝ Lie

@[instance_reducible] def actual_lie_algebra : LieAlgebra ℝ Lie := inferInstance

def conjugation (g x : G) : G := g * x * g⁻¹

theorem conjugation_eq_id (g : G) : conjugation g = id := by
  funext x
  simp [conjugation]

theorem conjugation_smooth (g : G) : ContMDiff model model ∞ (conjugation g) :=
  contMDiff_of_discreteTopology

def adjoint (g : G) : Lie →L[ℝ] Lie := by
  have h : conjugation g (1 : G) = 1 := by simp [conjugation]
  have d := mfderiv model model (conjugation g) (1 : G)
  rw [h] at d
  exact d

theorem adjoint_eq_id (g : G) : adjoint g = ContinuousLinearMap.id ℝ Lie :=
  Subsingleton.elim _ _

abbrev Dual := Module.Dual ℝ Lie

def coadjoint (g : G) (f : Dual) : Dual := f.comp (adjoint g⁻¹).toLinearMap

theorem coadjoint_eq (g : G) (f : Dual) : coadjoint g f = f :=
  Subsingleton.elim _ _

instance coadjointAction : MulAction G Dual where
  smul := coadjoint
  one_smul _ := Subsingleton.elim _ _
  mul_smul _ _ _ := Subsingleton.elim _ _

abbrev CoadjointOrbits := Quotient (MulAction.orbitRel G Dual)

instance coadjointOrbitsSubsingleton : Subsingleton CoadjointOrbits := inferInstance

theorem coadjoint_orbit_nonempty : Nonempty CoadjointOrbits :=
  ⟨Quotient.mk (MulAction.orbitRel G Dual) (0 : Dual)⟩

theorem complex_submodule_dichotomy (S : Submodule ℂ ℂ) : S = ⊥ ∨ S = ⊤ := by
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  have hx : ∃ x ∈ S, x ≠ 0 := by
    by_contra! hx
    apply hS
    apply le_antisymm
    · intro x hxS
      exact (Submodule.mem_bot ℂ).mpr (hx x hxS)
    · exact bot_le
  obtain ⟨x, hx, hx0⟩ := hx
  apply top_unique
  intro y _
  have h := S.smul_mem (y * x⁻¹) hx
  simpa only [smul_eq_mul, mul_assoc, inv_mul_cancel₀ hx0, mul_one] using h

/-- All continuous irreducible unitary representations on nonzero complex Hilbert
spaces in this universe. Equivalence below allows different carriers. -/
structure UnitaryRep where
  V : Type
  [normed : NormedAddCommGroup V]
  [inner : InnerProductSpace ℂ V]
  [complete : CompleteSpace V]
  [nontrivial : Nontrivial V]
  action : G →* (V ≃ₗᵢ[ℂ] V)
  strong_continuity : ∀ v : V, Continuous (fun g => action g v)
  irreducible : ∀ S : Submodule ℂ V, IsClosed (S : Set V) →
    (∀ g : G, ∀ v ∈ S, action g v ∈ S) → S = ⊥ ∨ S = ⊤

attribute [instance] UnitaryRep.normed UnitaryRep.inner UnitaryRep.complete
  UnitaryRep.nontrivial

def UnitarilyEquivalent (P Q : UnitaryRep) : Prop :=
  ∃ e : P.V ≃ₗᵢ[ℂ] Q.V, ∀ (g : G) (v : P.V), e (P.action g v) = Q.action g (e v)

theorem unitary_equivalence_refl (P : UnitaryRep) : UnitarilyEquivalent P P :=
  ⟨LinearIsometryEquiv.refl ℂ P.V, fun _ _ => rfl⟩

theorem unitary_equivalence_symm {P Q : UnitaryRep} :
    UnitarilyEquivalent P Q → UnitarilyEquivalent Q P := by
  rintro ⟨e, he⟩
  refine ⟨e.symm, ?_⟩
  intro g v
  apply e.injective
  rw [he]
  simp

theorem unitary_equivalence_trans {P Q R : UnitaryRep} :
    UnitarilyEquivalent P Q → UnitarilyEquivalent Q R → UnitarilyEquivalent P R := by
  rintro ⟨e, he⟩ ⟨f, hf⟩
  refine ⟨e.trans f, ?_⟩
  intro g v
  change f (e (P.action g v)) = R.action g (f (e v))
  rw [he, hf]

def unitarySetoid : Setoid UnitaryRep where
  r := UnitarilyEquivalent
  iseqv := ⟨unitary_equivalence_refl, unitary_equivalence_symm, unitary_equivalence_trans⟩

abbrev UnitaryDual := Quotient unitarySetoid

def trivialAction : G →* (ℂ ≃ₗᵢ[ℂ] ℂ) := 1

def signAction : G →* (ℂ ≃ₗᵢ[ℂ] ℂ) where
  toFun g := if Multiplicative.toAdd g = 0 then 1 else LinearIsometryEquiv.neg ℂ
  map_one' := by ext z; simp
  map_mul' := by
    intro g h
    fin_cases g <;> fin_cases h <;>
      ext z <;> simp only [toAdd_mul] <;> norm_num
    rw [if_pos (by decide : (2 : ZMod 2) = 0)]
    rfl

def trivialRep : UnitaryRep where
  V := ℂ
  action := trivialAction
  strong_continuity _ := continuous_of_discreteTopology
  irreducible S _ _ := complex_submodule_dichotomy S

def signRep : UnitaryRep where
  V := ℂ
  action := signAction
  strong_continuity _ := continuous_of_discreteTopology
  irreducible S _ _ := complex_submodule_dichotomy S

def generator : G := Multiplicative.ofAdd (1 : ZMod 2)

theorem sign_generator_apply (z : ℂ) : signAction generator z = -z := by
  simp [signAction, generator]

theorem trivial_generator_apply (z : ℂ) : trivialAction generator z = z := rfl

theorem trivial_not_equivalent_sign : ¬ UnitarilyEquivalent trivialRep signRep := by
  rintro ⟨e, he⟩
  have h := he generator (1 : ℂ)
  change e (trivialAction generator (1 : ℂ)) = signAction generator (e (1 : ℂ)) at h
  rw [trivial_generator_apply, sign_generator_apply] at h
  have hn : e (-(1 : ℂ)) = e (1 : ℂ) := by
    rw [map_neg]
    exact h.symm
  have hbad : -(1 : ℂ) = (1 : ℂ) := e.injective hn
  norm_num at hbad

theorem distinct_unitary_classes :
    (Quotient.mk unitarySetoid trivialRep : UnitaryDual) ≠
      Quotient.mk unitarySetoid signRep := by
  intro h
  exact trivial_not_equivalent_sign (Quotient.exact h)

theorem no_equivalence_between_orbits_and_unitary_dual :
    ¬ Nonempty (CoadjointOrbits ≃ UnitaryDual) := by
  rintro ⟨e⟩
  apply distinct_unitary_classes
  apply e.symm.injective
  exact Subsingleton.elim _ _

theorem no_bijective_correspondence :
    ¬ ∃ f : CoadjointOrbits → UnitaryDual, Function.Bijective f := by
  rintro ⟨f, hf⟩
  exact no_equivalence_between_orbits_and_unitary_dual ⟨Equiv.ofBijective f hf⟩

end TLMC3135

