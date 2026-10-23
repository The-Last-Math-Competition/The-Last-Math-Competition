import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped Manifold ContDiff
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace TLMC6034

abbrev G := Multiplicative (ZMod 2)
abbrev E := Fin 0 → ℝ
abbrev groupModel := modelWithCornersSelf ℝ E
abbrev V := Fin 2 → ℝ
abbrev planeModel := modelWithCornersSelf ℝ V

instance groupTopology : TopologicalSpace G := ⊥
instance groupDiscrete : DiscreteTopology G := ⟨rfl⟩
instance groupCharts : ChartedSpace E G := ChartedSpace.ofDiscreteTopology
instance groupManifold (n : ℕ∞ω) : IsManifold groupModel n G :=
  IsManifold.of_discreteTopology _
instance smoothGroup (n : ℕ∞ω) : LieGroup groupModel n G where
  contMDiff_mul := contMDiff_of_discreteTopology
  contMDiff_inv := contMDiff_of_discreteTopology

theorem group_card : Fintype.card G = 2 := by decide
theorem group_compact : CompactSpace G := inferInstance
theorem group_hausdorff : T2Space G := inferInstance
theorem plane_manifold : IsManifold planeModel ∞ V := inferInstance
theorem plane_connected : ConnectedSpace V := inferInstance
theorem plane_finrank : Module.finrank ℝ V = 2 := by simp

abbrev Lie := GroupLieAlgebra groupModel G
instance lieUnique : Unique Lie := by
  unfold Lie GroupLieAlgebra TangentSpace
  infer_instance
instance lieNormedAddCommGroup : NormedAddCommGroup Lie := by
  unfold Lie GroupLieAlgebra TangentSpace
  infer_instance
instance lieNormedSpace : NormedSpace ℝ Lie := by
  unfold Lie GroupLieAlgebra TangentSpace
  infer_instance
theorem lie_eq_zero (ξ : Lie) : ξ = 0 := Subsingleton.elim _ _
theorem lie_finrank : Module.finrank ℝ Lie = 0 :=
  Module.finrank_eq_zero_of_subsingleton ℝ Lie
instance lieFiniteDimensional : FiniteDimensional ℝ Lie := inferInstance
@[instance_reducible] def actualLieAlgebra : LieAlgebra ℝ Lie := inferInstance

def conjugation (g h : G) : G := g * h * g⁻¹
theorem conjugation_apply (g h : G) : conjugation g h = h := by
  simp [conjugation]
theorem conjugation_smooth (g : G) :
    ContMDiff groupModel groupModel ∞ (conjugation g) :=
  contMDiff_of_discreteTopology

def adjoint (g : G) : Lie →L[ℝ] Lie := by
  have h : conjugation g (1 : G) = 1 := conjugation_apply g 1
  have d := mfderiv groupModel groupModel (conjugation g) (1 : G)
  rw [h] at d
  exact d
theorem adjoint_eq_id (g : G) : adjoint g = ContinuousLinearMap.id ℝ Lie :=
  Subsingleton.elim _ _

/-- The continuous dual agrees with the algebraic dual in this finite-dimensional Lie algebra. -/
abbrev Dual := Lie →L[ℝ] ℝ
def algebraicDualEquiv : Module.Dual ℝ Lie ≃ₗ[ℝ] Dual :=
  LinearMap.toContinuousLinearMap
theorem algebraic_dual_equiv_apply (f : Module.Dual ℝ Lie) (ξ : Lie) :
    algebraicDualEquiv f ξ = f ξ := rfl
def coadjoint (g : G) (f : Dual) : Dual := f.comp (adjoint g⁻¹)
theorem coadjoint_eq (g : G) (f : Dual) : coadjoint g f = f :=
  Subsingleton.elim _ _
instance coadjointAction : MulAction G Dual where
  smul := coadjoint
  one_smul _ := Subsingleton.elim _ _
  mul_smul _ _ _ := Subsingleton.elim _ _
abbrev CoadjointOrbits := Quotient (MulAction.orbitRel G Dual)
instance coadjointOrbitsSubsingleton : Subsingleton CoadjointOrbits := inferInstance
instance coadjointOrbitsNonempty : Nonempty CoadjointOrbits :=
  ⟨Quotient.mk (MulAction.orbitRel G Dual) (0 : Dual)⟩
theorem coadjoint_orbit_card : Nat.card CoadjointOrbits = 1 := Nat.card_unique

def epsilon (g : G) : ℝ := if Multiplicative.toAdd g = 0 then 1 else -1
theorem epsilon_one : epsilon (1 : G) = 1 := by simp [epsilon]
theorem epsilon_mul (g h : G) : epsilon (g * h) = epsilon g * epsilon h := by
  have aux (a b : ZMod 2) :
      (if a + b = 0 then (1 : ℝ) else -1) =
        (if a = 0 then (1 : ℝ) else -1) * (if b = 0 then (1 : ℝ) else -1) := by
    fin_cases a <;> fin_cases b
    · change (1 : ℝ) = 1 * 1
      norm_num
    · change (-1 : ℝ) = 1 * -1
      norm_num
    · change (-1 : ℝ) = -1 * 1
      norm_num
    · change (1 : ℝ) = -1 * -1
      norm_num
  exact aux (Multiplicative.toAdd g) (Multiplicative.toAdd h)
theorem epsilon_sq (g : G) : epsilon g * epsilon g = 1 := by
  unfold epsilon
  split <;> norm_num

instance planeAction : MulAction G V where
  smul g x := epsilon g • x
  one_smul x := by
    change epsilon (1 : G) • x = x
    rw [epsilon_one, one_smul]
  mul_smul g h x := by
    change epsilon (g * h) • x = epsilon g • (epsilon h • x)
    rw [epsilon_mul, mul_smul]
theorem action_apply (g : G) (x : V) : g • x = epsilon g • x := rfl
theorem action_zero (g : G) : g • (0 : V) = 0 := by
  simp [action_apply]
theorem action_zero_iff (g : G) (x : V) : g • x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have := congrArg (fun y : V => g⁻¹ • y) h
    simpa [action_zero] using this
  · intro h
    rw [h, action_zero]

theorem epsilon_smooth : ContMDiff groupModel 𝓘(ℝ, ℝ) ∞ epsilon :=
  contMDiff_of_discreteTopology
theorem joint_action_smooth :
    ContMDiff (groupModel.prod planeModel) planeModel ∞ (fun p : G × V => p.1 • p.2) := by
  change ContMDiff (groupModel.prod planeModel) planeModel ∞
    (fun p : G × V => epsilon p.1 • p.2)
  exact (epsilon_smooth.comp contMDiff_fst).smul contMDiff_snd
instance smoothAction : ContMDiffSMul groupModel planeModel ∞ G V :=
  ⟨joint_action_smooth⟩

def coordinate (i : Fin 2) : V →L[ℝ] ℝ := ContinuousLinearMap.proj i
def area : V →L[ℝ] V →L[ℝ] ℝ :=
  (coordinate 0).smulRight (coordinate 1) -
    (coordinate 1).smulRight (coordinate 0)
theorem area_apply (u v : V) : area u v = u 0 * v 1 - u 1 * v 0 := rfl
def areaAt (x : V) :
    TangentSpace planeModel x →L[ℝ] TangentSpace planeModel x →L[ℝ] ℝ := area
theorem area_at_apply (x : V) (u v : TangentSpace planeModel x) :
    areaAt x u v = u 0 * v 1 - u 1 * v 0 := rfl
theorem area_alternating (u : V) : area u u = 0 := by
  rw [area_apply]
  ring
theorem area_skew (u v : V) : area u v = -area v u := by
  simp only [area_apply]
  ring

def axis0 : V := fun i => if i = 0 then 1 else 0
def axis1 : V := fun i => if i = 1 then 1 else 0
theorem axis0_ne_zero : axis0 ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [axis0] at h0
theorem area_nondegenerate (u : V) (h : ∀ v : V, area u v = 0) : u = 0 := by
  have h0 : u 0 = 0 := by simpa [area_apply, axis1] using h axis1
  have h1 : u 1 = 0 := by
    have h' : -(u 1) = 0 := by simpa [area_apply, axis0] using h axis0
    linarith
  ext i
  fin_cases i <;> assumption

/-- The constant differential 2-form in the global vector-space chart. -/
def areaField : V → V →L[ℝ] V →L[ℝ] ℝ := fun _ => area
theorem area_field_smooth : ContDiff ℝ ∞ areaField := contDiff_const
theorem area_field_hasFDerivAt (x : V) :
    HasFDerivAt areaField (0 : V →L[ℝ] (V →L[ℝ] V →L[ℝ] ℝ)) x :=
  hasFDerivAt_const _ _

/-- Exterior derivative of a 2-form in a vector-space chart, evaluated on constant fields. -/
def exteriorDerivativeTwo (formField : V → V →L[ℝ] V →L[ℝ] ℝ)
    (x u v w : V) : ℝ :=
  (fderiv ℝ formField x u) v w - (fderiv ℝ formField x v) u w + (fderiv ℝ formField x w) u v
theorem area_closed (x u v w : V) : exteriorDerivativeTwo areaField x u v w = 0 := by
  simp [exteriorDerivativeTwo, (area_field_hasFDerivAt x).fderiv]

theorem action_hasFDerivAt (g : G) (x : V) :
    HasFDerivAt (fun y : V => g • y)
      (epsilon g • ContinuousLinearMap.id ℝ V) x :=
  (hasFDerivAt_id x).const_smul (epsilon g)
theorem action_preserves_area (g : G) (u v : V) : area (g • u) (g • v) = area u v := by
  simp only [action_apply, area_apply, Pi.smul_apply, smul_eq_mul]
  calc
    epsilon g * u 0 * (epsilon g * v 1) - epsilon g * u 1 * (epsilon g * v 0) =
        (epsilon g * epsilon g) * (u 0 * v 1 - u 1 * v 0) := by ring
    _ = u 0 * v 1 - u 1 * v 0 := by rw [epsilon_sq, one_mul]
theorem action_pullback_area (g : G) (x u v : V) :
    areaField (g • x) (fderiv ℝ (fun y : V => g • y) x u)
      (fderiv ℝ (fun y : V => g • y) x v) = areaField x u v := by
  rw [(action_hasFDerivAt g x).fderiv]
  exact action_preserves_area g u v

/-- The fundamental vector field is the actual derivative of the orbit map at the identity. -/
def fundamental (ξ : Lie) (x : V) : V :=
  mfderiv groupModel planeModel (fun g : G => g • x) (1 : G) ξ
theorem orbit_map_smooth (x : V) :
    ContMDiff groupModel planeModel ∞ (fun g : G => g • x) :=
  contMDiff_of_discreteTopology
theorem fundamental_zero (ξ : Lie) (x : V) : fundamental ξ x = 0 := by
  rw [lie_eq_zero ξ]
  exact map_zero _

def momentMap : V → Dual := fun _ => 0
theorem moment_map_smooth : ContDiff ℝ ∞ momentMap := contDiff_const
theorem moment_map_equivariant (g : G) (x : V) : momentMap (g • x) = g • momentMap x :=
  Subsingleton.elim _ _
theorem moment_component_hasFDerivAt (ξ : Lie) (x : V) :
    HasFDerivAt (fun y : V => momentMap y ξ) (0 : V →L[ℝ] ℝ) x :=
  hasFDerivAt_const _ _
theorem moment_map_identity (ξ : Lie) (x v : V) :
    fderiv ℝ (fun y : V => momentMap y ξ) x v = areaField x (fundamental ξ x) v := by
  rw [(moment_component_hasFDerivAt ξ x).fderiv, fundamental_zero]
  simp [areaField]

def zeroLevel : Set V := {x | momentMap x = 0}
theorem zero_level_eq_univ : zeroLevel = Set.univ := by
  ext x
  simp [zeroLevel, momentMap]
abbrev Level := zeroLevel
instance levelAction : MulAction G Level where
  smul g x := ⟨g • x.1, by simp [zeroLevel, momentMap]⟩
  one_smul x := Subtype.ext (one_smul _ _)
  mul_smul g h x := Subtype.ext (mul_smul _ _ _)
theorem level_action_coe (g : G) (x : Level) : (g • x).1 = g • x.1 := rfl
abbrev ReducedSpace := Quotient (MulAction.orbitRel G Level)
def levelOrigin : Level := ⟨0, by simp [zeroLevel, momentMap]⟩
def levelAxis : Level := ⟨axis0, by simp [zeroLevel, momentMap]⟩

theorem plane_stabilizer_zero : MulAction.stabilizer G (0 : V) = ⊤ := by
  ext g
  simp [MulAction.mem_stabilizer_iff, action_zero]
theorem plane_stabilizer_nonzero (x : V) (hx : x ≠ 0) :
    MulAction.stabilizer G x = ⊥ := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
  by_cases hg : Multiplicative.toAdd g = 0
  · have hg1 : g = 1 := by
      apply Multiplicative.toAdd.injective
      simpa using hg
    simp [hg1]
  · constructor
    · intro h
      have hn : -x = x := by simpa [action_apply, epsilon, hg] using h
      apply False.elim
      apply hx
      ext i
      change x i = 0
      have hi := congrFun hn i
      simp only [Pi.neg_apply] at hi
      linarith
    · intro h
      exact (hg (by simp [h])).elim
theorem level_stabilizer_eq_plane (x : Level) :
    MulAction.stabilizer G x = MulAction.stabilizer G x.1 := by
  ext g
  simp only [MulAction.mem_stabilizer_iff, Subtype.ext_iff, level_action_coe]

/-- Actual conjugacy of subgroups. For this abelian group it is equality, proved below. -/
def SubgroupsConjugate (H K : Subgroup G) : Prop :=
  ∃ g : G, ∀ h : G, h ∈ H ↔ conjugation g h ∈ K
theorem subgroups_conjugate_iff (H K : Subgroup G) : SubgroupsConjugate H K ↔ H = K := by
  constructor
  · rintro ⟨g, h⟩
    ext a
    simpa only [conjugation_apply] using h a
  · intro h
    subst K
    exact ⟨1, fun a => by rw [conjugation_apply]⟩
def subgroupConjugacy : Setoid (Subgroup G) where
  r := SubgroupsConjugate
  iseqv := ⟨fun H => (subgroups_conjugate_iff H H).mpr rfl,
    fun {H K} h => (subgroups_conjugate_iff K H).mpr
      ((subgroups_conjugate_iff H K).mp h).symm,
    fun {H K L} h k => (subgroups_conjugate_iff H L).mpr
      (((subgroups_conjugate_iff H K).mp h).trans ((subgroups_conjugate_iff K L).mp k))⟩
abbrev SubgroupClasses := Quotient subgroupConjugacy
def originType : SubgroupClasses := Quotient.mk subgroupConjugacy (⊤ : Subgroup G)
def freeType : SubgroupClasses := Quotient.mk subgroupConjugacy (⊥ : Subgroup G)
theorem subgroup_top_ne_bot : (⊤ : Subgroup G) ≠ ⊥ := by
  intro h
  have hmem : Multiplicative.ofAdd (1 : ZMod 2) ∈ (⊤ : Subgroup G) := trivial
  rw [h, Subgroup.mem_bot] at hmem
  have hbad := congrArg Multiplicative.toAdd hmem
  norm_num at hbad
theorem distinct_types : originType ≠ freeType := by
  intro h
  exact subgroup_top_ne_bot ((subgroups_conjugate_iff _ _).mp (Quotient.exact h))

def isotropyType (x : Level) : SubgroupClasses :=
  Quotient.mk subgroupConjugacy (MulAction.stabilizer G x)
theorem isotropy_origin : isotropyType levelOrigin = originType := by
  simp [isotropyType, level_stabilizer_eq_plane, levelOrigin, plane_stabilizer_zero, originType]
theorem isotropy_axis : isotropyType levelAxis = freeType := by
  simp [isotropyType, level_stabilizer_eq_plane, levelAxis,
    plane_stabilizer_nonzero axis0 axis0_ne_zero, freeType]
theorem isotropy_zero (x : Level) (hx : x.1 = 0) : isotropyType x = originType := by
  simp [isotropyType, level_stabilizer_eq_plane, hx, plane_stabilizer_zero, originType]
theorem isotropy_nonzero (x : Level) (hx : x.1 ≠ 0) : isotropyType x = freeType := by
  simp [isotropyType, level_stabilizer_eq_plane,
    plane_stabilizer_nonzero x.1 hx, freeType]
theorem isotropy_smul (g : G) (x : Level) : isotropyType (g • x) = isotropyType x := by
  by_cases hx : x.1 = 0
  · have hzero : (g • x).1 = 0 := by
      change g • x.1 = 0
      rw [hx, action_zero]
    rw [isotropy_zero x hx, isotropy_zero (g • x) hzero]
  · have hnonzero : (g • x).1 ≠ 0 := by
      change g • x.1 ≠ 0
      exact fun h => hx ((action_zero_iff g x.1).mp h)
    rw [isotropy_nonzero x hx, isotropy_nonzero (g • x) hnonzero]

def reducedIsotropyType : ReducedSpace → SubgroupClasses :=
  Quotient.lift isotropyType (by
    intro x y h
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp h
    rw [← hg]
    exact isotropy_smul g y)
theorem reduced_isotropy_mk (x : Level) :
    reducedIsotropyType (Quotient.mk (MulAction.orbitRel G Level) x) = isotropyType x := rfl

/-- The nonempty orbit-type strata of the genuine zero-level quotient. -/
def isotropyTypes : Set SubgroupClasses := Set.range reducedIsotropyType
def stratum (t : SubgroupClasses) : Set ReducedSpace := {x | reducedIsotropyType x = t}
theorem stratum_nonempty_iff (t : SubgroupClasses) : (stratum t).Nonempty ↔ t ∈ isotropyTypes := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, hx⟩
theorem isotropy_types_eq_pair : isotropyTypes = {originType, freeType} := by
  ext t
  constructor
  · rintro ⟨x, rfl⟩
    induction x using Quotient.inductionOn with
    | _ x =>
      rw [reduced_isotropy_mk]
      by_cases hx : x.1 = 0
      · simp [isotropy_zero x hx]
      · simp [isotropy_nonzero x hx]
  · intro ht
    rcases Set.mem_insert_iff.mp ht with ht | ht
    · exact ⟨Quotient.mk (MulAction.orbitRel G Level) levelOrigin,
        isotropy_origin.trans ht.symm⟩
    · have ht' : t = freeType := Set.mem_singleton_iff.mp ht
      exact ⟨Quotient.mk (MulAction.orbitRel G Level) levelAxis,
        isotropy_axis.trans ht'.symm⟩
theorem isotropy_types_finite : isotropyTypes.Finite := by
  rw [isotropy_types_eq_pair]
  exact Set.toFinite _
theorem isotropy_type_card : isotropyTypes.ncard = 2 := by
  rw [isotropy_types_eq_pair]
  exact Set.ncard_pair distinct_types
theorem action_not_free : ¬ ∀ x : Level, MulAction.stabilizer G x = ⊥ := by
  intro h
  apply subgroup_top_ne_bot
  simpa [level_stabilizer_eq_plane, levelOrigin, plane_stabilizer_zero] using h levelOrigin

theorem counterexample : isotropyTypes.ncard ≠ Nat.card CoadjointOrbits := by
  rw [isotropy_type_card, coadjoint_orbit_card]
  norm_num

end TLMC6034
