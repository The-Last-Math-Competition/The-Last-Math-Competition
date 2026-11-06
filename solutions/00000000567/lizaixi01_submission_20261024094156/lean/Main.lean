import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Idempotents.Biproducts
import Mathlib.CategoryTheory.Idempotents.FunctorCategories
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleModule.Rank
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

/-!
The ordinary finite-dimensional representation category of the arrowless A1
quiver and its actual Karoubi envelope.  This is not the derived orbit cluster
category.  Both object-isomorphism counting and the basic-object convention
will be kept explicit.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.Idempotents
open scoped BigOperators

namespace TLMC567

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

inductive Vertex where
  | point
  deriving DecidableEq

instance vertex_unique : Unique Vertex where
  default := .point
  uniq x := by cases x; rfl

instance vertex_fintype : Fintype Vertex := Fintype.ofFinite Vertex

instance a1_quiver : Quiver.{0} Vertex where
  Hom _ _ := PEmpty

abbrev A1Path := Paths Vertex
abbrev Vect := FGModuleCat.{0} ℂ
abbrev Rep := A1Path ⥤ Vect
abbrev Envelope := Karoubi Rep

def point : A1Path := Vertex.point

theorem vertex_count : Fintype.card Vertex = 1 := Fintype.card_unique

theorem no_arrows (a b : Vertex) : IsEmpty (a ⟶ b) := by
  change IsEmpty PEmpty
  infer_instance

theorem path_is_identity (p : point ⟶ point) : p = 𝟙 point := by
  cases p with
  | nil => rfl
  | cons q e => exact PEmpty.elim e

def evaluate : Rep ⥤ Vect := (evaluation A1Path Vect).obj point

def constant : Vect ⥤ Rep := Functor.const A1Path

def representationUnit (F : Rep) : F ≅ constant.obj (evaluate.obj F) :=
  NatIso.ofComponents (fun j => by
    cases j
    exact Iso.refl _) (by
      intro a b f
      cases a
      cases b
      have hf : f = 𝟙 point := path_is_identity f
      subst f
      simp [constant, evaluate, point])

def representationEquivalence : Rep ≌ Vect where
  functor := evaluate
  inverse := constant
  unitIso := NatIso.ofComponents representationUnit (by
    intro F G f
    ext j
    cases j
    rfl)
  counitIso := Iso.refl _

def envelopeEquivalence : Envelope ≌ Vect :=
  (toKaroubiEquivalence Rep).symm.trans representationEquivalence

abbrev realize (P : Envelope) : Vect := envelopeEquivalence.functor.obj P

instance rep_finite_biproducts : HasFiniteBiproducts Rep :=
  HasFiniteBiproducts.of_hasFiniteProducts

instance envelope_finite_products : HasFiniteProducts Envelope := by
  haveI : HasFiniteBiproducts Envelope := inferInstance
  exact hasFiniteProducts_of_hasFiniteBiproducts Envelope

instance envelope_abelian : Abelian Envelope :=
  abelianOfEquivalence envelopeEquivalence.functor

theorem finite_vector_epi_surjective {M N : Vect} (f : M ⟶ N) [Epi f] :
    Function.Surjective f.hom.hom := by
  haveI : Epi ((forget₂ Vect (ModuleCat.{0} ℂ)).map f) := inferInstance
  exact (ModuleCat.epi_iff_surjective ((forget₂ Vect (ModuleCat.{0} ℂ)).map f)).mp
    inferInstance

instance vector_projective (M : Vect) : Projective M where
  factors := by
    intro E X f e he
    obtain ⟨g, hg⟩ := Module.projective_lifting_property e.hom.hom f.hom.hom
      (finite_vector_epi_surjective e)
    exact ⟨FGModuleCat.ofHom g, by
      apply FGModuleCat.hom_ext
      exact hg⟩

instance envelope_projective (P : Envelope) : Projective P := by
  have h : Projective (envelopeEquivalence.inverse.obj (realize P)) :=
    envelopeEquivalence.inverse.projective_obj (realize P)
  exact Projective.of_iso (envelopeEquivalence.unitIso.app P).symm h

instance envelope_enough_projectives : EnoughProjectives Envelope where
  presentation P := ⟨{ p := P, f := 𝟙 P }⟩

instance envelope_has_ext : HasExt.{0} Envelope :=
  hasExt_of_enoughProjectives.{0} Envelope

theorem envelope_ext_vanishes (P Q : Envelope) (e : Ext P Q 1) : e = 0 :=
  Ext.eq_zero_of_projective e

def standard (n : ℕ) : Envelope :=
  (toKaroubi Rep).obj (constant.obj (FGModuleCat.of ℂ (Fin n → ℂ)))

def standardRealization (n : ℕ) : realize (standard n) ≅ FGModuleCat.of ℂ (Fin n → ℂ) :=
  envelopeEquivalence.counitIso.app _

theorem standard_dimension (n : ℕ) : Module.finrank ℂ (realize (standard n)) = n := by
  rw [(FGModuleCat.isoToLinearEquiv (standardRealization n)).finrank_eq]
  simp

theorem standard_nonisomorphic {m n : ℕ} (e : standard m ≅ standard n) : m = n := by
  have h := (FGModuleCat.isoToLinearEquiv (envelopeEquivalence.functor.mapIso e)).finrank_eq
  simpa only [standard_dimension] using h

abbrev dimension (P : Envelope) : ℕ := Module.finrank ℂ (realize P)

def underlying : Envelope ⥤ ModuleCat.{0} ℂ :=
  envelopeEquivalence.functor ⋙ forget₂ Vect (ModuleCat.{0} ℂ)

instance realization_additive : envelopeEquivalence.functor.Additive := by
  exact Functor.additive_of_preserves_binary_products envelopeEquivalence.functor

instance underlying_faithful : underlying.Faithful := by
  dsimp [underlying]
  infer_instance

instance underlying_additive : underlying.Additive := by
  dsimp [underlying]
  infer_instance

instance underlying_preserves_binary_biproducts : PreservesBinaryBiproducts underlying :=
  preservesBinaryBiproducts_of_preservesBinaryProducts underlying

def classifyObject (P : Envelope) : P ≅ standard (dimension P) :=
  envelopeEquivalence.unitIso.app P ≪≫
    envelopeEquivalence.inverse.mapIso
      (Module.finBasis ℂ (realize P)).equivFun.toFGModuleCatIso

theorem isZero_iff_subsingleton (P : Envelope) : IsZero P ↔ Subsingleton (realize P) := by
  constructor
  · intro h
    apply ModuleCat.isZero_iff_subsingleton.mp
    apply (IsZero.iff_id_eq_zero (underlying.obj P)).mpr
    simpa only [underlying.map_id, underlying.map_zero] using
      congrArg underlying.map ((IsZero.iff_id_eq_zero P).mp h)
  · intro h
    letI : Subsingleton (underlying.obj P) := h
    apply (IsZero.iff_id_eq_zero P).mpr
    apply underlying.map_injective
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _

theorem isZero_iff_dimension_zero (P : Envelope) : IsZero P ↔ dimension P = 0 := by
  rw [isZero_iff_subsingleton]
  exact (Module.finrank_zero_iff (R := ℂ) (M := realize P)).symm

def realizationBiproduct {n : ℕ} (S : Fin n → Envelope) :
    underlying.obj (⨁ S) ≅ ModuleCat.of ℂ (∀ i, realize (S i)) :=
  Functor.mapBiproduct underlying S ≪≫ ModuleCat.biproductIsoPi (fun i => underlying.obj (S i))

theorem dimension_biproduct {n : ℕ} (S : Fin n → Envelope) :
    dimension (⨁ S) = ∑ i, dimension (S i) := by
  have h := (realizationBiproduct S).toLinearEquiv.finrank_eq
  change Module.finrank ℂ (realize (⨁ S)) = Module.finrank ℂ (∀ i, realize (S i)) at h
  exact h.trans (Module.finrank_pi_fintype ℂ)

theorem dimension_biprod (P Q : Envelope) : dimension (P ⊞ Q) = dimension P + dimension Q := by
  let e := Functor.mapBiprod underlying P Q ≪≫ ModuleCat.biprodIsoProd (underlying.obj P) (underlying.obj Q)
  have h := e.toLinearEquiv.finrank_eq
  change Module.finrank ℂ (realize (P ⊞ Q)) =
    Module.finrank ℂ ((realize P) × (realize Q)) at h
  exact h.trans Module.finrank_prod

def finiteCopies (P : Envelope) (n : ℕ) : Envelope := ⨁ fun _ : Fin n => P

def InAdd (T P : Envelope) : Prop :=
  ∃ n : ℕ, Nonempty (Retract P (finiteCopies T n))

def Rigid (T : Envelope) : Prop := ∀ e : Ext T T 1, e = 0

def MaximalRigid (T : Envelope) : Prop :=
  Rigid T ∧ ∀ P : Envelope, Rigid P → InAdd P T → InAdd T P

def ClusterTilting (T : Envelope) : Prop :=
  ∀ P : Envelope,
    (InAdd T P ↔ ∀ e : Ext T P 1, e = 0) ∧
    (InAdd T P ↔ ∀ e : Ext P T 1, e = 0)

theorem all_objects_rigid (T : Envelope) : Rigid T := envelope_ext_vanishes T T

theorem clusterTilting_iff_generates (T : Envelope) : ClusterTilting T ↔ ∀ P, InAdd T P := by
  constructor
  · intro h P
    exact (h P).1.mpr (envelope_ext_vanishes T P)
  · intro h P
    exact ⟨⟨fun _ => envelope_ext_vanishes T P, fun _ => h P⟩,
      ⟨fun _ => envelope_ext_vanishes P T, fun _ => h P⟩⟩

theorem clusterTilting_maximalRigid {T : Envelope} (h : ClusterTilting T) : MaximalRigid T :=
  ⟨all_objects_rigid T, fun P _ _ => (clusterTilting_iff_generates T).mp h P⟩

theorem dimension_iso {P Q : Envelope} (e : P ≅ Q) : dimension P = dimension Q :=
  (FGModuleCat.isoToLinearEquiv (envelopeEquivalence.functor.mapIso e)).finrank_eq

def isoOfDimensionEq {P Q : Envelope} (h : dimension P = dimension Q) : P ≅ Q :=
  classifyObject P ≪≫ eqToIso (congrArg standard h) ≪≫ (classifyObject Q).symm

def coordinateInclude {m n : ℕ} (_h : m ≤ n) : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi fun j => if hj : j.val < m then LinearMap.proj ⟨j.val, hj⟩ else 0

def coordinateProject {m n : ℕ} (h : m ≤ n) : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
  LinearMap.pi fun i => LinearMap.proj (Fin.castLE h i)

theorem coordinate_split {m n : ℕ} (h : m ≤ n) :
    (coordinateProject h).comp (coordinateInclude h) = LinearMap.id := by
  ext x i
  simp [coordinateProject, coordinateInclude, i.isLt]

def standardMap {m n : ℕ} (f : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :
    standard m ⟶ standard n :=
  (toKaroubi Rep).map (constant.map (FGModuleCat.ofHom f))

theorem standardMap_comp {l m n : ℕ} (f : (Fin l → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (g : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :
    standardMap f ≫ standardMap g = standardMap (g.comp f) := by
  simp only [standardMap, ← Functor.map_comp]
  rfl

theorem standardMap_id (n : ℕ) : standardMap (LinearMap.id (R := ℂ) (M := Fin n → ℂ)) = 𝟙 _ := by
  change (toKaroubi Rep).map (constant.map (𝟙 _)) = 𝟙 _
  simp

def standardRetract {m n : ℕ} (h : m ≤ n) : Retract (standard m) (standard n) where
  i := standardMap (coordinateInclude h)
  r := standardMap (coordinateProject h)
  retract := by rw [standardMap_comp, coordinate_split, standardMap_id]

def retractOfDimensionLE {P Q : Envelope} (h : dimension P ≤ dimension Q) : Retract P Q :=
  (Retract.ofIso (classifyObject P)).trans
    ((standardRetract h).trans (Retract.ofIso (classifyObject Q).symm))

theorem retract_dimension_le {P Q : Envelope} (r : Retract P Q) : dimension P ≤ dimension Q := by
  let i := (underlying.map r.i).hom
  let p := (underlying.map r.r).hom
  have h : p.comp i = LinearMap.id := by
    have hr := congrArg (fun f => (underlying.map f).hom) r.retract
    rw [underlying.map_comp, underlying.map_id] at hr
    exact hr
  have hi : Function.Injective i := (show Function.LeftInverse p i from
    fun x => LinearMap.congr_fun h x).injective
  exact LinearMap.finrank_le_finrank_of_injective hi

theorem dimension_finiteCopies (T : Envelope) (n : ℕ) :
    dimension (finiteCopies T n) = n * dimension T := by
  simp [finiteCopies, dimension_biproduct, smul_eq_mul]

theorem nonzero_generates {T : Envelope} (hT : ¬ IsZero T) (P : Envelope) : InAdd T P := by
  have hd : 0 < dimension T := Nat.pos_of_ne_zero
    (fun h => hT ((isZero_iff_dimension_zero T).mpr h))
  refine ⟨dimension P, ⟨retractOfDimensionLE ?_⟩⟩
  rw [dimension_finiteCopies]
  simpa using Nat.mul_le_mul_left (dimension P) (Nat.succ_le_of_lt hd)

theorem standard_one_nonzero : ¬ IsZero (standard 1) := by
  intro h
  have := (isZero_iff_dimension_zero (standard 1)).mp h
  norm_num only [dimension, standard_dimension] at this

theorem zero_cannot_generate_one {T : Envelope} (hT : IsZero T) : ¬ InAdd T (standard 1) := by
  rintro ⟨n, ⟨r⟩⟩
  have h := retract_dimension_le r
  rw [dimension_finiteCopies, (isZero_iff_dimension_zero T).mp hT] at h
  norm_num only [dimension, standard_dimension, Nat.mul_zero] at h

theorem clusterTilting_iff_nonzero (T : Envelope) : ClusterTilting T ↔ ¬ IsZero T := by
  rw [clusterTilting_iff_generates]
  exact ⟨fun h hz => zero_cannot_generate_one hz (h (standard 1)),
    fun h => nonzero_generates h⟩

theorem maximalRigid_iff_nonzero (T : Envelope) : MaximalRigid T ↔ ¬ IsZero T := by
  constructor
  · intro h hz
    apply zero_cannot_generate_one hz
    exact h.2 (standard 1) (all_objects_rigid _) (nonzero_generates standard_one_nonzero T)
  · intro h
    exact clusterTilting_maximalRigid ((clusterTilting_iff_nonzero T).mpr h)

@[simp] theorem dimension_standard (n : ℕ) : dimension (standard n) = n := standard_dimension n

def Indecomposable (P : Envelope) : Prop :=
  ¬ IsZero P ∧ ∀ A B : Envelope, Nonempty (P ≅ A ⊞ B) → IsZero A ∨ IsZero B

theorem indecomposable_iff_dimension_one (P : Envelope) :
    Indecomposable P ↔ dimension P = 1 := by
  constructor
  · intro h
    have hpos : 0 < dimension P := Nat.pos_of_ne_zero
      (fun hz => h.1 ((isZero_iff_dimension_zero P).mpr hz))
    by_contra hn
    have htwo : 2 ≤ dimension P := by omega
    let e : P ≅ standard 1 ⊞ standard (dimension P - 1) := isoOfDimensionEq (by
      rw [dimension_biprod, dimension_standard, dimension_standard]
      omega)
    rcases h.2 _ _ ⟨e⟩ with ha | hb
    · exact standard_one_nonzero ha
    · have hb0 := (isZero_iff_dimension_zero _).mp hb
      rw [dimension_standard] at hb0
      omega
  · intro h
    refine ⟨fun hz => ?_, fun A B he => ?_⟩
    · have := (isZero_iff_dimension_zero P).mp hz
      omega
    · obtain ⟨e⟩ := he
      have hd := dimension_iso e
      rw [dimension_biprod, h] at hd
      have hz : dimension A = 0 ∨ dimension B = 0 := by omega
      exact hz.imp (isZero_iff_dimension_zero A).mpr (isZero_iff_dimension_zero B).mpr

def Basic (P : Envelope) : Prop :=
  ∃ (n : ℕ) (S : Fin n → Envelope),
    (∀ i, Indecomposable (S i)) ∧
    (Pairwise fun i j => ¬ Nonempty (S i ≅ S j)) ∧ Nonempty (P ≅ ⨁ S)

theorem basic_iff_dimension_le_one (P : Envelope) : Basic P ↔ dimension P ≤ 1 := by
  constructor
  · rintro ⟨n, S, hi, hp, ⟨e⟩⟩
    have hd : dimension P = n := by
      have h := (dimension_iso e).trans (dimension_biproduct S)
      have hs : ∀ i, dimension (S i) = 1 := fun i =>
        (indecomposable_iff_dimension_one (S i)).mp (hi i)
      simpa only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
        mul_one] using h
    rw [hd]
    by_contra hn
    have htwo : 2 ≤ n := by omega
    let i : Fin n := ⟨0, by omega⟩
    let j : Fin n := ⟨1, by omega⟩
    have hij : i ≠ j := by
      intro h
      have := congrArg Fin.val h
      change 0 = 1 at this
      omega
    apply hp hij
    exact ⟨isoOfDimensionEq
      (((indecomposable_iff_dimension_one _).mp (hi i)).trans
        ((indecomposable_iff_dimension_one _).mp (hi j)).symm)⟩
  · intro h
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with hz | ho
    · let S : Fin 0 → Envelope := Fin.elim0
      refine ⟨0, S, fun i => Fin.elim0 i, ?_, ⟨isoOfDimensionEq ?_⟩⟩
      · intro i
        exact Fin.elim0 i
      · rw [hz, dimension_biproduct]
        simp
    · let S : Fin 1 → Envelope := fun _ => P
      refine ⟨1, S, fun _ => (indecomposable_iff_dimension_one P).mpr ho, ?_,
        ⟨(biproductUniqueIso S).symm⟩⟩
      intro i j hij
      exact (hij (Subsingleton.elim i j)).elim

theorem standard_one_basic : Basic (standard 1) :=
  (basic_iff_dimension_le_one _).mpr (by simp)

theorem basic_maximalRigid_dimension {P : Envelope} (h : MaximalRigid P ∧ Basic P) :
    dimension P = 1 := by
  have hpos : 0 < dimension P := Nat.pos_of_ne_zero
    (fun hz => ((maximalRigid_iff_nonzero P).mp h.1) ((isZero_iff_dimension_zero P).mpr hz))
  have hle := (basic_iff_dimension_le_one P).mp h.2
  omega

def objectSetoid (p : Envelope → Prop) : Setoid {P : Envelope // p P} where
  r P Q := Nonempty (P.val ≅ Q.val)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩,
    fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩⟩

abbrev AllClasses := Quotient (objectSetoid MaximalRigid)
abbrev BasicClasses := Quotient (objectSetoid fun P => MaximalRigid P ∧ Basic P)

theorem standard_positive_clusterTilting (n : ℕ) : ClusterTilting (standard (n + 1)) := by
  apply (clusterTilting_iff_nonzero _).mpr
  intro hz
  have := (isZero_iff_dimension_zero _).mp hz
  simp only [dimension_standard] at this
  omega

def allClass (n : ℕ) : AllClasses :=
  Quotient.mk _ ⟨standard (n + 1), clusterTilting_maximalRigid (standard_positive_clusterTilting n)⟩

theorem allClass_injective : Function.Injective allClass := by
  intro m n h
  obtain ⟨e⟩ := Quotient.exact h
  have := standard_nonisomorphic e
  omega

instance allClasses_infinite : Infinite AllClasses := Infinite.of_injective allClass allClass_injective

instance basicClasses_subsingleton : Subsingleton BasicClasses where
  allEq a b := by
    induction a using Quotient.inductionOn with | h P =>
      induction b using Quotient.inductionOn with | h Q =>
        apply Quotient.sound
        exact ⟨isoOfDimensionEq
          ((basic_maximalRigid_dimension P.property).trans
            (basic_maximalRigid_dimension Q.property).symm)⟩

instance basicClasses_nonempty : Nonempty BasicClasses :=
  ⟨Quotient.mk _ ⟨standard 1,
    clusterTilting_maximalRigid (standard_positive_clusterTilting 0), standard_one_basic⟩⟩

theorem basic_class_count : Nat.card BasicClasses = 1 := Nat.card_unique

theorem full_class_count_not_finite (n : ℕ) : ¬ Nonempty (AllClasses ≃ Fin n) := by
  rintro ⟨e⟩
  letI : Finite AllClasses := Finite.of_equiv (Fin n) e.symm
  exact not_finite AllClasses

instance evaluate_isEquivalence : evaluate.IsEquivalence :=
  inferInstanceAs representationEquivalence.functor.IsEquivalence

def evaluatedIdempotent (P : Envelope) : Module.End ℂ (P.X.obj point) :=
  (P.p.app point).hom.hom

theorem evaluatedIdempotent_idem (P : Envelope) (x : P.X.obj point) :
    evaluatedIdempotent P (evaluatedIdempotent P x) = evaluatedIdempotent P x := by
  have h := congr_app P.idem point
  exact congrArg (fun f => f.hom.hom x) h

def imageVector (P : Envelope) : Vect :=
  FGModuleCat.of ℂ (LinearMap.range (evaluatedIdempotent P))

def imageRepresentation (P : Envelope) : Rep := constant.obj (imageVector P)

def imageProjection (P : Envelope) : P.X ⟶ imageRepresentation P :=
  evaluate.preimage (FGModuleCat.ofHom (evaluatedIdempotent P).rangeRestrict)

def imageInclusion (P : Envelope) : imageRepresentation P ⟶ P.X :=
  evaluate.preimage (FGModuleCat.ofHom (LinearMap.range (evaluatedIdempotent P)).subtype)

theorem projection_idempotent (P : Envelope) : P.p ≫ imageProjection P = imageProjection P := by
  apply evaluate.map_injective
  simp only [Functor.map_comp, imageProjection, Functor.map_preimage]
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact evaluatedIdempotent_idem P x

theorem inclusion_idempotent (P : Envelope) : imageInclusion P ≫ P.p = imageInclusion P := by
  apply evaluate.map_injective
  simp only [Functor.map_comp, imageInclusion, Functor.map_preimage]
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change evaluatedIdempotent P x.val = x.val
  obtain ⟨y, hy⟩ := x.property
  rw [← hy]
  exact evaluatedIdempotent_idem P y

theorem image_projection_inclusion (P : Envelope) :
    imageProjection P ≫ imageInclusion P = P.p := by
  apply evaluate.map_injective
  simp only [Functor.map_comp, imageProjection, imageInclusion, Functor.map_preimage]
  rfl

theorem image_inclusion_projection (P : Envelope) :
    imageInclusion P ≫ imageProjection P = 𝟙 (imageRepresentation P) := by
  apply evaluate.map_injective
  simp only [Functor.map_comp, imageProjection, imageInclusion, Functor.map_preimage,
    ]
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change evaluatedIdempotent P x.val = x.val
  obtain ⟨y, hy⟩ := x.property
  rw [← hy]
  exact evaluatedIdempotent_idem P y

def explicitImageIso (P : Envelope) : P ≅ (toKaroubi Rep).obj (imageRepresentation P) where
  hom := ⟨imageProjection P, by simpa using projection_idempotent P⟩
  inv := ⟨imageInclusion P, by simpa using inclusion_idempotent P⟩
  hom_inv_id := by
    apply Karoubi.hom_ext
    exact image_projection_inclusion P
  inv_hom_id := by
    apply Karoubi.hom_ext
    exact image_inclusion_projection P

def rootValue (b : Bool) : ℂ := if b then -1 else 1

def corootValue (b : Bool) : Module.Dual ℂ ℂ :=
  (2 * rootValue b) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)

def rootSwap : Equiv.Perm Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b <;> rfl

def a1Roots : RootPairing Bool ℂ ℂ (Module.Dual ℂ ℂ) where
  toLinearMap := Module.Dual.eval ℂ ℂ
  root := ⟨rootValue, by
    intro a b h
    cases a <;> cases b <;> norm_num [rootValue] at *⟩
  coroot := ⟨corootValue, by
    intro a b h
    have h1 := congrArg (fun f : Module.Dual ℂ ℂ => f 1) h
    cases a <;> cases b <;> norm_num [corootValue, rootValue] at *⟩
  root_coroot_two := by
    intro b
    cases b <;> norm_num [rootValue, corootValue]
  reflectionPerm _ := rootSwap
  reflectionPerm_root := by
    intro a b
    cases a <;> cases b <;> norm_num [rootValue, corootValue, rootSwap, smul_eq_mul]
  reflectionPerm_coroot := by
    intro a b
    cases a <;> cases b <;> apply LinearMap.ext <;> intro x <;>
      simp [rootValue, corootValue, rootSwap, smul_eq_mul] <;> ring

instance a1_root_system : a1Roots.IsRootSystem where
  span_root_eq_top := by
    apply top_le_iff.mp
    intro x _
    have h : (1 : ℂ) ∈ Submodule.span ℂ (Set.range a1Roots.root) :=
      Submodule.subset_span ⟨false, rfl⟩
    simpa only [smul_eq_mul, mul_one] using
      (Submodule.span ℂ (Set.range a1Roots.root)).smul_mem x h
  span_coroot_eq_top := by
    apply top_le_iff.mp
    intro f _
    have h : corootValue false ∈ Submodule.span ℂ (Set.range a1Roots.coroot) :=
      Submodule.subset_span ⟨false, rfl⟩
    have hf : (f 1 / 2) • corootValue false ∈
        Submodule.span ℂ (Set.range a1Roots.coroot) :=
      (Submodule.span ℂ (Set.range a1Roots.coroot)).smul_mem _ h
    convert hf using 1
    apply LinearMap.ext
    intro x
    have hx : f x = x * f 1 := by
      simpa only [smul_eq_mul, mul_one] using f.map_smul x (1 : ℂ)
    rw [hx]
    simp only [corootValue, rootValue, Bool.false_eq_true, ↓reduceIte,
      LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    field_simp

theorem a1_roots_explicit (b : Bool) : a1Roots.root b = 1 ∨ a1Roots.root b = -1 := by
  cases b <;> simp [a1Roots, rootValue]

def a1Base : a1Roots.Base where
  support := {false}
  linearIndepOn_root := by
    simp [a1Roots, rootValue]
  linearIndepOn_coroot := by
    rw [Finset.coe_singleton, linearIndepOn_singleton_iff]
    intro h
    have h1 := congrArg (fun f : Module.Dual ℂ ℂ => f 1) h
    norm_num [a1Roots, corootValue, rootValue] at h1
  root_mem_or_neg_mem b := by
    have h : a1Roots.root false ∈
        AddSubmonoid.closure (a1Roots.root '' (↑({false} : Finset Bool) : Set Bool)) :=
      AddSubmonoid.subset_closure ⟨false, by simp, rfl⟩
    cases b
    · exact Or.inl h
    · exact Or.inr (by simpa [a1Roots, rootValue] using h)
  coroot_mem_or_neg_mem b := by
    have h : a1Roots.coroot false ∈
        AddSubmonoid.closure (a1Roots.coroot '' (↑({false} : Finset Bool) : Set Bool)) :=
      AddSubmonoid.subset_closure ⟨false, by simp, rfl⟩
    cases b
    · exact Or.inl h
    · exact Or.inr (by simpa [a1Roots, corootValue, rootValue] using h)

theorem root_base_rank_is_quiver_rank : a1Base.support.card = Fintype.card Vertex := by
  simp [a1Base]

def simpleIndex : Vertex ≃ a1Base.support where
  toFun _ := ⟨false, by simp [a1Base]⟩
  invFun _ := Vertex.point
  left_inv v := Subsingleton.elim _ _
  right_inv i := by
    apply Subtype.ext
    exact (Finset.mem_singleton.mp
      (show i.val ∈ ({false} : Finset Bool) from i.property)).symm

def rootBasis : Module.Basis Vertex ℂ ℂ := Module.Basis.singleton Vertex ℂ

theorem rootBasis_is_simple (v : Vertex) :
    rootBasis v = a1Roots.root (simpleIndex v).val := by
  simp [rootBasis, simpleIndex, a1Roots, rootValue]

theorem a1_cartan_entry : a1Roots.pairing false false = 2 := by
  norm_num [RootPairing.pairing, RootPairing.root', a1Roots, rootValue, corootValue]

@[simp] theorem a1_reflection_apply (x : ℂ) : a1Roots.reflection false x = -x := by
  simp [RootPairing.reflection_apply, RootPairing.coroot', a1Roots, rootValue,
    corootValue, smul_eq_mul]
  ring

def coxeterElement : ℂ ≃ₗ[ℂ] ℂ :=
  (List.ofFn fun i : Fin (Fintype.card Vertex) =>
    a1Roots.reflection (simpleIndex ((Fintype.equivFin Vertex).symm i)).val).prod

theorem coxeter_element_reflection : coxeterElement = a1Roots.reflection false := by
  simp [coxeterElement, simpleIndex, List.ofFn_succ]

@[simp] theorem coxeterElement_apply (x : ℂ) : coxeterElement x = -x := by
  rw [coxeter_element_reflection]
  exact a1_reflection_apply x

def coxeterNumber : ℕ := orderOf coxeterElement

theorem coxeter_number_eq_two : coxeterNumber = 2 := by
  apply orderOf_eq_prime
  · ext x
    change coxeterElement (coxeterElement x) = x
    simp
  · intro h
    have h1 := congrArg (fun f : ℂ ≃ₗ[ℂ] ℂ => f 1) h
    norm_num at h1

theorem coxeter_primitive_root : IsPrimitiveRoot (-1 : ℂ) coxeterNumber := by
  rw [coxeter_number_eq_two]
  exact IsPrimitiveRoot.neg_one 0 (by decide)

theorem coxeter_eigenvalue_iff (μ : ℂ) :
    Module.End.HasEigenvalue coxeterElement.toLinearMap μ ↔ μ = -1 := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    have he := hv.apply_eq_smul
    change coxeterElement v = μ * v at he
    apply mul_right_cancel₀ hv.2
    simpa using he.symm
  · rintro rfl
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := (1 : ℂ))
    refine ⟨?_, one_ne_zero⟩
    apply Module.End.mem_eigenspace_iff.mpr
    simp

theorem coxeter_eigenspace_full :
    Module.End.eigenspace coxeterElement.toLinearMap (-1 : ℂ) = ⊤ := by
  ext x
  simp [smul_eq_mul]

def coxeterExponents : Finset ℕ := by
  classical
  exact (Finset.range coxeterNumber).filter fun e =>
    Module.End.HasEigenvalue coxeterElement.toLinearMap ((-1 : ℂ) ^ e)

theorem coxeter_exponents_eq : coxeterExponents = {1} := by
  classical
  ext e
  simp only [coxeterExponents, Finset.mem_filter, Finset.mem_range,
    coxeter_number_eq_two, coxeter_eigenvalue_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨he, hv⟩
    have h : e = 0 ∨ e = 1 := by omega
    rcases h with rfl | rfl
    · norm_num at hv
    · rfl
  · rintro rfl
    norm_num

theorem exponent_count_is_rank : coxeterExponents.card = Fintype.card Vertex := by
  rw [coxeter_exponents_eq, Finset.card_singleton, vertex_count]

def predictedCount : ℚ :=
  ∏ e ∈ coxeterExponents, ((coxeterNumber : ℚ) + e + 1) / ((e : ℚ) + 1)

theorem predicted_count_two : predictedCount = 2 := by
  rw [predictedCount, coxeter_exponents_eq, Finset.prod_singleton, coxeter_number_eq_two]
  norm_num

theorem basic_count_not_predicted : (Nat.card BasicClasses : ℚ) ≠ predictedCount := by
  rw [basic_class_count, predicted_count_two]
  norm_num

theorem complete_counterexample :
    Infinite AllClasses ∧ Nat.card BasicClasses = 1 ∧ predictedCount = 2 ∧
      (Nat.card BasicClasses : ℚ) ≠ predictedCount ∧
      (∀ n : ℕ, ¬ Nonempty (AllClasses ≃ Fin n)) ∧
      (∀ n : ℕ, ClusterTilting (standard (n + 1))) :=
  ⟨inferInstance, basic_class_count, predicted_count_two, basic_count_not_predicted,
    full_class_count_not_finite, standard_positive_clusterTilting⟩

end

end TLMC567
