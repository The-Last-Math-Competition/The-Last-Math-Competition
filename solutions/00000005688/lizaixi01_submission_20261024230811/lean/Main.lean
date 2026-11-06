import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Rigid.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.CategoryTheory.Groupoid.Discrete
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.RingTheory.Length
import Mathlib.Tactic

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory BigOperators ZeroObject

namespace TLMC5688

abbrev Index := Fin 3
abbrev Vec := FGModuleCat.{0} ℂ

theorem base_algebraically_closed : IsAlgClosed ℂ := inferInstance

instance vectorRigid : RigidCategory Vec :=
  BraidedCategory.rigidCategoryOfRightRigidCategory

/-- All triples of finite-dimensional complex spaces, with every componentwise linear map. -/
abbrev Cat := Discrete Index ⥤ Vec

theorem actual_linear : Nonempty (Linear ℂ Cat) := ⟨inferInstance⟩
theorem actual_abelian : Nonempty (Abelian Cat) := ⟨inferInstance⟩
theorem actual_monoidal : Nonempty (MonoidalCategory Cat) := ⟨inferInstance⟩
theorem actual_rigid : Nonempty (RigidCategory Cat) := ⟨inferInstance⟩

instance tensorAdditive : MonoidalPreadditive Cat where
  whiskerLeft_zero := by intros; apply NatTrans.ext; funext i; exact MonoidalPreadditive.whiskerLeft_zero
  zero_whiskerRight := by intros; apply NatTrans.ext; funext i; exact MonoidalPreadditive.zero_whiskerRight
  whiskerLeft_add := by intros; apply NatTrans.ext; funext i; exact MonoidalPreadditive.whiskerLeft_add _ _
  add_whiskerRight := by intros; apply NatTrans.ext; funext i; exact MonoidalPreadditive.add_whiskerRight _ _

instance tensorLinear : MonoidalLinear ℂ Cat where
  whiskerLeft_smul := by intros; apply NatTrans.ext; funext i; exact MonoidalLinear.whiskerLeft_smul _ _ _
  smul_whiskerRight := by intros; apply NatTrans.ext; funext i; exact MonoidalLinear.smul_whiskerRight _ _ _

theorem actual_tensor_bilinear : Nonempty (MonoidalLinear ℂ Cat) := ⟨inferInstance⟩

def morph {X Y : Cat} (f : ∀ i : Index, X.obj ⟨i⟩ ⟶ Y.obj ⟨i⟩) : X ⟶ Y :=
  Discrete.natTrans (fun i => f i.as)

@[simp] theorem morph_app {X Y : Cat} (f : ∀ i : Index, X.obj ⟨i⟩ ⟶ Y.obj ⟨i⟩)
    (i : Index) : (morph f).app ⟨i⟩ = f i := rfl

def homComponents (X Y : Cat) : (X ⟶ Y) →ₗ[ℂ] (∀ i : Index, X.obj ⟨i⟩ ⟶ Y.obj ⟨i⟩) where
  toFun f i := f.app ⟨i⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance finiteHom (X Y : Cat) : FiniteDimensional ℂ (X ⟶ Y) := by
  apply FiniteDimensional.of_injective (homComponents X Y)
  intro f g h
  apply NatTrans.ext
  funext i
  exact congrFun h i.as

def coord (i : Index) : Cat :=
  Discrete.functor (fun j : Index => if j = i then FGModuleCat.of ℂ ℂ else 0)

@[simp] theorem coord_same (i : Index) : (coord i).obj ⟨i⟩ = FGModuleCat.of ℂ ℂ := by
  simp [coord]

@[simp] theorem coord_other {i j : Index} (h : j ≠ i) : (coord i).obj ⟨j⟩ = 0 := by
  simp [coord,h]

def totalDimension (X : Cat) : ℕ := ∑ i : Index, Module.finrank ℂ (X.obj ⟨i⟩)

theorem unit_dimension : totalDimension (𝟙_ Cat) = 3 := by
  change (∑ _ : Index, Module.finrank ℂ ℂ) = 3
  norm_num

def BasisIndex (X : Cat) := (i : Index) × Fin (Module.finrank ℂ (X.obj ⟨i⟩))

instance basisIndexFinite (X : Cat) : Fintype (BasisIndex X) := inferInstanceAs
  (Fintype ((i : Index) × Fin (Module.finrank ℂ (X.obj ⟨i⟩))))

def fin3Elim {C : Index → Sort*} (c0 : C 0) (c1 : C 1) (c2 : C 2) : ∀ i, C i :=
  Fin.cases c0 (Fin.cases c1 (Fin.cases c2 (fun i => Fin.elim0 i)))

@[simp] theorem fin3Elim_zero {C : Index → Sort*} (c0 : C 0) (c1 : C 1) (c2 : C 2) :
    fin3Elim c0 c1 c2 0 = c0 := rfl
@[simp] theorem fin3Elim_one {C : Index → Sort*} (c0 : C 0) (c1 : C 1) (c2 : C 2) :
    fin3Elim c0 c1 c2 1 = c1 := rfl
@[simp] theorem fin3Elim_two {C : Index → Sort*} (c0 : C 0) (c1 : C 1) (c2 : C 2) :
    fin3Elim c0 c1 c2 2 = c2 := rfl

def morph3 {X Y : Cat} (f0 : X.obj ⟨0⟩ ⟶ Y.obj ⟨0⟩)
    (f1 : X.obj ⟨1⟩ ⟶ Y.obj ⟨1⟩) (f2 : X.obj ⟨2⟩ ⟶ Y.obj ⟨2⟩) : X ⟶ Y :=
  Discrete.natTrans (fun i => fin3Elim (C := fun i => X.obj ⟨i⟩ ⟶ Y.obj ⟨i⟩) f0 f1 f2 i.as)

def inclusion (X : Cat) (a : BasisIndex X) : coord a.1 ⟶ X :=
  fin3Elim (C := fun i => Fin (Module.finrank ℂ (X.obj ⟨i⟩)) → (coord i ⟶ X))
    (fun u => morph3 (FGModuleCat.ofHom (LinearMap.toSpanSingleton ℂ _
      ((Module.finBasis ℂ (X.obj ⟨0⟩)) u))) 0 0)
    (fun u => morph3 0 (FGModuleCat.ofHom (LinearMap.toSpanSingleton ℂ _
      ((Module.finBasis ℂ (X.obj ⟨1⟩)) u))) 0)
    (fun u => morph3 0 0 (FGModuleCat.ofHom (LinearMap.toSpanSingleton ℂ _
      ((Module.finBasis ℂ (X.obj ⟨2⟩)) u)))) a.1 a.2

def projection (X : Cat) (a : BasisIndex X) : X ⟶ coord a.1 :=
  fin3Elim (C := fun i => Fin (Module.finrank ℂ (X.obj ⟨i⟩)) → (X ⟶ coord i))
    (fun u => morph3 (FGModuleCat.ofHom ((Module.finBasis ℂ (X.obj ⟨0⟩)).coord u)) 0 0)
    (fun u => morph3 0 (FGModuleCat.ofHom ((Module.finBasis ℂ (X.obj ⟨1⟩)).coord u)) 0)
    (fun u => morph3 0 0 (FGModuleCat.ofHom ((Module.finBasis ℂ (X.obj ⟨2⟩)).coord u))) a.1 a.2

@[simp] theorem underlying_zero (V W : Vec) : (0 : V ⟶ W).hom.hom = 0 := rfl
@[simp] theorem underlying_ofHom {V W : Vec} (f : V →ₗ[ℂ] W) :
    (FGModuleCat.ofHom f : V ⟶ W).hom.hom = f := rfl

@[simp] theorem underlying_ofHom_unbundled {V W : Type} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
    (f : V →ₗ[ℂ] W) : (FGModuleCat.ofHom f).hom.hom = f := rfl

instance zeroVecSubsingleton : Subsingleton (0 : Vec) := by
  apply ModuleCat.isZero_iff_subsingleton.mp
  exact Functor.map_isZero (forget₂ Vec (ModuleCat ℂ)) (isZero_zero Vec)

@[simp] theorem zeroVec_finrank : Module.finrank ℂ (0 : Vec) = 0 :=
  Module.finrank_zero_of_subsingleton

@[simp] theorem inclusion_00 (X : Cat) (u : Fin (Module.finrank ℂ (X.obj ⟨0⟩))) :
    (inclusion X ⟨0,u⟩).app ⟨0⟩ = FGModuleCat.ofHom
      (LinearMap.toSpanSingleton ℂ _ ((Module.finBasis ℂ (X.obj ⟨0⟩)) u)) := rfl
@[simp] theorem inclusion_11 (X : Cat) (u : Fin (Module.finrank ℂ (X.obj ⟨1⟩))) :
    (inclusion X ⟨1,u⟩).app ⟨1⟩ = FGModuleCat.ofHom
      (LinearMap.toSpanSingleton ℂ _ ((Module.finBasis ℂ (X.obj ⟨1⟩)) u)) := rfl
@[simp] theorem inclusion_22 (X : Cat) (u : Fin (Module.finrank ℂ (X.obj ⟨2⟩))) :
    (inclusion X ⟨2,u⟩).app ⟨2⟩ = FGModuleCat.ofHom
      (LinearMap.toSpanSingleton ℂ _ ((Module.finBasis ℂ (X.obj ⟨2⟩)) u)) := rfl
@[simp] theorem projection_00 (X : Cat) (u : Fin (Module.finrank ℂ (X.obj ⟨0⟩))) :
    (projection X ⟨0,u⟩).app ⟨0⟩ =
      FGModuleCat.ofHom ((Module.finBasis ℂ (X.obj ⟨0⟩)).coord u) := rfl
@[simp] theorem projection_11 (X : Cat) (u : Fin (Module.finrank ℂ (X.obj ⟨1⟩))) :
    (projection X ⟨1,u⟩).app ⟨1⟩ =
      FGModuleCat.ofHom ((Module.finBasis ℂ (X.obj ⟨1⟩)).coord u) := rfl
@[simp] theorem projection_22 (X : Cat) (u : Fin (Module.finrank ℂ (X.obj ⟨2⟩))) :
    (projection X ⟨2,u⟩).app ⟨2⟩ =
      FGModuleCat.ofHom ((Module.finBasis ℂ (X.obj ⟨2⟩)).coord u) := rfl

@[simp] theorem inclusion_other (X : Cat) (a : BasisIndex X) (i : Index) (h : i ≠ a.1) :
    (inclusion X a).app ⟨i⟩ = 0 := by
  rcases a with ⟨j,u⟩
  fin_cases i <;> fin_cases j <;> first | exact False.elim (h rfl) | rfl

@[simp] theorem projection_other (X : Cat) (a : BasisIndex X) (i : Index) (h : i ≠ a.1) :
    (projection X a).app ⟨i⟩ = 0 := by
  rcases a with ⟨j,u⟩
  fin_cases i <;> fin_cases j <;> first | exact False.elim (h rfl) | rfl

open scoped Classical in
theorem basis_diagonal (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (u : Fin (Module.finrank ℂ V)) :
    ((Module.finBasis ℂ V).coord u).comp
      (LinearMap.toSpanSingleton ℂ V ((Module.finBasis ℂ V) u)) = LinearMap.id := by
  ext
  simp [LinearMap.toSpanSingleton]

theorem basis_off_diagonal (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (u v : Fin (Module.finrank ℂ V)) (h : u ≠ v) :
    ((Module.finBasis ℂ V).coord v).comp
      (LinearMap.toSpanSingleton ℂ V ((Module.finBasis ℂ V) u)) = 0 := by
  ext
  simp [LinearMap.toSpanSingleton,Ne.symm h]

open scoped Classical in
theorem inclusion_projection (X : Cat) (a b : BasisIndex X) :
    inclusion X a ≫ projection X b =
      if h : a = b then eqToHom (congrArg (fun a : BasisIndex X => coord a.1) h) else 0 := by
  classical
  by_cases hab : a = b
  · subst b
    rw [dif_pos rfl]
    rcases a with ⟨i,u⟩
    fin_cases i <;>
      (apply NatTrans.ext; funext k; rcases k with ⟨k⟩; fin_cases k <;>
        first
        | (apply FGModuleCat.hom_ext; exact basis_diagonal (X.obj ⟨0⟩) u)
        | (apply FGModuleCat.hom_ext; exact basis_diagonal (X.obj ⟨1⟩) u)
        | (apply FGModuleCat.hom_ext; exact basis_diagonal (X.obj ⟨2⟩) u)
        | (change (0 : (0 : Vec) ⟶ 0) = 𝟙 (0 : Vec); exact (Limits.id_zero (C := Vec)).symm))
  · rw [dif_neg hab]
    rcases a with ⟨i,u⟩
    rcases b with ⟨j,v⟩
    fin_cases i <;> fin_cases j <;>
      (apply NatTrans.ext; funext k; rcases k with ⟨k⟩; fin_cases k <;>
        first
        | (apply FGModuleCat.hom_ext; exact basis_off_diagonal (X.obj ⟨0⟩) u v
            (by intro h; apply hab; subst v; rfl))
        | (apply FGModuleCat.hom_ext; exact basis_off_diagonal (X.obj ⟨1⟩) u v
            (by intro h; apply hab; subst v; rfl))
        | (apply FGModuleCat.hom_ext; exact basis_off_diagonal (X.obj ⟨2⟩) u v
            (by intro h; apply hab; subst v; rfl))
        | simp)

def homAt (X Y : Cat) (i : Index) : (X ⟶ Y) →ₗ[ℂ] (X.obj ⟨i⟩ →ₗ[ℂ] Y.obj ⟨i⟩) where
  toFun f := (f.app ⟨i⟩).hom.hom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem homAt_id (X : Cat) (i : Index) : homAt X X i (𝟙 X) = LinearMap.id := rfl

theorem homAt_injective {X Y : Cat} {f g : X ⟶ Y}
    (h : ∀ i, homAt X Y i f = homAt X Y i g) : f = g := by
    apply NatTrans.ext
    funext k
    rcases k with ⟨k⟩
    exact FGModuleCat.hom_ext (h k)

def basisBicone (X : Cat) : Bicone (fun a : BasisIndex X => coord a.1) where
  pt := X
  π := projection X
  ι := inclusion X
  ι_π := inclusion_projection X

theorem basis_total (X : Cat) :
    ∑ a : BasisIndex X, projection X a ≫ inclusion X a = 𝟙 X := by
  classical
  apply homAt_injective
  intro j
  rw [map_sum,homAt_id]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.sum_apply,LinearMap.id_apply]
  rw [show (∑ a : BasisIndex X, (homAt X X j (projection X a ≫ inclusion X a)) x) =
      ∑ i : Index, ∑ u : Fin (Module.finrank ℂ (X.obj ⟨i⟩)),
        (homAt X X j (projection X ⟨i,u⟩ ≫ inclusion X ⟨i,u⟩)) x from
    Fintype.sum_sigma _]
  fin_cases j <;>
    (simp [homAt,Fin.sum_univ_succ,LinearMap.toSpanSingleton]; first
    | (change (∑ u, (Module.finBasis ℂ (X.obj ⟨0⟩)).repr x u •
        (Module.finBasis ℂ (X.obj ⟨0⟩)) u) = x;
       exact (Module.finBasis ℂ (X.obj ⟨0⟩)).sum_repr x)
    | (change (∑ u, (Module.finBasis ℂ (X.obj ⟨1⟩)).repr x u •
        (Module.finBasis ℂ (X.obj ⟨1⟩)) u) = x;
       exact (Module.finBasis ℂ (X.obj ⟨1⟩)).sum_repr x)
    | (change (∑ u, (Module.finBasis ℂ (X.obj ⟨2⟩)).repr x u •
        (Module.finBasis ℂ (X.obj ⟨2⟩)) u) = x;
       exact (Module.finBasis ℂ (X.obj ⟨2⟩)).sum_repr x))

def basisBilimit (X : Cat) : (basisBicone X).IsBilimit :=
  isBilimitOfTotal (basisBicone X) (basis_total X)

theorem component_injective {X Y : Cat} (f : X ⟶ Y) [Mono f] (i : Index) :
    Function.Injective (homAt X Y i f) := by
  change Function.Injective ((forget₂ Vec (ModuleCat ℂ)).map (f.app ⟨i⟩))
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

def spaceObject (X : Cat) (N : ∀ i : Index, Submodule ℂ (X.obj ⟨i⟩)) : Cat :=
  Discrete.functor (fun i => FGModuleCat.of ℂ (N i))

def spaceArrow (X : Cat) (N : ∀ i : Index, Submodule ℂ (X.obj ⟨i⟩)) : spaceObject X N ⟶ X :=
  morph (fun i => FGModuleCat.ofHom (N i).subtype)

instance spaceArrowMono (X : Cat) (N : ∀ i : Index, Submodule ℂ (X.obj ⟨i⟩)) :
    Mono (spaceArrow X N) := by
  have h : ∀ i : Discrete Index, Mono ((spaceArrow X N).app i) := fun i =>
    ConcreteCategory.mono_of_injective _ Subtype.val_injective
  exact NatTrans.mono_of_mono_app _

def spaces (X : Cat) (S : Subobject X) : ∀ i : Index, Submodule ℂ (X.obj ⟨i⟩) :=
  fun i => LinearMap.range (homAt (S : Cat) X i S.arrow)

def spaceSubobject (X : Cat) (N : ∀ i : Index, Submodule ℂ (X.obj ⟨i⟩)) : Subobject X :=
  Subobject.mk (spaceArrow X N)

def rangeIso (X : Cat) (S : Subobject X) : (S : Cat) ≅ spaceObject X (spaces X S) :=
  Discrete.natIso (fun i => LinearEquiv.toFGModuleCatIso
    (LinearEquiv.ofInjective (homAt (S : Cat) X i.as S.arrow)
      (component_injective S.arrow i.as)))

theorem subobject_eq_spaceSubobject (X : Cat) (S : Subobject X) :
    S = spaceSubobject X (spaces X S) := by
  apply Subobject.eq_mk_of_comm (spaceArrow X (spaces X S)) (rangeIso X S)
  apply homAt_injective
  intro i
  apply LinearMap.ext
  intro x
  rfl

theorem spaces_spaceSubobject (X : Cat) (N : ∀ i : Index, Submodule ℂ (X.obj ⟨i⟩)) :
    spaces X (spaceSubobject X N) = N := by
  funext i
  unfold spaces spaceSubobject
  rw [← Subobject.underlyingIso_hom_comp_eq_mk (spaceArrow X N)]
  change LinearMap.range ((N i).subtype.comp
    (FGModuleCat.isoToLinearEquiv
      ((Subobject.underlyingIso (spaceArrow X N)).app ⟨i⟩)).toLinearMap) = N i
  rw [LinearEquiv.range_comp, Submodule.range_subtype]

theorem spaces_mono {X : Cat} {S T : Subobject X} (h : S ≤ T) : spaces X S ≤ spaces X T := by
  intro i
  rw [spaces, ← Subobject.ofLE_arrow h]
  exact LinearMap.range_comp_le_range _ _

theorem spaceSubobject_mono (X : Cat) {N M : ∀ i : Index, Submodule ℂ (X.obj ⟨i⟩)}
    (h : N ≤ M) : spaceSubobject X N ≤ spaceSubobject X M := by
  apply Subobject.mk_le_mk_of_comm (morph (fun i => FGModuleCat.ofHom (Submodule.inclusion (h i))))
  apply homAt_injective
  intro i
  rfl

/-- The actual categorical subobjects are precisely triples of actual vector subspaces. -/
def subobjectSpaces (X : Cat) : Subobject X ≃o (∀ i : Index, Submodule ℂ (X.obj ⟨i⟩)) where
  toFun := spaces X
  invFun := spaceSubobject X
  left_inv S := (subobject_eq_spaceSubobject X S).symm
  right_inv := spaces_spaceSubobject X
  map_rel_iff' := by
    intro S T
    constructor
    · intro h
      change spaces X S ≤ spaces X T at h
      have hh := spaceSubobject_mono X h
      rw [← subobject_eq_spaceSubobject X S, ← subobject_eq_spaceSubobject X T] at hh
      exact hh
    · exact spaces_mono

theorem coord_space_eq {i j : Index} (h : j ≠ i)
    (N M : Submodule ℂ ((coord i).obj ⟨j⟩)) : N = M := by
  have : Subsingleton ((coord i).obj ⟨j⟩) := by rw [coord_other h]; infer_instance
  exact Subsingleton.elim _ _

theorem coord_spaces_simple (i : Index) :
    IsSimpleOrder (∀ j : Index, Submodule ℂ ((coord i).obj ⟨j⟩)) := by
  have : IsSimpleOrder (Submodule ℂ ((coord i).obj ⟨i⟩)) := by
    rw [coord_same]
    infer_instance
  refine { exists_pair_ne := ⟨⊥,⊤,?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrFun h i)
  · intro N
    rcases eq_bot_or_eq_top (N i) with h | h
    · left
      funext j
      by_cases hj : j = i
      · subst j; exact h
      · exact coord_space_eq hj _ _
    · right
      funext j
      by_cases hj : j = i
      · subst j; exact h
      · exact coord_space_eq hj _ _

instance coordSimple (i : Index) : Simple (coord i) := by
  have := coord_spaces_simple i
  have : IsSimpleOrder (Subobject (coord i)) :=
    (OrderIso.isSimpleOrder_iff (subobjectSpaces (coord i))).mpr inferInstance
  exact simple_of_isSimpleOrder_subobject _

theorem coord_dimension (i : Index) : totalDimension (coord i) = 1 := by
  unfold totalDimension
  rw [Finset.sum_eq_single i]
  · rw [coord_same]; simp
  · intro j _ hji
    rw [coord_other hji]
    simp
  · simp

theorem coord_noniso {i j : Index} (h : i ≠ j) : ¬Nonempty (coord i ≅ coord j) := by
  rintro ⟨e⟩
  have he := (FGModuleCat.isoToLinearEquiv (e.app ⟨i⟩)).finrank_eq
  rw [coord_same,coord_other h] at he
  simp at he

theorem inclusion_nonzero (X : Cat) (a : BasisIndex X) : inclusion X a ≠ 0 := by
  intro h
  have he := inclusion_projection X a a
  rw [h,zero_comp,dif_pos rfl,eqToHom_refl] at he
  exact id_nonzero (coord a.1) he.symm

theorem simple_has_basis (X : Cat) [Simple X] : Nonempty (BasisIndex X) := by
  by_contra h
  have : IsEmpty (BasisIndex X) := not_nonempty_iff.mp h
  have he := basis_total X
  simp only [Finset.univ_eq_empty,Finset.sum_empty] at he
  exact id_nonzero X he.symm

theorem all_simples_are_coordinates (X : Cat) [Simple X] :
    ∃ i : Index, Nonempty (coord i ≅ X) := by
  obtain ⟨a⟩ := simple_has_basis X
  have : IsIso (inclusion X a) := isIso_of_hom_simple (inclusion_nonzero X a)
  exact ⟨a.1,⟨asIso (inclusion X a)⟩⟩

/-- A genuine finite simple biproduct decomposition for every object of the category. -/
theorem finite_simple_decomposition (X : Cat) :
    (∀ a : BasisIndex X, Simple (coord a.1)) ∧ Nonempty (basisBicone X).IsBilimit :=
  ⟨fun _ => inferInstance, ⟨basisBilimit X⟩⟩

def simpleIsoSetoid : Setoid {X : Cat // Simple X} where
  r X Y := Nonempty (X.1 ≅ Y.1)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun h => h.map Iso.symm,
    fun h k => h.elim (fun e => k.map e.trans)⟩

abbrev SimpleClasses := Quotient simpleIsoSetoid

def coordinateClass (i : Index) : SimpleClasses :=
  Quotient.mk _ ⟨coord i,inferInstance⟩

theorem coordinateClass_bijective : Function.Bijective coordinateClass := by
  constructor
  · intro i j h
    by_contra hij
    exact coord_noniso hij (Quotient.exact h)
  · intro q
    induction q using Quotient.inductionOn with
    | _ X =>
      have : Simple X.1 := X.2
      obtain ⟨i,⟨e⟩⟩ := all_simples_are_coordinates X.1
      exact ⟨i,Quotient.sound ⟨e⟩⟩

instance simpleClassesFinite : Finite SimpleClasses :=
  Finite.of_surjective coordinateClass coordinateClass_bijective.2

theorem three_simple_classes : Nat.card SimpleClasses = 3 := by
  simpa [Index] using
    (Nat.card_congr (Equiv.ofBijective coordinateClass coordinateClass_bijective)).symm

theorem totalDimension_iso {X Y : Cat} (e : X ≅ Y) : totalDimension X = totalDimension Y := by
  apply Finset.sum_congr rfl
  intro i _
  exact (FGModuleCat.isoToLinearEquiv (e.app ⟨i⟩)).finrank_eq

theorem unit_not_simple : ¬Simple (𝟙_ Cat) := by
  intro h
  obtain ⟨i,⟨e⟩⟩ := all_simples_are_coordinates (𝟙_ Cat)
  have he := totalDimension_iso e
  rw [coord_dimension,unit_dimension] at he
  omega

instance subobjectModular (X : Cat) : IsModularLattice (Subobject X) where
  sup_inf_le_assoc_of_le := by
    intro x y z h
    apply (subobjectSpaces X).le_iff_le.mp
    simp only [map_inf,map_sup]
    intro i
    exact IsModularLattice.sup_inf_le_assoc_of_le _ ((subobjectSpaces X).monotone h i)

def spacesDimension (X : Cat) (N : ∀ i : Index, Submodule ℂ (X.obj ⟨i⟩)) : ℕ :=
  ∑ i, Module.finrank ℂ (N i)

theorem spacesDimension_strictMono (X : Cat) : StrictMono (spacesDimension X) := by
  intro N M h
  have hex : ∃ i, N i < M i := by
    by_contra hh
    push Not at hh
    apply h.ne
    funext i
    by_contra hne
    exact hh i (lt_of_le_of_ne (h.le i) hne)
  obtain ⟨i,hi⟩ := hex
  apply Finset.sum_lt_sum (fun j _ => Submodule.finrank_mono (h.le j))
  exact ⟨i,Finset.mem_univ i,Submodule.finrank_lt_finrank_of_lt hi⟩

theorem spacesDimension_le (X : Cat) (N : ∀ i : Index, Submodule ℂ (X.obj ⟨i⟩)) :
    spacesDimension X N ≤ totalDimension X :=
  Finset.sum_le_sum (fun i _ => Submodule.finrank_le (N i))

theorem subobject_chain_length_bound (X : Cat) (s : LTSeries (Subobject X)) :
    s.length ≤ totalDimension X := by
  let q : LTSeries ℕ := s.map (fun S => spacesDimension X (subobjectSpaces X S))
    ((spacesDimension_strictMono X).comp (subobjectSpaces X).strictMono)
  have hq := q.head_add_length_le_nat
  have hb := spacesDimension_le X (subobjectSpaces X s.last)
  change q.head + s.length ≤ spacesDimension X (subobjectSpaces X s.last) at hq
  omega

theorem all_objects_finite_length (X : Cat) : FiniteDimensionalOrder (Subobject X) := by
  apply not_infiniteDimensionalOrder_iff.mp
  intro h
  have := h
  obtain ⟨s,hs⟩ := SetRel.InfiniteDimensional.exists_relSeries_with_length
    (r := {(a,b) : Subobject X × Subobject X | a < b}) (totalDimension X + 1)
  have hb := subobject_chain_length_bound X s
  omega

def unitSpacesBool : (∀ i : Index, Submodule ℂ ((𝟙_ Cat).obj ⟨i⟩)) ≃o (Index → Bool) := by
  classical
  haveI : ∀ i : Index, IsSimpleOrder (Submodule ℂ ((𝟙_ Cat).obj ⟨i⟩)) := by
    intro i
    change IsSimpleOrder (Submodule ℂ ℂ)
    infer_instance
  exact
    { toFun := fun N i => IsSimpleOrder.orderIsoBool (N i)
      invFun := fun b i => IsSimpleOrder.orderIsoBool.symm (b i)
      left_inv := fun N => funext (fun _ => OrderIso.symm_apply_apply _ _)
      right_inv := fun b => funext (fun _ => OrderIso.apply_symm_apply _ _)
      map_rel_iff' := fun {N M} => by
        change (∀ i, IsSimpleOrder.orderIsoBool (N i) ≤ IsSimpleOrder.orderIsoBool (M i)) ↔ N ≤ M
        simp only [OrderIso.le_iff_le]
        rfl }

def unitSubobjectsBool : Subobject (𝟙_ Cat) ≃o (Index → Bool) :=
  (subobjectSpaces (𝟙_ Cat)).trans unitSpacesBool

def booleanFlag (j : Fin 4) : Index → Bool := fun i => decide (i.val < j.val)

theorem booleanFlag_cover (j : Fin 3) : booleanFlag j.castSucc ⋖ booleanFlag j.succ := by
  rw [Pi.covBy_iff]
  refine ⟨j,?_,?_⟩
  · simp [booleanFlag,Bool.covBy_iff]
  · intro i hij
    have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    by_cases h : i.val < j.val
    · have h' : i.val < j.val + 1 := by omega
      simp [booleanFlag,h,h']
    · have h' : ¬i.val < j.val + 1 := by omega
      simp [booleanFlag,h,h']

def booleanSeries : CompositionSeries (Index → Bool) where
  length := 3
  toFun := booleanFlag
  step := booleanFlag_cover

theorem booleanSeries_head : booleanSeries.head = ⊥ := by
  funext i
  simp [booleanSeries,booleanFlag,RelSeries.head]

theorem booleanSeries_last : booleanSeries.last = ⊤ := by
  funext i
  simp [booleanSeries,booleanFlag,RelSeries.last,i.isLt]

theorem cover_orderIso {A B : Type*} [PartialOrder A] [PartialOrder B]
    (e : A ≃o B) {a b : A} (h : a ⋖ b) : e a ⋖ e b := by
  refine ⟨e.strictMono h.lt,?_⟩
  intro c hac hcb
  exact h.2 (by simpa using e.symm.strictMono hac) (by simpa using e.symm.strictMono hcb)

def unitSeries : CompositionSeries (Subobject (𝟙_ Cat)) where
  length := booleanSeries.length
  toFun j := unitSubobjectsBool.symm (booleanSeries j)
  step j := cover_orderIso unitSubobjectsBool.symm (booleanSeries.step j)

theorem unitSeries_head : unitSeries.head = ⊥ := by
  change unitSubobjectsBool.symm booleanSeries.head = ⊥
  rw [booleanSeries_head]
  exact unitSubobjectsBool.symm.map_bot

theorem unitSeries_last : unitSeries.last = ⊤ := by
  change unitSubobjectsBool.symm booleanSeries.last = ⊤
  rw [booleanSeries_last]
  exact unitSubobjectsBool.symm.map_top

theorem unitSeries_length : unitSeries.length = 3 := rfl

/-- Every complete native composition series of the actual tensor unit has length three. -/
theorem unit_composition_length (s : CompositionSeries (Subobject (𝟙_ Cat)))
    (h0 : s.head = ⊥) (h1 : s.last = ⊤) : s.length = 3 := by
  have h := (s.jordan_holder unitSeries (h0.trans unitSeries_head.symm)
    (h1.trans unitSeries_last.symm)).length_eq
  exact h.trans unitSeries_length

theorem no_length_two_unit :
    ¬∃ s : CompositionSeries (Subobject (𝟙_ Cat)), s.head = ⊥ ∧ s.last = ⊤ ∧ s.length = 2 := by
  rintro ⟨s,h0,h1,h2⟩
  have h3 := unit_composition_length s h0 h1
  omega

def unitBasisPoint (i : Index) : BasisIndex (𝟙_ Cat) :=
  ⟨i,⟨0,by change 0 < Module.finrank ℂ ℂ; simp⟩⟩

def unitBasisEquiv : BasisIndex (𝟙_ Cat) ≃ Index where
  toFun a := a.1
  invFun := unitBasisPoint
  left_inv := by
    rintro ⟨i,u⟩
    dsimp only [unitBasisPoint]
    have hu := u.isLt
    change u.val < Module.finrank ℂ ℂ at hu
    norm_num at hu
    have hu0 : u = ⟨0,by change 0 < Module.finrank ℂ ℂ; simp⟩ := by
      apply Fin.ext
      exact hu
    rw [hu0]
  right_inv _ := rfl

def unitBicone : Bicone coord where
  pt := 𝟙_ Cat
  π i := projection (𝟙_ Cat) (unitBasisPoint i)
  ι i := inclusion (𝟙_ Cat) (unitBasisPoint i)
  ι_π := by
    intro i j
    classical
    have h := inclusion_projection (𝟙_ Cat) (unitBasisPoint i) (unitBasisPoint j)
    by_cases hij : i = j
    · subst j; simpa [unitBasisPoint] using h
    · have hp : unitBasisPoint i ≠ unitBasisPoint j := fun hh => hij (congrArg Sigma.fst hh)
      rw [dif_neg hp] at h
      rw [dif_neg hij]
      exact h

theorem unitBicone_total : ∑ i : Index, unitBicone.π i ≫ unitBicone.ι i = 𝟙 (𝟙_ Cat) := by
  classical
  have h : (∑ i : Index, projection (𝟙_ Cat) (unitBasisPoint i) ≫
      inclusion (𝟙_ Cat) (unitBasisPoint i)) =
      ∑ a : BasisIndex (𝟙_ Cat), projection (𝟙_ Cat) a ≫ inclusion (𝟙_ Cat) a :=
    Fintype.sum_equiv unitBasisEquiv.symm _ _ (fun _ => rfl)
  exact h.trans (basis_total (𝟙_ Cat))

def unitBilimit : unitBicone.IsBilimit := isBilimitOfTotal unitBicone unitBicone_total

instance unitHasBiproduct : HasBiproduct coord := hasBiproduct_of_total unitBicone unitBicone_total

def unitBiproductIso : (𝟙_ Cat) ≅ ⨁ coord := biproduct.uniqueUpToIso coord unitBilimit

theorem component_surjective {X Y : Cat} (f : X ⟶ Y) [Epi f] (i : Index) :
    Function.Surjective (homAt X Y i f) := by
  change Function.Surjective ((forget₂ Vec (ModuleCat ℂ)).map (f.app ⟨i⟩))
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

instance everyObjectProjective (P : Cat) : Projective P where
  factors {E X} f e _ := by
    let l : ∀ i : Index, P.obj ⟨i⟩ →ₗ[ℂ] E.obj ⟨i⟩ := fun i =>
      (Module.projective_lifting_property (homAt E X i e) (homAt P X i f)
        (component_surjective e i)).choose
    refine ⟨morph (fun i => FGModuleCat.ofHom (l i)),?_⟩
    apply homAt_injective
    intro i
    exact (Module.projective_lifting_property (homAt E X i e) (homAt P X i f)
      (component_surjective e i)).choose_spec

instance actualEnoughProjectives : EnoughProjectives Cat where
  presentation X := ⟨{ p := X, f := 𝟙 X }⟩

/-- Refutation of only the printed universal unit-length-two clause. -/
theorem printed_unit_length_two_false :
    Nonempty (Linear ℂ Cat) ∧ Nonempty (Abelian Cat) ∧
    Nonempty (RigidCategory Cat) ∧ Nonempty (MonoidalLinear ℂ Cat) ∧
    (∀ X Y : Cat, FiniteDimensional ℂ (X ⟶ Y)) ∧
    (∀ X : Cat, (∀ a : BasisIndex X, Simple (coord a.1)) ∧
      Nonempty (basisBicone X).IsBilimit) ∧
    (∀ X : Cat, FiniteDimensionalOrder (Subobject X)) ∧
    Nat.card SimpleClasses = 3 ∧ ¬Simple (𝟙_ Cat) ∧
    Nonempty ((𝟙_ Cat) ≅ ⨁ coord) ∧
    (unitSeries.head = ⊥ ∧ unitSeries.last = ⊤ ∧ unitSeries.length = 3) ∧
    ¬∃ s : CompositionSeries (Subobject (𝟙_ Cat)),
      s.head = ⊥ ∧ s.last = ⊤ ∧ s.length = 2 :=
  ⟨actual_linear,actual_abelian,actual_rigid,actual_tensor_bilinear,
    fun _ _ => inferInstance,finite_simple_decomposition,all_objects_finite_length,
    three_simple_classes,unit_not_simple,⟨unitBiproductIso⟩,
    ⟨unitSeries_head,unitSeries_last,unitSeries_length⟩,no_length_two_unit⟩

end TLMC5688
