import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.Module.GradedModule
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped BigOperators

set_option maxHeartbeats 1200000

noncomputable section
namespace TLMC561

abbrev V := Fin 2 → ℚ
abbrev A := TrivSqZeroExt ℚ V

instance residueAlgebra : Algebra A ℚ := TrivSqZeroExt.algebraBase ℚ V

def epsilon (a : Fin 2) : A := TrivSqZeroExt.inr (Pi.single a 1)

@[simp] theorem epsilon_fst (a : Fin 2) : (epsilon a).fst = 0 := rfl

@[simp] theorem epsilon_mul_epsilon (a b : Fin 2) : epsilon a * epsilon b = 0 :=
  TrivSqZeroExt.inr_mul_inr _ _ _

@[simp] theorem mul_snd (x y : A) (a : Fin 2) :
    (x * y).snd a = x.fst * y.snd a + x.snd a * y.fst := by
  simp [TrivSqZeroExt.snd_mul, Pi.smul_apply, smul_eq_mul, mul_comm]

def component (n : ℕ) : Submodule ℚ A :=
  if n = 0 then (TrivSqZeroExt.sndHom ℚ V).ker
  else if n = 1 then (TrivSqZeroExt.fstHom ℚ ℚ V).toLinearMap.ker else ⊥

@[simp] theorem mem_component_zero (x : A) : x ∈ component 0 ↔ x.snd = 0 := by
  simp [component]

@[simp] theorem mem_component_one (x : A) : x ∈ component 1 ↔ x.fst = 0 := by
  simp [component]

@[simp] theorem component_add_two (n : ℕ) : component (n + 2) = ⊥ := by
  simp [component, Nat.add_eq_zero_iff]

instance componentMonoid : SetLike.GradedMonoid component where
  one_mem := by simp
  mul_mem := by
    intro i j x y hx hy
    obtain (_ | _ | i) := i <;> obtain (_ | _ | j) := j
    all_goals simp only [Nat.zero_add, Nat.add_zero, Nat.reduceAdd,
      mem_component_zero, mem_component_one, component_add_two, Submodule.mem_bot] at hx hy ⊢
    all_goals try { subst x; simp }
    all_goals try { subst y; simp }
    · ext a
      simp [mul_snd, hx, hy]
    · simp [TrivSqZeroExt.fst_mul, hy]
    · simp [TrivSqZeroExt.fst_mul, hx]
    · apply TrivSqZeroExt.ext
      · simp [hx, hy]
      · ext a
        simp [mul_snd, hx, hy]

def splitZero (x : A) : component 0 := ⟨TrivSqZeroExt.inl x.fst, by simp⟩
def splitOne (x : A) : component 1 := ⟨TrivSqZeroExt.inr x.snd, by simp⟩

@[simp] theorem splitZero_zero : splitZero 0 = 0 := by apply Subtype.ext; simp [splitZero]
@[simp] theorem splitOne_zero : splitOne 0 = 0 := by apply Subtype.ext; simp [splitOne]

def decompositionMap : A →+ DirectSum ℕ (fun n => ↥(component n)) where
  toFun x := DirectSum.of (fun n => component n) 0 (splitZero x) +
    DirectSum.of (fun n => component n) 1 (splitOne x)
  map_zero' := by simp
  map_add' x y := by
    have h0 : splitZero (x + y) = splitZero x + splitZero y := by apply Subtype.ext; simp [splitZero]
    have h1 : splitOne (x + y) = splitOne x + splitOne y := by apply Subtype.ext; simp [splitOne]
    simp only [h0, h1, map_add]
    abel

theorem decomposition_homogeneous (n : ℕ) (x : component n) :
    decompositionMap x = DirectSum.of (fun n => component n) n x := by
  obtain (_ | _ | n) := n
  · have hx : x.val.snd = 0 := (mem_component_zero x).1 x.property
    have h0 : splitZero x = x := by apply Subtype.ext; exact TrivSqZeroExt.ext rfl hx.symm
    have h1 : splitOne x = 0 := by apply Subtype.ext; simp [splitOne, hx]
    simp [decompositionMap, h0, h1]
  · have hx : x.val.fst = 0 := (mem_component_one x).1 x.property
    have h0 : splitZero x = 0 := by apply Subtype.ext; simp [splitZero, hx]
    have h1 : splitOne x = x := by apply Subtype.ext; exact TrivSqZeroExt.ext hx.symm rfl
    simp [decompositionMap, h0, h1]
  · have hx : x.val = 0 := by simpa using x.property
    have : x = 0 := Subtype.ext hx
    subst x
    simp

instance actualDecomposition : DirectSum.Decomposition component :=
  DirectSum.Decomposition.ofAddHom component decompositionMap
    (by
      apply AddMonoidHom.ext
      intro x
      change DirectSum.coeAddMonoidHom component
        (DirectSum.of _ 0 (splitZero x) + DirectSum.of _ 1 (splitOne x)) = x
      simp only [map_add, DirectSum.coeAddMonoidHom_of]
      exact x.inl_fst_add_inr_snd_eq)
    (by ext n x : 2; simpa using decomposition_homogeneous n x)

instance actualGradedAlgebra : GradedAlgebra component := { componentMonoid, actualDecomposition with }

def connectedEquiv : ℚ ≃ₗ[ℚ] component 0 where
  toFun q := ⟨TrivSqZeroExt.inl q, by simp⟩
  invFun x := x.val.fst
  left_inv q := rfl
  right_inv x := by
    apply Subtype.ext
    exact TrivSqZeroExt.ext rfl ((mem_component_zero x).1 x.property).symm
  map_add' _ _ := by apply Subtype.ext; simp
  map_smul' _ _ := by ext <;> simp

theorem degree_one_generators (x : component 1) :
    (x : A) = ∑ a : Fin 2, x.val.snd a • epsilon a := by
  apply TrivSqZeroExt.ext
  · simpa using (mem_component_one x).1 x.property
  · ext a
    fin_cases a <;> simp [epsilon, Fin.sum_univ_two]

@[reducible] def Word : ℕ → Type
  | 0 => PUnit
  | n + 1 => Fin 2 × Word n

instance wordFintype : (n : ℕ) → Fintype (Word n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => by unfold Word; letI := wordFintype n; infer_instance

instance wordDecidableEq : (n : ℕ) → DecidableEq (Word n)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | n + 1 => by unfold Word; letI := wordDecidableEq n; infer_instance

theorem word_card (n : ℕ) : Fintype.card (Word n) = 2 ^ n := by
  induction n with
  | zero => simp only [pow_zero]; exact Fintype.card_unique
  | succ n ih =>
    change Fintype.card (Fin 2 × Word n) = _
    rw [Fintype.card_prod, Fintype.card_fin, ih, pow_succ, mul_comm]

abbrev P (n : ℕ) := Word n → A

def differential (n : ℕ) : P (n + 1) →ₗ[A] P n where
  toFun f w := ∑ a : Fin 2, epsilon a * f (a, w)
  map_add' f g := by funext w; simp [mul_add, Finset.sum_add_distrib]
  map_smul' r f := by
    funext w
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact mul_left_comm _ _ _

@[simp] theorem differential_fst (n : ℕ) (f : P (n + 1)) (w : Word n) :
    (differential n f w).fst = 0 := by simp [differential, Fin.sum_univ_two]

@[simp] theorem differential_snd (n : ℕ) (f : P (n + 1)) (w : Word n) (a : Fin 2) :
    (differential n f w).snd a = (f (a, w)).fst := by
  fin_cases a <;> simp [differential, Fin.sum_univ_two, epsilon]

theorem differential_kernel (n : ℕ) (f : P (n + 1)) :
    differential n f = 0 ↔ ∀ w, (f w).fst = 0 := by
  constructor
  · intro h w
    obtain ⟨a, w⟩ := w
    have := congrArg (fun z : P n => (z w).snd a) h
    rw [← differential_snd n f w a]
    exact this
  · intro h
    funext w
    apply TrivSqZeroExt.ext
    · exact differential_fst n f w
    · ext a
      rw [differential_snd, h]
      rfl

theorem differential_range (n : ℕ) (f : P n) :
    (∃ g, differential n g = f) ↔ ∀ w, (f w).fst = 0 := by
  constructor
  · rintro ⟨g, rfl⟩ w
    exact differential_fst n g w
  · intro h
    refine ⟨fun z => TrivSqZeroExt.inl ((f z.2).snd z.1), ?_⟩
    funext w
    apply TrivSqZeroExt.ext
    · rw [differential_fst, h]
    · ext a
      rw [differential_snd]
      rfl

theorem differential_square (n : ℕ) :
    (differential n).comp (differential (n + 1)) = 0 := by
  apply LinearMap.ext
  intro f
  exact (differential_kernel n _).2 (fun w => differential_fst _ _ _)

def augmentation : P 0 →ₗ[A] ℚ where
  toFun f := (f PUnit.unit).fst
  map_add' _ _ := rfl
  map_smul' r f := by
    change (r * f PUnit.unit).fst = r.fst * (f PUnit.unit).fst
    rfl

theorem augmentation_surjective : Function.Surjective augmentation := by
  intro q
  exact ⟨fun _ => TrivSqZeroExt.inl q, rfl⟩

theorem augmentation_differential : augmentation.comp (differential 0) = 0 := by
  apply LinearMap.ext
  intro f
  exact differential_fst 0 f PUnit.unit

theorem exact_augmentation (f : P 0) (hf : augmentation f = 0) :
    ∃ g, differential 0 g = f := by
  apply (differential_range 0 f).2
  intro w
  have : w = PUnit.unit := Subsingleton.elim _ _
  subst w
  exact hf

@[reducible] def resolutionComplex : ChainComplex (ModuleCat A) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of A (P n))
    (fun n => ModuleCat.ofHom (differential n))
    (fun n => ModuleCat.hom_ext (differential_square n))

@[simp] theorem resolutionComplex_d (n : ℕ) :
    resolutionComplex.d (n + 1) n = ModuleCat.ofHom (differential n) := by
  simp [resolutionComplex]

set_option backward.isDefEq.respectTransparency false in
theorem complex_exact (n : ℕ) : resolutionComplex.ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff _).2
  intro f hf
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', ChainComplex.of_d] at hf ⊢
  change differential n f = 0 at hf
  obtain ⟨g, hg⟩ := (differential_range (n + 1) f).2 ((differential_kernel n f).1 hf)
  refine ⟨g, ?_⟩
  simpa [ChainComplex.of.d] using hg

abbrev residue : ModuleCat A := ModuleCat.of A ℚ

def augmentationMap : resolutionComplex ⟶ (ChainComplex.single₀ (ModuleCat A)).obj residue :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨ModuleCat.ofHom augmentation, by
    simpa using ModuleCat.hom_ext augmentation_differential⟩

@[simp] theorem augmentationMap_f_zero : augmentationMap.f 0 = ModuleCat.ofHom augmentation := rfl

instance augmentationMap_epi : Epi (augmentationMap.f 0) :=
  (ModuleCat.epi_iff_surjective _).2 augmentation_surjective

@[reducible] def resolution : ProjectiveResolution residue where
  complex := resolutionComplex
  projective n := ModuleCat.projective_of_free (Pi.basisFun A (Word n))
  π := augmentationMap
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff]
      rw [ShortComplex.quasiIso_iff_of_zeros' _ (by rfl) (by
        change ((ChainComplex.single₀ (ModuleCat A)).obj residue).d 1 0 = 0
        simp only [HomologicalComplex.single_obj_d]) (by rfl)]
      constructor
      · apply (ShortComplex.moduleCat_exact_iff _).2
        simp only [HomologicalComplex.shortComplexFunctor',
          augmentationMap_f_zero]
        exact exact_augmentation
      · change Epi (ModuleCat.ofHom augmentation)
        exact (ModuleCat.epi_iff_surjective _).2 augmentation_surjective
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact complex_exact n
      · apply ChainComplex.exactAt_succ_single_obj⟩

open scoped ModuleCat.Algebra

@[simp] theorem epsilon_smul_residue (a : Fin 2) (q : ℚ) : epsilon a • q = 0 := by
  change 0 * q = 0
  exact zero_mul q

theorem hom_differential_zero (n : ℕ)
    (f : ModuleCat.of A (P n) ⟶ residue) :
    ModuleCat.ofHom (differential n) ≫ f = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hd : differential n x = ∑ a : Fin 2, epsilon a • (fun w => x (a, w)) := by
    funext w
    simp [differential]
  change f.hom (differential n x) = 0
  rw [hd, map_sum]
  apply Finset.sum_eq_zero
  intro a _
  rw [map_smul]
  exact epsilon_smul_residue a _

def cochainFromCoordinates (n : ℕ) (c : Word n → ℚ) :
    ModuleCat.of A (P n) ⟶ residue := ModuleCat.ofHom
  { toFun := fun f => ∑ w, (f w).fst * c w
    map_add' := by intros; simp [add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro r f
      change (∑ w, (r * f w).fst * c w) = r.fst * ∑ w, (f w).fst * c w
      simp [TrivSqZeroExt.fst_mul, Finset.mul_sum, mul_assoc] }

@[simp] theorem cochainFromCoordinates_single (n : ℕ) (c : Word n → ℚ) (w : Word n) :
    cochainFromCoordinates n c (Pi.single w 1) = c w := by
  classical
  change (∑ v, ((Pi.single w 1 : P n) v).fst * c v) = c w
  simp [Pi.single_apply, apply_ite]

theorem cochain_reconstruction (n : ℕ) (f : ModuleCat.of A (P n) ⟶ residue) :
    cochainFromCoordinates n (fun w => f (Pi.single w 1)) = f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx : ∑ w, x w • (Pi.single w 1 : P n) = x := by
    funext v
    simp [Pi.single_apply]
  change (∑ w, (x w).fst * f (Pi.single w 1)) = f x
  calc
    _ = f.hom (∑ w, x w • (Pi.single w 1 : P n)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro w _
      rw [map_smul]
      rfl
    _ = f x := congrArg f.hom hx

def cochainCoordinateEquiv (n : ℕ) :
    (ModuleCat.of A (P n) ⟶ residue) ≃ₗ[ℚ] (Word n → ℚ) where
  toFun f w := f (Pi.single w 1)
  invFun := cochainFromCoordinates n
  left_inv := cochain_reconstruction n
  right_inv c := by funext w; exact cochainFromCoordinates_single n c w
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def extFromCochain (n : ℕ) :
    (ModuleCat.of A (P n) ⟶ residue) →ₗ[ℚ] Ext.{0} residue residue n where
  toFun f := resolution.extMk f (n + 1) rfl (by
    change resolutionComplex.d (n + 1) n ≫ f = 0
    rw [resolutionComplex_d]
    exact hom_differential_zero n f)
  map_add' f g := (resolution.add_extMk f g (n + 1) rfl _ _).symm
  map_smul' r f := by
    simp only [RingHom.id_apply]
    rw [Ext.smul_eq_comp_mk₀, resolution.extMk_comp_mk₀]
    congr 1

theorem extFromCochain_surjective (n : ℕ) : Function.Surjective (extFromCochain n) := by
  intro x
  obtain ⟨f, hf, h⟩ := resolution.extMk_surjective x (n + 1) rfl
  exact ⟨f, h⟩

theorem extFromCochain_succ_injective (n : ℕ) :
    Function.Injective (extFromCochain (n + 1)) := by
  apply (LinearMap.ker_eq_bot).1
  apply (Submodule.eq_bot_iff _).2
  intro f hf
  have hz : resolution.complex.d (n + 2) (n + 1) ≫ f = 0 := by
    rw [resolutionComplex_d]
    exact hom_differential_zero _ f
  change resolution.extMk f (n + 2) rfl hz = 0 at hf
  obtain ⟨g, hg⟩ := (resolution.extMk_eq_zero_iff f (n + 2) rfl hz n rfl).1 hf
  have hg0 := hom_differential_zero n g
  change resolutionComplex.d (n + 1) n ≫ g = f at hg
  rw [resolutionComplex_d] at hg
  exact hg.symm.trans hg0

def positiveExtEquiv (n : ℕ) : Ext.{0} residue residue (n + 1) ≃ₗ[ℚ] (Word (n + 1) → ℚ) :=
  (LinearEquiv.ofBijective (extFromCochain (n + 1))
    ⟨extFromCochain_succ_injective n, extFromCochain_surjective _⟩).symm.trans
      (cochainCoordinateEquiv (n + 1))

def residueEndFromScalar (q : ℚ) : residue ⟶ residue := ModuleCat.ofHom
  { toFun := fun x => q * x
    map_add' := fun _ _ => mul_add _ _ _
    map_smul' := by intro r x; change q * (r.fst * x) = r.fst * (q * x); ring }

def residueEndEquiv : (residue ⟶ residue) ≃ₗ[ℚ] ℚ where
  toFun f := f 1
  invFun := residueEndFromScalar
  left_inv f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx := f.hom.map_smul (TrivSqZeroExt.inl x : A) (1 : ℚ)
    change f (x * 1) = x * f 1 at hx
    change f 1 * x = f x
    simpa [mul_comm] using hx.symm
  right_inv q := mul_one q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def zeroExtEquiv : Ext.{0} residue residue 0 ≃ₗ[ℚ] ℚ :=
  Ext.linearEquiv₀.trans residueEndEquiv

instance extFinite (n : ℕ) : Module.Finite ℚ (Ext.{0} residue residue n) := by
  cases n with
  | zero => exact Module.Finite.equiv zeroExtEquiv.symm
  | succ n => exact Module.Finite.equiv (positiveExtEquiv n).symm

theorem ext_finrank (n : ℕ) : Module.finrank ℚ (Ext.{0} residue residue n) = 2 ^ n := by
  cases n with
  | zero => simpa using zeroExtEquiv.finrank_eq
  | succ n =>
    rw [(positiveExtEquiv n).finrank_eq, Module.finrank_pi]
    simp [word_card, pow_succ, mul_comm]

abbrev Free := FreeAlgebra ℚ (Fin 2)

def quadraticRelations (x y : Free) : Prop :=
  ∃ a b : Fin 2, x = FreeAlgebra.ι ℚ a * FreeAlgebra.ι ℚ b ∧ y = 0

abbrev Presented := RingQuot quadraticRelations

def generator (a : Fin 2) : Presented :=
  RingQuot.mkAlgHom ℚ quadraticRelations (FreeAlgebra.ι ℚ a)

@[simp] theorem generator_mul (a b : Fin 2) : generator a * generator b = 0 := by
  have h := RingQuot.mkAlgHom_rel ℚ (s := quadraticRelations) ⟨a, b, rfl, rfl⟩
  simpa only [generator, map_mul, map_zero] using h

def presentedRadical : V →ₗ[ℚ] Presented where
  toFun v := ∑ a, v a • generator a
  map_add' _ _ := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' _ _ := by simp [smul_smul]

theorem presentedRadical_square (v w : V) : presentedRadical v * presentedRadical w = 0 := by
  change (∑ a, v a • generator a) * (∑ b, w b • generator b) = 0
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro b _
  rw [smul_mul_assoc, mul_smul_comm, generator_mul]
  simp

def toPresented : A →ₐ[ℚ] Presented :=
  TrivSqZeroExt.lift (Algebra.ofId ℚ Presented) presentedRadical presentedRadical_square
    (by intro r v; exact (presentedRadical.map_smul r v).trans (Algebra.smul_def r _))
    (by
      intro r v
      rw [op_smul_eq_smul]
      exact (presentedRadical.map_smul r v).trans
        ((Algebra.smul_def r _).trans (Algebra.commutes r _)))

@[simp] theorem toPresented_inr (v : V) : toPresented (TrivSqZeroExt.inr v) = presentedRadical v :=
  TrivSqZeroExt.lift_apply_inr _ _ _ _ _ v

@[simp] theorem toPresented_epsilon (a : Fin 2) : toPresented (epsilon a) = generator a := by
  fin_cases a <;> simp [epsilon, presentedRadical]

def freeEvaluation : Free →ₐ[ℚ] A := FreeAlgebra.lift ℚ epsilon

theorem freeEvaluation_relations {x y : Free} (h : quadraticRelations x y) :
    freeEvaluation x = freeEvaluation y := by
  obtain ⟨a, b, rfl, rfl⟩ := h
  simp [freeEvaluation]

def fromPresented : Presented →ₐ[ℚ] A :=
  RingQuot.liftAlgHom ℚ ⟨freeEvaluation, fun _ _ h => freeEvaluation_relations h⟩

@[simp] theorem fromPresented_generator (a : Fin 2) : fromPresented (generator a) = epsilon a := by
  simp [fromPresented, generator, freeEvaluation]

theorem inr_expansion (v : V) : (TrivSqZeroExt.inr v : A) = ∑ a : Fin 2, v a • epsilon a := by
  exact degree_one_generators ⟨TrivSqZeroExt.inr v, by simp⟩

theorem from_to_presented : fromPresented.comp toPresented = AlgHom.id ℚ A := by
  apply TrivSqZeroExt.algHom_ext
  intro v
  change fromPresented (toPresented (TrivSqZeroExt.inr v)) = TrivSqZeroExt.inr v
  rw [toPresented_inr]
  change fromPresented (∑ a, v a • generator a) = TrivSqZeroExt.inr v
  simp only [map_sum, map_smul, fromPresented_generator]
  exact (inr_expansion v).symm

theorem to_from_presented : toPresented.comp fromPresented = AlgHom.id ℚ Presented := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext a
  change toPresented (fromPresented (generator a)) = generator a
  rw [fromPresented_generator, toPresented_epsilon]

def actualQuadraticPresentation : Presented ≃ₐ[ℚ] A :=
  AlgEquiv.ofAlgHom fromPresented toPresented from_to_presented to_from_presented

def pComponent (n j : ℕ) : Submodule ℚ (P n) :=
  if j = n then Submodule.pi Set.univ (fun _ => component 0)
  else if j = n + 1 then Submodule.pi Set.univ (fun _ => component 1) else ⊥

@[simp] theorem mem_pComponent_base (n : ℕ) (f : P n) :
    f ∈ pComponent n n ↔ ∀ w, (f w).snd = 0 := by
  simp [pComponent, Submodule.mem_pi]

@[simp] theorem mem_pComponent_next (n : ℕ) (f : P n) :
    f ∈ pComponent n (n + 1) ↔ ∀ w, (f w).fst = 0 := by
  simp [pComponent, Submodule.mem_pi]

theorem pComponent_other (n j : ℕ) (h0 : j ≠ n) (h1 : j ≠ n + 1) :
    pComponent n j = ⊥ := by simp [pComponent, h0, h1]

def pSplitZero (n : ℕ) (f : P n) : pComponent n n :=
  ⟨fun w => TrivSqZeroExt.inl (f w).fst, by simp⟩

def pSplitOne (n : ℕ) (f : P n) : pComponent n (n + 1) :=
  ⟨fun w => TrivSqZeroExt.inr (f w).snd, by simp⟩

@[simp] theorem pSplitZero_zero (n : ℕ) : pSplitZero n 0 = 0 := by
  apply Subtype.ext
  funext w
  simp [pSplitZero]

@[simp] theorem pSplitOne_zero (n : ℕ) : pSplitOne n 0 = 0 := by
  apply Subtype.ext
  funext w
  simp [pSplitOne]

def pDecompositionMap (n : ℕ) : P n →+ DirectSum ℕ (fun j => ↥(pComponent n j)) where
  toFun f := DirectSum.of _ n (pSplitZero n f) + DirectSum.of _ (n + 1) (pSplitOne n f)
  map_zero' := by simp
  map_add' f g := by
    have h0 : pSplitZero n (f + g) = pSplitZero n f + pSplitZero n g := by
      apply Subtype.ext; funext w; simp [pSplitZero]
    have h1 : pSplitOne n (f + g) = pSplitOne n f + pSplitOne n g := by
      apply Subtype.ext; funext w; simp [pSplitOne]
    simp only [h0, h1, map_add]
    abel

theorem pDecomposition_homogeneous (n j : ℕ) (x : pComponent n j) :
    pDecompositionMap n x = DirectSum.of _ j x := by
  by_cases h0 : j = n
  · subst j
    have hx := (mem_pComponent_base n x).1 x.property
    have hz : pSplitZero n x = x := by
      apply Subtype.ext; funext w
      exact TrivSqZeroExt.ext rfl (hx w).symm
    have ho : pSplitOne n x = 0 := by
      apply Subtype.ext; funext w; simp [pSplitOne, hx w]
    simp [pDecompositionMap, hz, ho]
  · by_cases h1 : j = n + 1
    · subst j
      have hx := (mem_pComponent_next n x).1 x.property
      have hz : pSplitZero n x = 0 := by
        apply Subtype.ext; funext w; simp [pSplitZero, hx w]
      have ho : pSplitOne n x = x := by
        apply Subtype.ext; funext w
        exact TrivSqZeroExt.ext (hx w).symm rfl
      simp [pDecompositionMap, hz, ho]
    · have hx : (x : P n) = 0 := by
        exact (le_of_eq (pComponent_other n j h0 h1)) x.property
      have : x = 0 := Subtype.ext hx
      subst x
      simp

instance pDecomposition (n : ℕ) : DirectSum.Decomposition (pComponent n) :=
  DirectSum.Decomposition.ofAddHom (pComponent n) (pDecompositionMap n)
    (by
      apply AddMonoidHom.ext
      intro f
      change DirectSum.coeAddMonoidHom (pComponent n)
        (DirectSum.of _ n (pSplitZero n f) + DirectSum.of _ (n + 1) (pSplitOne n f)) = f
      simp only [map_add, DirectSum.coeAddMonoidHom_of]
      funext w
      exact (f w).inl_fst_add_inr_snd_eq)
    (by ext j x : 2; simpa using pDecomposition_homogeneous n j x)

instance pGradedSMul (n : ℕ) : SetLike.GradedSMul component (pComponent n) where
  smul_mem := by
    intro i j a f ha hf
    change a • f ∈ pComponent n (i + j)
    obtain (_ | _ | i) := i
    · rw [Nat.zero_add]
      by_cases hj : j = n
      · subst j
        apply (mem_pComponent_base _ _).2
        intro w
        have h0 := (mem_component_zero a).1 ha
        have h1 := (mem_pComponent_base _ _).1 hf w
        ext b
        change (a * f w).snd b = 0
        simp [mul_snd, h0, h1]
      · by_cases hj1 : j = n + 1
        · subst j
          apply (mem_pComponent_next _ _).2
          intro w
          change (a * f w).fst = 0
          simp [TrivSqZeroExt.fst_mul, (mem_pComponent_next _ _).1 hf w]
        · rw [pComponent_other n j hj hj1] at hf ⊢
          simp_all
    · have h0 := (mem_component_one a).1 ha
      by_cases hj : j = n
      · subst j
        rw [Nat.add_comm 1 n]
        apply (mem_pComponent_next _ _).2
        intro w
        change (a * f w).fst = 0
        simp [TrivSqZeroExt.fst_mul, h0]
      · by_cases hj1 : j = n + 1
        · subst j
          have heq : a • f = 0 := by
            funext w
            apply TrivSqZeroExt.ext
            · simp [TrivSqZeroExt.fst_mul, h0]
            · ext b
              change (a * f w).snd b = 0
              simp [mul_snd, h0, (mem_pComponent_next _ _).1 hf w]
          rw [heq]
          exact Submodule.zero_mem _
        · have : f = 0 := by simpa [pComponent_other n j hj hj1] using hf
          subst f
          simp
    · have : a = 0 := by simpa using ha
      subst a
      simp

theorem differential_homogeneous (n j : ℕ) (f : P (n + 1))
    (hf : f ∈ pComponent (n + 1) j) : differential n f ∈ pComponent n j := by
  by_cases h0 : j = n + 1
  · subst j
    exact (mem_pComponent_next _ _).2 (differential_fst n f)
  · by_cases h1 : j = n + 1 + 1
    · subst j
      have hz := (differential_kernel n f).2 ((mem_pComponent_next _ _).1 hf)
      rw [hz]
      exact Submodule.zero_mem _
    · have : f = 0 := by simpa [pComponent_other (n + 1) j h0 h1] using hf
      subst f
      simp

theorem free_basis_degree (n : ℕ) (w : Word n) :
    (Pi.basisFun A (Word n)) w ∈ pComponent n n := by
  apply (mem_pComponent_base _ _).2
  intro v
  simp [Pi.basisFun_apply, Pi.single_apply, apply_ite]

theorem actual_matrix_entry (n : ℕ) (a : Fin 2) (w : Word n) :
    differential n (Pi.single (a, w) 1) = epsilon a • (Pi.single w 1 : P n) := by
  funext v
  by_cases h : v = w
  · subst v
    fin_cases a <;> simp [differential, Fin.sum_univ_two]
  · fin_cases a <;> simp [differential, Fin.sum_univ_two, h]

theorem actual_matrix_entry_degree (n : ℕ) (a : Fin 2) (w : Word n) :
    differential n (Pi.single (a, w) 1) ∈ pComponent n (n + 1) :=
  (mem_pComponent_next _ _).2 (differential_fst n (Pi.single (a, w) 1))

theorem minimal_every_degree (n : ℕ) :
    (LinearMap.range (differential n)).restrictScalars ℚ = pComponent n (n + 1) := by
  ext f
  change (∃ g, differential n g = f) ↔ f ∈ pComponent n (n + 1)
  rw [mem_pComponent_next]
  exact differential_range n f

abbrev Yoneda (n : ℕ) := Ext.{0} residue residue n

def yonedaProduct (i j : ℕ) : Yoneda i →ₗ[ℚ] Yoneda j →ₗ[ℚ] Yoneda (i + j) :=
  Ext.bilinearCompOfLinear ℚ residue residue residue i j (i + j) rfl

def hilbert : PowerSeries ℚ :=
  PowerSeries.mk fun n => (Module.finrank ℚ (Yoneda n) : ℚ)

@[simp] theorem hilbert_coefficient (n : ℕ) : hilbert.coeff n = (2 : ℚ) ^ n := by
  simp [hilbert, PowerSeries.coeff_mk, ext_finrank]

theorem hilbert_identity :
    (1 - PowerSeries.C 2 * PowerSeries.X) * hilbert = 1 := by
  ext n
  rw [sub_mul, one_mul]
  simp only [map_sub]
  cases n with
  | zero => simp
  | succ n =>
    rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
    simp [pow_succ, mul_comm]

def finiteDenominator {ι : Type*} [Fintype ι] (d : ι → ℕ) : Polynomial ℚ :=
  ∏ i, (1 - Polynomial.X ^ d i)

theorem finiteDenominator_half_ne_zero {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (hd : ∀ i, 0 < d i) :
    Polynomial.eval (1 / 2 : ℚ) (finiteDenominator d) ≠ 0 := by
  classical
  simp only [finiteDenominator, Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.2
  intro i _
  simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X]
  apply sub_ne_zero.mpr
  exact (ne_of_lt (pow_lt_one₀ (by norm_num : (0 : ℚ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℚ) < 1) (Nat.ne_of_gt (hd i)))).symm

theorem no_finite_cyclotomic_denominator {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (hd : ∀ i, 0 < d i) (p : Polynomial ℚ) :
    (finiteDenominator d : PowerSeries ℚ) * hilbert ≠ (p : PowerSeries ℚ) := by
  intro h
  have hs : (((1 - Polynomial.C 2 * Polynomial.X) * p : Polynomial ℚ) : PowerSeries ℚ) =
      (finiteDenominator d : PowerSeries ℚ) := by
    calc
      _ = (1 - PowerSeries.C 2 * PowerSeries.X) *
          ((finiteDenominator d : PowerSeries ℚ) * hilbert) := by
        rw [h]
        simp
      _ = (finiteDenominator d : PowerSeries ℚ) *
          ((1 - PowerSeries.C 2 * PowerSeries.X) * hilbert) := by ring
      _ = _ := by rw [hilbert_identity, mul_one]
  have hp : (1 - Polynomial.C 2 * Polynomial.X) * p = finiteDenominator d :=
    Polynomial.coe_injective ℚ hs
  apply finiteDenominator_half_ne_zero d hd
  rw [← hp]
  norm_num

def koszulDegree (N i : ℕ) : ℕ := N * (i / 2) + i % 2

theorem koszulDegree_two (i : ℕ) : koszulDegree 2 i = i := by
  unfold koszulDegree
  omega

theorem full_linear_resolution_certificate :
    (∀ n, CategoryTheory.Projective (resolution.complex.X n)) ∧
    (∀ n, resolution.complex.ExactAt (n + 1)) ∧
    (∀ n w, (Pi.basisFun A (Word n)) w ∈ pComponent n (koszulDegree 2 n)) ∧
    (∀ n j f, f ∈ pComponent (n + 1) j → differential n f ∈ pComponent n j) ∧
    (∀ n, (LinearMap.range (differential n)).restrictScalars ℚ = pComponent n (n + 1)) := by
  refine ⟨fun n => resolution.projective n, complex_exact, ?_, differential_homogeneous,
    minimal_every_degree⟩
  intro n w
  rw [koszulDegree_two]
  exact free_basis_degree n w

theorem complete_counterexample :
    Nonempty (Presented ≃ₐ[ℚ] A) ∧ Nonempty (ℚ ≃ₗ[ℚ] component 0) ∧
    (∀ n, Module.finrank ℚ (Yoneda n) = 2 ^ n) ∧
    ((1 - PowerSeries.C 2 * PowerSeries.X) * hilbert = 1) ∧
    (∀ (m : ℕ) (d : Fin m → ℕ), (∀ i, 0 < d i) →
      ∀ p : Polynomial ℚ, (finiteDenominator d : PowerSeries ℚ) * hilbert ≠ p) := by
  exact ⟨⟨actualQuadraticPresentation⟩, ⟨connectedEquiv⟩, ext_finrank,
    hilbert_identity, fun _ d hd p => no_finite_cyclotomic_denominator d hd p⟩

def kComponent (j : ℕ) : Submodule ℚ ℚ := if j = 0 then ⊤ else ⊥

def kTerm : ℚ →+ kComponent 0 where
  toFun q := ⟨q, by simp [kComponent]⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def kDecompositionMap : ℚ →+ DirectSum ℕ (fun j => ↥(kComponent j)) :=
  (DirectSum.of _ 0).comp kTerm

instance kDecomposition : DirectSum.Decomposition kComponent :=
  DirectSum.Decomposition.ofAddHom kComponent kDecompositionMap
    (by ext q; simp [kDecompositionMap, kTerm])
    (by
      ext j x : 2
      by_cases h : j = 0
      · subst j
        have hx : kTerm (x : ℚ) = x := rfl
        simp [kDecompositionMap, hx]
      · have hx : (x : ℚ) = 0 := by simpa [kComponent, h] using x.property
        have : x = 0 := Subtype.ext hx
        subst x
        simp)

instance kGradedSMul : SetLike.GradedSMul component kComponent where
  smul_mem := by
    intro i j a q ha hq
    change a • q ∈ kComponent (i + j)
    by_cases hj : j = 0
    · subst j
      obtain (_ | _ | i) := i
      · simp [kComponent]
      · change a.fst * q ∈ kComponent 1
        rw [(mem_component_one a).1 ha]
        simp
      · have : a = 0 := by simpa using ha
        subst a
        change (0 : ℚ) * q ∈ kComponent (i + 1 + 1 + 0)
        rw [zero_mul]
        exact Submodule.zero_mem _
    · have : q = 0 := by simpa [kComponent, hj] using hq
      subst q
      change a.fst * 0 ∈ kComponent (i + j)
      rw [mul_zero]
      exact Submodule.zero_mem _

theorem augmentation_homogeneous (j : ℕ) (f : P 0) (hf : f ∈ pComponent 0 j) :
    augmentation f ∈ kComponent j := by
  by_cases h0 : j = 0
  · subst j
    simp [kComponent]
  · by_cases h1 : j = 1
    · subst j
      have h := (mem_pComponent_next 0 f).1 hf PUnit.unit
      change (f PUnit.unit).fst = 0
      exact h
    · have : f = 0 := by simpa [pComponent_other 0 j h0 h1] using hf
      subst f
      simp

def augmentationIdeal : Ideal A := RingHom.ker (TrivSqZeroExt.fstHom ℚ ℚ V).toRingHom

@[simp] theorem epsilon_mem_augmentationIdeal (a : Fin 2) : epsilon a ∈ augmentationIdeal := rfl

def radicalFree (n : ℕ) : Submodule A (P n) :=
  Submodule.span A {x | ∃ (a : Fin 2) (w : Word n), x = epsilon a • (Pi.single w 1 : P n)}

theorem radicalFree_eq_range (n : ℕ) : radicalFree n = LinearMap.range (differential n) := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro x ⟨a, w, rfl⟩
    exact ⟨Pi.single (a, w) 1, actual_matrix_entry n a w⟩
  · rintro x ⟨f, rfl⟩
    have hf : (∑ z : Word (n + 1), f z • (Pi.single z 1 : P (n + 1))) = f := by
      funext w
      simp [Pi.single_apply]
    have hs : (∑ z : Word (n + 1), f z • differential n (Pi.single z 1)) ∈ radicalFree n := by
      apply Submodule.sum_mem
      intro z _
      apply Submodule.smul_mem
      obtain ⟨a, w⟩ := z
      rw [actual_matrix_entry]
      exact Submodule.subset_span ⟨a, w, rfl⟩
    have hh : differential n f = ∑ z : Word (n + 1), f z • differential n (Pi.single z 1) := by
      conv_lhs => rw [← hf]
      simp only [map_sum, map_smul]
    rwa [← hh] at hs

theorem graded_minimal_augmentation_certificate :
    (∀ j f, f ∈ pComponent 0 j → augmentation f ∈ kComponent j) ∧
    (∀ n, radicalFree n = LinearMap.range (differential n)) ∧
    (∀ a : Fin 2, epsilon a ∈ component 1 ∧ epsilon a ∈ augmentationIdeal) := by
  exact ⟨augmentation_homogeneous, radicalFree_eq_range, fun a => ⟨by simp, by simp⟩⟩

end TLMC561
