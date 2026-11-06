import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Combinatorics.Young.SemistandardTableau
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
The genuine rank-two q-Schur cell quotient at q=-1.
The Hecke presentation, full permutation-module endomorphisms and cellular
quotient are constructed explicitly; no classification theorem is assumed.
-/
namespace TLMC1770
open Polynomial Module
open scoped DirectSum
noncomputable section
set_option linter.unusedSimpArgs false

abbrev K := ℂ
abbrev H := TrivSqZeroExt K K

def eps : H := TrivSqZeroExt.inr 1
def heckeGenerator : H := eps - 1
def heckePolynomial : K[X] := (X + 1)^2
abbrev HeckePresentation := AdjoinRoot heckePolynomial

theorem eps_sq : eps * eps = 0 := by
  simp [eps]

theorem hecke_relation : (heckeGenerator - (-1 : H)) * (heckeGenerator + 1) = 0 := by
  simpa [heckeGenerator] using eps_sq

theorem root_eps_sq : (AdjoinRoot.root heckePolynomial + 1)^2 = 0 := by
  have h := AdjoinRoot.eval₂_root heckePolynomial
  change (((X + 1)^2 : K[X]).eval₂ (AdjoinRoot.of heckePolynomial)
    (AdjoinRoot.root heckePolynomial)) = 0 at h
  rw [eval₂_pow, eval₂_add, eval₂_X, eval₂_one] at h
  exact h

def fromPresentation : HeckePresentation →ₐ[K] H :=
  AdjoinRoot.liftAlgHom heckePolynomial (Algebra.ofId K H) heckeGenerator (by
    simp [heckePolynomial, heckeGenerator, pow_two, eps_sq])

def toPresentation : H →ₐ[K] HeckePresentation :=
  TrivSqZeroExt.liftEquivOfComm ⟨
    (LinearMap.id : K →ₗ[K] K).smulRight (AdjoinRoot.root heckePolynomial + 1), by
    intro x y
    simp only [LinearMap.smulRight_apply, LinearMap.id_apply]
    rw [smul_mul_smul_comm, ← pow_two, root_eps_sq, smul_zero]⟩

@[simp] theorem fromPresentation_root :
    fromPresentation (AdjoinRoot.root heckePolynomial) = heckeGenerator := by
  simp [fromPresentation]

@[simp] theorem toPresentation_inr (c : K) :
    toPresentation (TrivSqZeroExt.inr c) = c • (AdjoinRoot.root heckePolynomial + 1) := by
  simp [toPresentation]

def heckeEquiv : HeckePresentation ≃ₐ[K] H :=
  AlgEquiv.ofAlgHom fromPresentation toPresentation
    (by
      apply TrivSqZeroExt.algHom_ext
      intro c
      simp only [AlgHom.comp_apply, toPresentation_inr, map_smul, map_add,
        fromPresentation_root, map_one, AlgHom.id_apply]
      simp only [heckeGenerator, sub_add_cancel]
      change c • (TrivSqZeroExt.inr (1:K) : H)=TrivSqZeroExt.inr c
      rw [← TrivSqZeroExt.inr_smul]
      simp)
    (by
      apply AdjoinRoot.algHom_ext
      simp [heckeGenerator, eps])

theorem q_primitive : IsPrimitiveRoot (-1 : K) 2 := IsPrimitiveRoot.neg_one 0 (by decide)

instance baseAlgebra : Algebra H K := TrivSqZeroExt.algebraBase K K

@[simp] theorem base_smul (h : H) (c : K) : h • c=h.fst*c := rfl

instance baseTower : IsScalarTower K H K where
  smul_assoc a h b := by
    change (a * h.fst) * b = a * (h.fst * b)
    ring

abbrev M := K × (H × K)
abbrev S := Module.End H M

@[simp] theorem map_K_smul (f : S) (c : K) (x : M) : f (c • x)=c • f x :=
  (f.restrictScalars K).map_smul c x

def topVector : M := (0, (1, 0))

def socleVector (i : Fin 3) : M :=
  ![(1, (0, 0)), (0, (eps, 0)), (0, (0, 1))] i

def inputVector (i : Fin 3) : M :=
  ![(1, (0, 0)), topVector, (0, (0, 1))] i

def coefficient (i : Fin 3) (x : M) : K :=
  ![x.1, x.2.1.snd, x.2.2] i

def augmentation (x : M) : K := x.2.1.fst

def rowFunctional (j : Fin 3) : M →ₗ[H] K where
  toFun x := ![x.1, x.2.1.fst, x.2.2] j
  map_add' x y := by fin_cases j <;> rfl
  map_smul' h x := by
    fin_cases j <;> simp [TrivSqZeroExt.algebraBase, smul_eq_mul]

def rowInclusion (i : Fin 3) : K →ₗ[H] M where
  toFun c := c • socleVector i
  map_add' c d := by simp [add_smul]
  map_smul' h c := by
    fin_cases i <;> ext <;>
      simp [socleVector, eps, TrivSqZeroExt.algebraBase, smul_eq_mul, mul_comm, mul_left_comm]

def phi (i j : Fin 3) : S := (rowInclusion i).comp (rowFunctional j)

def e : S where
  toFun x := (0, (x.2.1, 0))
  map_add' x y := by simp
  map_smul' h x := by simp

@[simp] theorem phi_apply (i j : Fin 3) (x : M) :
    phi i j x = rowFunctional j x • socleVector i := rfl

@[simp] theorem e_apply (x : M) : e x = (0, (x.2.1, 0)) := rfl

@[simp] theorem row_input (i j : Fin 3) :
    rowFunctional i (inputVector j) = if i=j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [rowFunctional, inputVector, topVector]

@[simp] theorem row_socle (i j : Fin 3) :
    rowFunctional i (socleVector j) = if i=j ∧ j≠1 then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [rowFunctional, socleVector, eps]

@[simp] theorem coeff_socle (i j : Fin 3) :
    coefficient i (socleVector j) = if i=j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [coefficient, socleVector, eps]

@[simp] theorem coefficient_add (i : Fin 3) (x y : M) :
    coefficient i (x+y)=coefficient i x+coefficient i y := by fin_cases i <;> rfl

@[simp] theorem coefficient_smul (i : Fin 3) (c : K) (x : M) :
    coefficient i (c • x)=c*coefficient i x := by fin_cases i <;> rfl

theorem eps_top : eps • topVector = socleVector 1 := by
  ext <;> simp [eps, topVector, socleVector, TrivSqZeroExt.algebraBase, smul_eq_mul]

theorem eps_smul (x : M) : eps • x = augmentation x • socleVector 1 := by
  ext <;> simp [eps, augmentation, socleVector, TrivSqZeroExt.algebraBase, smul_eq_mul]

theorem expansion_M (x : M) :
    x = augmentation x • topVector + ∑ i : Fin 3, coefficient i x • socleVector i := by
  ext <;> simp [Fin.sum_univ_three, augmentation, coefficient, topVector, socleVector,
    eps, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraBase, smul_eq_mul]

def alpha (f : S) : K := augmentation (f topVector)
def entry (f : S) (i j : Fin 3) : K := coefficient i (f (inputVector j))

theorem end_socle (f : S) : f (socleVector 1) = alpha f • socleVector 1 := by
  calc
    _ = f (eps • topVector) := by rw [eps_top]
    _ = eps • f topVector := by rw [map_smul]
    _ = alpha f • socleVector 1 := eps_smul _

theorem end_socle_aug (f : S) (i : Fin 3) : augmentation (f (socleVector i))=0 := by
  have h : eps • f (socleVector i)=0 := by
    rw [← map_smul]
    have hz : eps • socleVector i=0 := by
      fin_cases i <;> ext <;> simp [socleVector, eps, TrivSqZeroExt.algebraBase, smul_eq_mul]
    rw [hz, map_zero]
  have h' := congrArg (fun x : M => x.2.1.snd) h
  simpa [eps_smul, socleVector, eps, augmentation] using h'

theorem identity_decomposition : (1 : S)=e+phi 0 0+phi 2 2 := by
  ext x <;> simp [phi, rowInclusion, rowFunctional, socleVector]

theorem end_ext {f g : S} (h : ∀ i : Fin 3, f (inputVector i)=g (inputVector i)) : f=g := by
  have ht : f topVector=g topVector := h 1
  have hb : ∀ i : Fin 3, f (socleVector i)=g (socleVector i) := by
    intro i
    fin_cases i
    · exact h 0
    · change f (socleVector 1)=g (socleVector 1)
      rw [← eps_top, map_smul, map_smul, ht]
    · exact h 2
  apply LinearMap.ext
  intro x
  rw [expansion_M x]
  simp only [map_add, map_sum, map_K_smul, ht, hb]

@[simp] theorem phi_mul_phi (i j k l : Fin 3) :
    phi i j * phi k l = (if j=k ∧ k≠1 then (1:K) else 0) • phi i l := by
  apply LinearMap.ext
  intro x
  change rowInclusion i (rowFunctional j (rowInclusion k (rowFunctional l x))) = _
  simp only [rowInclusion, LinearMap.coe_mk, AddHom.coe_mk]
  rw [show rowFunctional j (rowFunctional l x • socleVector k) =
      rowFunctional l x • rowFunctional j (socleVector k) from
      (rowFunctional j |>.restrictScalars K).map_smul _ _]
  rw [row_socle]
  split_ifs <;> simp [phi_apply, smul_smul]

@[simp] theorem e_mul_e : e*e=e := by ext x <;> simp

@[simp] theorem e_mul_phi (i j : Fin 3) :
    e * phi i j = if i=1 then phi i j else 0 := by
  fin_cases i <;> apply LinearMap.ext <;> intro x <;>
    ext <;> simp [phi_apply, rowInclusion, socleVector, eps]

@[simp] theorem phi_mul_e (i j : Fin 3) :
    phi i j * e = if j=1 then phi i j else 0 := by
  fin_cases j <;> apply LinearMap.ext <;> intro x <;>
    ext <;> simp [phi_apply, rowInclusion, rowFunctional, socleVector]

theorem end_reconstruction (f : S) :
    f=alpha f • e + ∑ i : Fin 3, ∑ j : Fin 3, entry f i j • phi i j := by
  have h0 := end_socle_aug f 0
  have h2 := end_socle_aug f 2
  simp [augmentation, socleVector] at h0 h2
  apply end_ext
  intro j
  fin_cases j <;> ext <;>
    simp [Fin.sum_univ_three, entry, alpha, augmentation, coefficient, phi_apply,
      rowFunctional, rowInclusion, socleVector, inputVector, topVector, eps, h0, h2]

abbrev CellIndex := Option (Fin 3 × Fin 3)

def cell : CellIndex → S
  | none => e
  | some (i,j) => phi i j

def coordinate (f : S) : CellIndex → K
  | none => alpha f
  | some (i,j) => entry f i j

@[simp] theorem coordinate_cell (a b : CellIndex) : coordinate (cell a) b = if b=a then 1 else 0 := by
  cases a with
  | none =>
    cases b with
    | none => simp [coordinate, cell, alpha, augmentation, topVector]
    | some b => rcases b with ⟨i,j⟩; fin_cases i <;> fin_cases j <;>
        simp [coordinate, cell, entry, coefficient, inputVector, topVector, eps]
  | some a =>
    rcases a with ⟨i,j⟩
    cases b with
    | none => fin_cases i <;> fin_cases j <;>
        simp [coordinate, cell, alpha, augmentation, phi_apply, rowFunctional, socleVector, topVector, eps]
    | some b =>
      rcases b with ⟨k,l⟩
      fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
        simp [coordinate, cell, entry, coefficient, phi_apply, rowFunctional, socleVector,
          inputVector, topVector, eps]

def coordinateMap : S →ₗ[K] (CellIndex → K) where
  toFun := coordinate
  map_add' f g := by
    funext a
    cases a with
    | none => rfl
    | some a => rcases a with ⟨i,j⟩; simp [coordinate, entry]
  map_smul' c f := by
    funext a
    cases a with
    | none => rfl
    | some a => rcases a with ⟨i,j⟩; simp [coordinate, entry]

theorem coordinate_injective : Function.Injective coordinate := by
  intro f g h
  rw [end_reconstruction f, end_reconstruction g]
  have ha : alpha f=alpha g := congrFun h none
  have he : ∀ i j, entry f i j=entry g i j := fun i j => congrFun h (some (i,j))
  simp only [ha, he]

theorem coordinate_surjective : Function.Surjective coordinate := by
  intro c
  refine ⟨∑ a : CellIndex, c a • cell a, ?_⟩
  change coordinateMap _=c
  rw [map_sum]
  simp only [map_smul]
  ext b
  simp [Finset.sum_apply, coordinateMap, coordinate_cell]

def cellCoordinates : S ≃ₗ[K] (CellIndex → K) :=
  LinearEquiv.ofBijective coordinateMap ⟨coordinate_injective,coordinate_surjective⟩

def fullCellBasis : Basis CellIndex K S := Basis.ofEquivFun cellCoordinates

theorem fullCellBasis_apply (a : CellIndex) : fullCellBasis a=cell a := by
  apply coordinate_injective
  ext b
  have h := Basis.ofEquivFun_repr_apply cellCoordinates (fullCellBasis a) b
  change fullCellBasis.repr (fullCellBasis a) b=coordinate (fullCellBasis a) b at h
  rw [← h, Basis.repr_self_apply]
  simp [coordinate_cell, eq_comm]

def transposeIndex : CellIndex → CellIndex
  | none => none
  | some (i,j) => some (j,i)

def cellAnti : S →ₗ[K] S := fullCellBasis.constr K (fun a => cell (transposeIndex a))

@[simp] theorem cellAnti_cell (a : CellIndex) : cellAnti (cell a)=cell (transposeIndex a) := by
  rw [← fullCellBasis_apply]
  exact fullCellBasis.constr_basis K _ a

@[simp] theorem cellAnti_e : cellAnti e=e := cellAnti_cell none

@[simp] theorem cellAnti_phi (i j : Fin 3) : cellAnti (phi i j)=phi j i := cellAnti_cell (some (i,j))

theorem cellAnti_involutive (f : S) : cellAnti (cellAnti f)=f := by
  have h : cellAnti.comp cellAnti=(LinearMap.id : S →ₗ[K] S) := by
    apply fullCellBasis.ext
    intro a
    rw [fullCellBasis_apply]
    cases a with
    | none => simp [cell]
    | some a => rcases a with ⟨i,j⟩; simp [cell]
  exact congrArg (fun F : S →ₗ[K] S => F f) h

theorem cellAnti_cell_product (a b : CellIndex) :
    cellAnti (cell a*cell b)=cellAnti (cell b)*cellAnti (cell a) := by
  cases a with
  | none =>
    cases b with
    | none => simp [cell]
    | some b => rcases b with ⟨i,j⟩; by_cases hi:i=1 <;> simp [cell,hi]
  | some a =>
    rcases a with ⟨i,j⟩
    cases b with
    | none => by_cases hj:j=1 <;> simp [cell,hj]
    | some b =>
      rcases b with ⟨k,l⟩
      by_cases h:j=k
      · subst k
        by_cases hj:j=1 <;> simp [cell,hj]
      · simp [cell,h,Ne.symm h]

theorem cellAnti_mul (f g : S) : cellAnti (f*g)=cellAnti g*cellAnti f := by
  have hf : f=∑ a : CellIndex, fullCellBasis.repr f a • cell a := by
    simpa [fullCellBasis_apply] using (fullCellBasis.sum_repr f).symm
  have hg : g=∑ a : CellIndex, fullCellBasis.repr g a • cell a := by
    simpa [fullCellBasis_apply] using (fullCellBasis.sum_repr g).symm
  rw [hf,hg]
  simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,
    Finset.smul_sum,smul_smul,map_sum,map_smul,cellAnti_cell_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_comm]

@[simp] theorem augmentation_add (x y : M) : augmentation (x+y)=augmentation x+augmentation y := rfl
@[simp] theorem augmentation_smul (c : K) (x : M) : augmentation (c • x)=c*augmentation x := rfl

theorem augmentation_end (f : S) (x : M) : augmentation (f x)=alpha f*augmentation x := by
  conv_lhs => rw [expansion_M x]
  simp [map_K_smul,Fin.sum_univ_three,end_socle_aug,alpha,mul_comm]

@[simp] theorem alpha_mul (f g : S) : alpha (f*g)=alpha f*alpha g := augmentation_end f (g topVector)
@[simp] theorem alpha_add (f g : S) : alpha (f+g)=alpha f+alpha g := rfl
@[simp] theorem alpha_smul (c : K) (f : S) : alpha (c • f)=c*alpha f := rfl
@[simp] theorem alpha_one : alpha (1:S)=1 := rfl
@[simp] theorem alpha_e : alpha e=1 := rfl
@[simp] theorem alpha_phi (i j : Fin 3) : alpha (phi i j)=0 := by
  simpa [coordinate,cell] using coordinate_cell (some (i,j)) none

def scalarCharacter : S →ₐ[K] K where
  toFun := alpha
  map_one' := alpha_one
  map_mul' := alpha_mul
  map_zero' := rfl
  map_add' := alpha_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,alpha_smul,alpha_one,mul_one]
    simp

def higherSpan : Submodule K S := Submodule.span K (Set.range (fun a : Fin 3 × Fin 3 => phi a.1 a.2))

theorem higherSpan_eq_ker : higherSpan=LinearMap.ker scalarCharacter.toLinearMap := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i,j⟩,rfl⟩
    exact alpha_phi i j
  · intro f hf
    have ha : alpha f=0 := hf
    rw [end_reconstruction f,ha,zero_smul,zero_add]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i,j),rfl⟩)

theorem higherSpan_mem_iff (f : S) : f ∈ higherSpan ↔ alpha f=0 := by
  rw [higherSpan_eq_ker]
  rfl

theorem higherSpan_mul_left (f g : S) (hf : f∈higherSpan) : g*f∈higherSpan := by
  rw [higherSpan_mem_iff] at hf ⊢
  simp [hf]

theorem higherSpan_mul_right (f g : S) (hf : f∈higherSpan) : f*g∈higherSpan := by
  rw [higherSpan_mem_iff] at hf ⊢
  simp [hf]

def oppositeCharacter : Sᵐᵒᵖ →+* K where
  toFun s := alpha s.unop
  map_one' := alpha_one
  map_zero' := rfl
  map_add' x y := alpha_add _ _
  map_mul' x y := by simp [mul_comm]

instance rightScalarModule : Module Sᵐᵒᵖ K := Module.compHom K oppositeCharacter

@[simp] theorem right_scalar_smul (s : Sᵐᵒᵖ) (c : K) : s • c=alpha s.unop*c := rfl

def rightCharacter : S →ₗ[Sᵐᵒᵖ] K where
  toFun := alpha
  map_add' := alpha_add
  map_smul' s f := by
    change alpha (f*s.unop)=alpha s.unop*alpha f
    simp [mul_comm]

theorem rightCharacter_surjective : Function.Surjective rightCharacter := by
  intro c
  exact ⟨c • (1:S),by simp [rightCharacter]⟩

def higherRight : Submodule Sᵐᵒᵖ S := LinearMap.ker rightCharacter
abbrev CellQuotient := S ⧸ higherRight

theorem higherRight_mem_iff (f : S) : f ∈ higherRight ↔ f∈higherSpan := by
  rw [higherSpan_mem_iff]
  rfl

def quotientCharacter : CellQuotient ≃ₗ[Sᵐᵒᵖ] K :=
  rightCharacter.quotKerEquivOfSurjective rightCharacter_surjective

@[simp] theorem quotientCharacter_mk (f : S) :
    quotientCharacter (higherRight.mkQ f)=alpha f := by
  exact rightCharacter.quotKerEquivOfSurjective_apply_mk rightCharacter_surjective f

instance rightScalar_simple : IsSimpleModule Sᵐᵒᵖ K := by
  apply isSimpleModule_iff_toSpanSingleton_surjective.mpr
  refine ⟨inferInstance,?_⟩
  intro x hx y
  refine ⟨MulOpposite.op ((y/x) • (1:S)),?_⟩
  change alpha ((y/x) • (1:S))*x=y
  simp [div_mul_cancel₀ _ hx]

instance quotient_simple : IsSimpleModule Sᵐᵒᵖ CellQuotient :=
  IsSimpleModule.congr quotientCharacter

def columnCell : Submodule Sᵐᵒᵖ CellQuotient :=
  Submodule.span Sᵐᵒᵖ {higherRight.mkQ e}

theorem columnCell_eq_top : columnCell=⊤ := by
  apply top_unique
  intro q _
  have hz : higherRight.mkQ e∈columnCell := Submodule.subset_span (by simp)
  have heq : q=MulOpposite.op (quotientCharacter q • (1:S)) • higherRight.mkQ e := by
    apply quotientCharacter.injective
    rw [map_smul]
    change quotientCharacter q=alpha (quotientCharacter q • (1:S))*quotientCharacter (higherRight.mkQ e)
    rw [quotientCharacter_mk,alpha_e,alpha_smul,alpha_one]
    simp
  rw [heq]
  exact columnCell.smul_mem _ hz

def columnCellEquiv : columnCell ≃ₗ[Sᵐᵒᵖ] K :=
  (LinearEquiv.ofEq _ _ columnCell_eq_top).trans ((Submodule.topEquiv).trans quotientCharacter)

instance columnCell_simple : IsSimpleModule Sᵐᵒᵖ columnCell := IsSimpleModule.congr columnCellEquiv

theorem columnCell_semisimple : IsSemisimpleModule Sᵐᵒᵖ columnCell := inferInstance

/-! The complete native permutation-module realization. -/
abbrev WeakComposition := {v : Fin 2 → ℕ // ∑ i, v i=2}

def composition (i : Fin 3) : WeakComposition :=
  ⟨![2-i.val,i.val],by simp [Fin.sum_univ_two]; omega⟩

theorem composition_bijective : Function.Bijective composition := by
  constructor
  · intro i j h
    have h' := congrArg (fun c : WeakComposition => c.val 1) h
    exact Fin.ext h'
  · intro μ
    have h := μ.property
    simp only [Fin.sum_univ_two] at h
    have hi : μ.val 1<3 := by omega
    refine ⟨⟨μ.val 1,hi⟩,Subtype.ext ?_⟩
    funext k
    fin_cases k
    · simp [composition]; omega
    · rfl

def compositionEquiv : Fin 3 ≃ WeakComposition := Equiv.ofBijective composition composition_bijective

instance : Fintype WeakComposition := Fintype.ofEquiv (Fin 3) compositionEquiv
instance : DecidableEq WeakComposition := Classical.decEq _

theorem all_compositions (μ : WeakComposition) : ∃ i : Fin 3, μ=composition i := by
  obtain ⟨i,hi⟩ := composition_bijective.2 μ
  exact ⟨i,hi.symm⟩

def rowOf (μ : WeakComposition) (i : Fin 2) : Fin 2 := if i.val<μ.val 0 then 0 else 1

abbrev G := Equiv.Perm (Fin 2)
def transposition : G := Equiv.swap 0 1

@[simp] theorem transposition_ne_one : transposition≠1 := by decide

theorem group_cases (g : G) : g=1 ∨ g=transposition := by
  have h : ∀ g : G, g=1 ∨ g=transposition := by decide
  exact h g

theorem group_univ : (Finset.univ : Finset G)={1,transposition} := by
  ext g
  simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_iff]
  exact group_cases g

def youngGroup (μ : WeakComposition) : Subgroup G where
  carrier := {g | ∀ i, rowOf μ (g i)=rowOf μ i}
  one_mem' i := rfl
  mul_mem' hg hh i := (hg _).trans (hh i)
  inv_mem' {g} hg i := by
    have h := hg (g⁻¹ i)
    simpa using h.symm

theorem youngGroup_zero : youngGroup (composition 0)=⊤ := by
  apply Subgroup.ext
  intro g
  change (∀ i, rowOf (composition 0) (g i)=rowOf (composition 0) i) ↔ True
  refine ⟨fun _ => trivial,fun _ i => ?_⟩
  change (if (g i).val<2 then (0:Fin 2) else 1)=(if i.val<2 then 0 else 1)
  rw [if_pos (g i).is_lt,if_pos i.is_lt]

theorem youngGroup_two : youngGroup (composition 2)=⊤ := by
  apply Subgroup.ext
  intro g
  change (∀ i, rowOf (composition 2) (g i)=rowOf (composition 2) i) ↔ True
  simp [rowOf,composition]

@[simp] theorem rowOf_middle (i : Fin 2) : rowOf (composition 1) i=i := by
  fin_cases i <;> rfl

theorem youngGroup_one : youngGroup (composition 1)=⊥ := by
  apply Subgroup.ext
  intro g
  constructor
  · intro h
    apply Equiv.ext
    intro i
    change g i=i
    simpa only [rowOf_middle] using h i
  · intro h
    have h' : g=1 := h
    subst g
    exact Subgroup.one_mem _

def heckeBasis (g : G) : H := if g=1 then 1 else heckeGenerator

def youngSymmetrizer (μ : WeakComposition) : H := by
  classical
  exact ∑ g ∈ (Finset.univ : Finset G).filter (fun g => g∈youngGroup μ), heckeBasis g

@[simp] theorem youngSymmetrizer_zero : youngSymmetrizer (composition 0)=eps := by
  classical
  unfold youngSymmetrizer
  simp only [youngGroup_zero,Subgroup.mem_top,Finset.filter_true]
  rw [group_univ]
  simp [heckeBasis,heckeGenerator,Ne.symm transposition_ne_one,add_comm]

@[simp] theorem youngSymmetrizer_two : youngSymmetrizer (composition 2)=eps := by
  classical
  unfold youngSymmetrizer
  simp only [youngGroup_two,Subgroup.mem_top,Finset.filter_true]
  rw [group_univ]
  simp [heckeBasis,heckeGenerator,Ne.symm transposition_ne_one,add_comm]

@[simp] theorem youngSymmetrizer_one : youngSymmetrizer (composition 1)=1 := by
  classical
  unfold youngSymmetrizer
  simp only [youngGroup_one,Subgroup.mem_bot]
  have hf : (Finset.univ.filter (fun g : G => g=1))={1} := by ext g; simp
  rw [hf]
  simp [heckeBasis]

def permutationIdeal (μ : WeakComposition) : Ideal H := Ideal.span {youngSymmetrizer μ}
def epsilonIdeal : Ideal H := Ideal.span {eps}

theorem epsilonIdeal_mem (x : H) : x∈epsilonIdeal ↔ x.fst=0 := by
  rw [epsilonIdeal,Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y,rfl⟩
    simp [eps]
  · intro hx
    refine ⟨TrivSqZeroExt.inl x.snd,?_⟩
    ext <;> simp [eps,hx]

@[simp] theorem permutationIdeal_zero : permutationIdeal (composition 0)=epsilonIdeal := by
  simp [permutationIdeal,epsilonIdeal]
@[simp] theorem permutationIdeal_two : permutationIdeal (composition 2)=epsilonIdeal := by
  simp [permutationIdeal,epsilonIdeal]
@[simp] theorem permutationIdeal_one : permutationIdeal (composition 1)=⊤ := by
  simp [permutationIdeal]

def epsilonIdealEquiv : K ≃ₗ[H] epsilonIdeal where
  toFun c := ⟨TrivSqZeroExt.inr c,(epsilonIdeal_mem _).mpr rfl⟩
  invFun x := x.val.snd
  left_inv c := rfl
  right_inv x := by
    apply Subtype.ext
    apply TrivSqZeroExt.ext
    · exact ((epsilonIdeal_mem x).mp x.property).symm
    · rfl
  map_add' c d := by apply Subtype.ext; simp
  map_smul' h c := by
    apply Subtype.ext
    ext <;> simp [base_smul,smul_eq_mul]

abbrev PermutationSum := ∀ μ : WeakComposition, permutationIdeal μ
abbrev ActualQSchur := Module.End H PermutationSum

def permutationDirectSumEquiv : (⨁ μ : WeakComposition, permutationIdeal μ) ≃ₗ[H] PermutationSum :=
  DirectSum.linearEquivFunOnFintype H WeakComposition (fun μ => permutationIdeal μ)

def permutationCoordinates (x : M) (μ : WeakComposition) : H :=
  if μ.val 1=0 then TrivSqZeroExt.inr x.1
  else if μ.val 1=1 then x.2.1 else TrivSqZeroExt.inr x.2.2

theorem permutationCoordinates_mem (x : M) (μ : WeakComposition) :
    permutationCoordinates x μ∈permutationIdeal μ := by
  obtain ⟨i,rfl⟩ := all_compositions μ
  fin_cases i
  · change TrivSqZeroExt.inr x.1∈permutationIdeal (composition 0)
    rw [permutationIdeal_zero,epsilonIdeal_mem]
    rfl
  · change x.2.1∈permutationIdeal (composition 1)
    rw [permutationIdeal_one]
    exact Submodule.mem_top
  · change TrivSqZeroExt.inr x.2.2∈permutationIdeal (composition 2)
    rw [permutationIdeal_two,epsilonIdeal_mem]
    rfl

def permutationMap : M →ₗ[H] PermutationSum where
  toFun x μ := ⟨permutationCoordinates x μ,permutationCoordinates_mem x μ⟩
  map_add' x y := by
    funext μ
    apply Subtype.ext
    obtain ⟨i,rfl⟩ := all_compositions μ
    fin_cases i <;> simp [permutationCoordinates,composition]
  map_smul' h x := by
    funext μ
    apply Subtype.ext
    obtain ⟨i,rfl⟩ := all_compositions μ
    fin_cases i <;> ext <;> simp [permutationCoordinates,composition,base_smul,smul_eq_mul]

def inversePermutationCoordinates (y : PermutationSum) : M :=
  ((y (composition 0)).val.snd,((y (composition 1)).val,(y (composition 2)).val.snd))

theorem inversePermutation_left (x : M) : inversePermutationCoordinates (permutationMap x)=x := by
  ext <;> simp [inversePermutationCoordinates,permutationMap,permutationCoordinates,composition]

theorem inversePermutation_right (y : PermutationSum) : permutationMap (inversePermutationCoordinates y)=y := by
  funext μ
  apply Subtype.ext
  obtain ⟨i,rfl⟩ := all_compositions μ
  have h0 := (epsilonIdeal_mem _).mp (show (y (composition 0)).val∈epsilonIdeal by simpa using (y (composition 0)).property)
  have h2 := (epsilonIdeal_mem _).mp (show (y (composition 2)).val∈epsilonIdeal by simpa using (y (composition 2)).property)
  simp [composition] at h0 h2
  fin_cases i <;> ext <;>
    simp [inversePermutationCoordinates,permutationMap,permutationCoordinates,composition,h0,h2]

def permutationEquiv : M ≃ₗ[H] PermutationSum :=
  LinearEquiv.ofBijective permutationMap ⟨
    Function.LeftInverse.injective inversePermutation_left,
    Function.RightInverse.surjective inversePermutation_right⟩

def fullQSchurEquiv : S ≃ₐ[H] ActualQSchur where
  __ := permutationEquiv.conjRingEquiv
  commutes' h := by
    apply LinearMap.ext
    intro y
    simp [Algebra.algebraMap_eq_smul_one]

instance rightScalarTower : IsScalarTower K Sᵐᵒᵖ K where
  smul_assoc c s x := by
    change alpha ((c • s).unop)*x=c*(alpha s.unop*x)
    simp [mul_assoc]

def columnCellComplexEquiv : columnCell ≃ₗ[K] K := columnCellEquiv.restrictScalars K

theorem columnCell_finrank : Module.finrank K columnCell=1 := by
  simpa using columnCellComplexEquiv.finrank_eq

theorem fullEnd_finrank : Module.finrank K S=10 := by
  rw [Module.finrank_eq_card_basis fullCellBasis]
  simp [CellIndex]

/-! Actual Young diagrams, bounded semistandard tableaux and hook lengths. -/
def rowShape : YoungDiagram := YoungDiagram.ofRowLens [2] (by decide)
def columnShape : YoungDiagram := YoungDiagram.ofRowLens [1,1] (by decide)

theorem rowShape_cells : rowShape.cells={(0,0),(0,1)} := by decide
theorem columnShape_cells : columnShape.cells={(0,0),(1,0)} := by decide

theorem rowShape_mem (i j : ℕ) : (i,j)∈rowShape ↔ i=0 ∧ j≤1 := by
  rw [← YoungDiagram.mem_cells,rowShape_cells]
  simp only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq]
  omega

theorem columnShape_mem (i j : ℕ) : (i,j)∈columnShape ↔ i≤1 ∧ j=0 := by
  rw [← YoungDiagram.mem_cells,columnShape_cells]
  simp only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq]
  omega

def arm (lam : YoungDiagram) (a : ℕ×ℕ) : Finset (ℕ×ℕ) :=
  lam.cells.filter (fun b => b.1=a.1 ∧ a.2<b.2)
def leg (lam : YoungDiagram) (a : ℕ×ℕ) : Finset (ℕ×ℕ) :=
  lam.cells.filter (fun b => b.2=a.2 ∧ a.1<b.1)
def hookLength (lam : YoungDiagram) (a : ℕ×ℕ) : ℕ := (arm lam a).card+(leg lam a).card+1

theorem column_top_hook : hookLength columnShape (0,0)=2 := by
  rw [hookLength,arm,leg,columnShape_cells]
  decide

theorem column_divisible_hook : ∃ a∈columnShape.cells, 2∣hookLength columnShape a := by
  refine ⟨(0,0),by rw [columnShape_cells]; decide,?_⟩
  rw [column_top_hook]

abbrev BoundedTableau (lam : YoungDiagram) :=
  {T : SemistandardYoungTableau lam // ∀ r c, (r,c)∈lam → T r c<2}

def rowLeft (i : Fin 3) : ℕ := ![0,0,1] i
def rowRight (i : Fin 3) : ℕ := ![0,1,1] i

def rowFilling (i : Fin 3) : SemistandardYoungTableau rowShape where
  entry r c := if r=0 ∧ c=0 then rowLeft i else if r=0 ∧ c=1 then rowRight i else 0
  row_weak' := by
    intro r c d hcd hd
    have hm := (rowShape_mem r d).mp hd
    have hr : r=0 := hm.1
    have hc : c=0 := by omega
    have he : d=1 := by omega
    subst r; subst c; subst d
    fin_cases i <;> decide
  col_strict' := by
    intro r s c hrs hs
    have hm := (rowShape_mem s c).mp hs
    omega
  zeros' := by
    intro r c hn
    have h0 : ¬(r=0 ∧ c=0) := by intro h; apply hn; rw [rowShape_mem]; omega
    have h1 : ¬(r=0 ∧ c=1) := by intro h; apply hn; rw [rowShape_mem]; omega
    simp [h0,h1]

def rowTableau (i : Fin 3) : BoundedTableau rowShape := ⟨rowFilling i,by
  intro r c hm
  have hs := (rowShape_mem r c).mp hm
  have hr : r=0 := hs.1
  have hc : c=0 ∨ c=1 := by omega
  subst r
  rcases hc with rfl|rfl <;> fin_cases i <;> decide⟩

@[simp] theorem rowTableau_value (i : Fin 3) (r c : ℕ) :
    (rowTableau i).val r c=if r=0 ∧ c=0 then rowLeft i else if r=0 ∧ c=1 then rowRight i else 0 := rfl

def columnTableau : BoundedTableau columnShape := ⟨SemistandardYoungTableau.highestWeight columnShape,by
  intro r c hm
  have h := (columnShape_mem r c).mp hm
  simp only [SemistandardYoungTableau.highestWeight_apply,if_pos hm]
  omega⟩

theorem rowTableau_ext {T U : BoundedTableau rowShape}
    (h0 : T.val 0 0=U.val 0 0) (h1 : T.val 0 1=U.val 0 1) : T=U := by
  apply Subtype.ext
  apply SemistandardYoungTableau.ext
  intro r c
  by_cases hm : (r,c)∈rowShape
  · have hs := (rowShape_mem r c).mp hm
    have hr : r=0 := hs.1
    subst r
    have hc : c=0 ∨ c=1 := by omega
    rcases hc with rfl|rfl <;> assumption
  · rw [T.val.zeros hm,U.val.zeros hm]

theorem all_rowTableaux (T : BoundedTableau rowShape) : ∃ i : Fin 3, T=rowTableau i := by
  have h0 := T.property 0 0 (by decide)
  have h1 := T.property 0 1 (by decide)
  have hle := T.val.row_weak (i:=0) (j1:=0) (j2:=1) (by decide) (by decide)
  have hc : (T.val 0 0=0 ∧ T.val 0 1=0) ∨
      (T.val 0 0=0 ∧ T.val 0 1=1) ∨ (T.val 0 0=1 ∧ T.val 0 1=1) := by omega
  rcases hc with h|h|h
  · exact ⟨0,rowTableau_ext h.1 h.2⟩
  · exact ⟨1,rowTableau_ext h.1 h.2⟩
  · exact ⟨2,rowTableau_ext h.1 h.2⟩

theorem rowTableau_injective : Function.Injective rowTableau := by
  intro i j h
  have h0 := congrArg (fun T : BoundedTableau rowShape => T.val 0 0) h
  have h1 := congrArg (fun T : BoundedTableau rowShape => T.val 0 1) h
  have hi : (rowTableau i).val 0 0+(rowTableau i).val 0 1=i.val := by fin_cases i <;> rfl
  have hj : (rowTableau j).val 0 0+(rowTableau j).val 0 1=j.val := by fin_cases j <;> rfl
  apply Fin.ext
  exact hi.symm.trans ((congrArg₂ Nat.add h0 h1).trans hj)

theorem all_columnTableaux (T : BoundedTableau columnShape) : T=columnTableau := by
  have h0 := T.property 0 0 (by decide)
  have h1 := T.property 1 0 (by decide)
  have hlt := T.val.col_strict (i1:=0) (i2:=1) (j:=0) (by decide) (by decide)
  have ht0 : T.val 0 0=0 := by omega
  have ht1 : T.val 1 0=1 := by omega
  apply Subtype.ext
  apply SemistandardYoungTableau.ext
  intro r c
  by_cases hm : (r,c)∈columnShape
  · have hs := (columnShape_mem r c).mp hm
    have hc : c=0 := hs.2
    subst c
    have hr : r=0 ∨ r=1 := by omega
    rcases hr with rfl|rfl
    · simpa [columnTableau,SemistandardYoungTableau.highestWeight_apply,columnShape_mem] using ht0
    · simpa [columnTableau,SemistandardYoungTableau.highestWeight_apply,columnShape_mem] using ht1
  · rw [T.val.zeros hm,columnTableau.val.zeros hm]

def rowTableauEquiv : Fin 3 ≃ BoundedTableau rowShape :=
  Equiv.ofBijective rowTableau ⟨rowTableau_injective,fun T => by
    obtain ⟨i,hi⟩ := all_rowTableaux T; exact ⟨i,hi.symm⟩⟩

def tableauContent {lam : YoungDiagram} (T : BoundedTableau lam) (k : Fin 2) : ℕ :=
  (lam.cells.filter (fun a => T.val a.1 a.2=k.val)).card

theorem rowTableau_content (i : Fin 3) : tableauContent (rowTableau i)=(composition i).val := by
  funext k
  fin_cases i <;> fin_cases k <;> decide

theorem columnTableau_content : tableauContent columnTableau=(composition 1).val := by
  funext k
  fin_cases k <;> decide

theorem three_cells_impossible (lam : YoungDiagram) (hc : lam.card=2)
    (a b c : ℕ×ℕ) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (ha : a∈lam) (hb : b∈lam) (hcc : c∈lam) : False := by
  have hs : ({a,b,c} : Finset (ℕ×ℕ))⊆lam.cells := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl <;> assumption
  have h := Finset.card_le_card hs
  have h3 : ({a,b,c} : Finset (ℕ×ℕ)).card=3 := by simp [hab,hac,hbc]
  rw [h3] at h
  change 3≤lam.card at h
  omega

theorem two_cells_bounds {lam : YoungDiagram} (hc : lam.card=2) {i j : ℕ}
    (hm : (i,j)∈lam) : i<2 ∧ j<2 := by
  constructor
  · by_contra hi
    have hi' : 2 ≤ i := by omega
    exact three_cells_impossible lam hc (0,0) (1,0) (2,0) (by decide) (by decide) (by decide)
      (lam.up_left_mem (by omega) (by omega) hm)
      (lam.up_left_mem (by omega) (by omega) hm)
      (lam.up_left_mem hi' (by omega) hm)
  · by_contra hj
    have hj' : 2 ≤ j := by omega
    exact three_cells_impossible lam hc (0,0) (0,1) (0,2) (by decide) (by decide) (by decide)
      (lam.up_left_mem (by omega) (by omega) hm)
      (lam.up_left_mem (by omega) (by omega) hm)
      (lam.up_left_mem (by omega) hj' hm)

theorem all_degree_two_shapes (lam : YoungDiagram) (hc : lam.card=2) :
    lam=rowShape ∨ lam=columnShape := by
  have hpos : 0<lam.cells.card := by change 0<lam.card; omega
  obtain ⟨⟨a,b⟩,hab⟩ := Finset.card_pos.mp hpos
  have h00 : (0,0)∈lam := lam.up_left_mem (by omega) (by omega) hab
  by_cases h01 : (0,1)∈lam
  · left
    apply YoungDiagram.ext
    apply Finset.ext
    rintro ⟨i,j⟩
    change (i,j)∈lam ↔ (i,j)∈rowShape
    rw [rowShape_mem]
    constructor
    · intro hm
      have hb := two_cells_bounds hc hm
      have hi : i=0 := by
        by_contra hni
        have h10 : (1,0)∈lam := lam.up_left_mem (by omega) (by omega) hm
        exact three_cells_impossible lam hc (0,0) (0,1) (1,0)
          (by decide) (by decide) (by decide) h00 h01 h10
      exact ⟨hi,by omega⟩
    · rintro ⟨rfl,hj⟩
      have hh : j=0 ∨ j=1 := by omega
      rcases hh with rfl|rfl <;> assumption
  · right
    have hjzero : ∀ {i j}, (i,j)∈lam → j=0 := by
      intro i j hm
      by_contra hn
      exact h01 (lam.up_left_mem (by omega) (by omega) hm)
    have h10 : (1,0)∈lam := by
      by_contra hn
      have hs : lam.cells⊆{(0,0)} := by
        rintro ⟨i,j⟩ hm
        have hj := hjzero hm
        have hi : i=0 := by
          by_contra hni
          exact hn (lam.up_left_mem (by omega) (by omega) hm)
        simp [hi,hj]
      have h := Finset.card_le_card hs
      change lam.card≤_ at h
      simp at h
      omega
    apply YoungDiagram.ext
    apply Finset.ext
    rintro ⟨i,j⟩
    change (i,j)∈lam ↔ (i,j)∈columnShape
    rw [columnShape_mem]
    constructor
    · intro hm
      have hb := two_cells_bounds hc hm
      exact ⟨by omega,hjzero hm⟩
    · rintro ⟨hi,rfl⟩
      have hh : i=0 ∨ i=1 := by omega
      rcases hh with rfl|rfl <;> assumption

def Dominates (lam mu : YoungDiagram) : Prop :=
  ∀ k : ℕ, (mu.rowLens.take k).sum≤(lam.rowLens.take k).sum

theorem row_dominates_column : Dominates rowShape columnShape := by
  have hr : rowShape.rowLens=[2] := YoungDiagram.rowLens_ofRowLens_eq_self (by simp)
  have hc : columnShape.rowLens=[1,1] := YoungDiagram.rowLens_ofRowLens_eq_self (by simp)
  intro k
  rw [hr,hc]
  cases k with
  | zero => decide
  | succ k => cases k with
    | zero => decide
    | succ k => simp

theorem not_column_dominates_row : ¬Dominates columnShape rowShape := by
  intro h
  have hh := h 1
  have hr : rowShape.rowLens=[2] := YoungDiagram.rowLens_ofRowLens_eq_self (by simp)
  have hc : columnShape.rowLens=[1,1] := YoungDiagram.rowLens_ofRowLens_eq_self (by simp)
  rw [hr,hc] at hh
  norm_num at hh

abbrev diagram : Bool → YoungDiagram
  | false => rowShape
  | true => columnShape

abbrev Tableau (s : Bool) := BoundedTableau (diagram s)

def contentComposition {s : Bool} (T : Tableau s) : WeakComposition :=
  ⟨tableauContent T,by
    cases s
    · obtain ⟨i,rfl⟩ := all_rowTableaux T
      rw [rowTableau_content]
      exact (composition i).property
    · rw [all_columnTableaux T,columnTableau_content]
      exact (composition 1).property⟩

@[simp] theorem row_contentComposition (i : Fin 3) :
    contentComposition (s:=false) (rowTableau i)=composition i := by
  apply Subtype.ext
  exact rowTableau_content i

@[simp] theorem column_contentComposition :
    contentComposition (s:=true) columnTableau=composition 1 := by
  apply Subtype.ext
  exact columnTableau_content

abbrev Standard (s : Bool) := {T : Tableau s // tableauContent T=(composition 1).val}

def initialStandard : (s : Bool) → Standard s
  | false => ⟨rowTableau 1,rowTableau_content 1⟩
  | true => ⟨columnTableau,columnTableau_content⟩

theorem standard_unique (s : Bool) (T : Standard s) : T=initialStandard s := by
  cases s
  · rcases T with ⟨T,h⟩
    obtain ⟨i,rfl⟩ := all_rowTableaux T
    rw [rowTableau_content] at h
    have h0 := congrFun h 0
    have hi : i=1 := by
      fin_cases i
      · norm_num [composition] at h0
      · rfl
      · norm_num [composition] at h0
    subst i
    rfl
  · apply Subtype.ext
    exact all_columnTableaux T.val

instance standardUnique (s : Bool) : Unique (Standard s) where
  default := initialStandard s
  uniq := standard_unique s

instance standardFintype (s : Bool) : Fintype (Standard s) := Fintype.ofSubsingleton (initialStandard s)

def cellPosition (s : Bool) (i : Fin 2) : ℕ×ℕ :=
  if s then (i.val,0) else (0,i.val)

theorem cellPosition_mem (s : Bool) (i : Fin 2) : cellPosition s i∈diagram s := by
  cases s <;> fin_cases i <;> decide

def standardLabel {s : Bool} (T : Standard s) (i : Fin 2) : Fin 2 :=
  ⟨T.val.val (cellPosition s i).1 (cellPosition s i).2,
    T.val.property _ _ (cellPosition_mem s i)⟩

theorem standardLabel_eq {s : Bool} (T : Standard s) (i : Fin 2) : standardLabel T i=i := by
  rw [standard_unique s T]
  cases s <;> fin_cases i <;> rfl

def standardPermutation {s : Bool} (T : Standard s) : G :=
  Equiv.ofBijective (standardLabel T) (by
    have h : standardLabel T=id := funext (standardLabel_eq T)
    rw [h]
    exact Function.bijective_id)

@[simp] theorem standardPermutation_eq {s : Bool} (T : Standard s) : standardPermutation T=1 := by
  apply Equiv.ext
  exact standardLabel_eq T

def coarsened {s : Bool} (μ : WeakComposition) (T : Standard s) (r c : ℕ) : ℕ :=
  if h : (r,c)∈diagram s then
    (rowOf μ ⟨T.val.val r c,T.val.property r c h⟩).val else 0

theorem coarsened_row (i : Fin 3) (T : Standard false) :
    coarsened (composition i) T=(rowTableau i).val := by
  rw [standard_unique false T]
  funext r c
  by_cases hm : (r,c)∈rowShape
  · have hs := (rowShape_mem r c).mp hm
    have hr : r=0 := hs.1
    have hc : c=0 ∨ c=1 := by omega
    subst r
    rcases hc with rfl|rfl <;> fin_cases i <;> rfl
  · rw [(rowTableau i).val.zeros hm]
    simp [coarsened,diagram,hm]

theorem coarsened_column (T : Standard true) :
    coarsened (composition 1) T=columnTableau.val := by
  rw [standard_unique true T]
  funext r c
  by_cases hm : (r,c)∈columnShape
  · have hs := (columnShape_mem r c).mp hm
    have hc : c=0 := hs.2
    have hr : r=0 ∨ r=1 := by omega
    subst c
    rcases hr with rfl|rfl <;> rfl
  · rw [columnTableau.val.zeros hm]
    simp [coarsened,diagram,hm]

theorem coarsened_content {s : Bool} (U : Tableau s) (T : Standard s) :
    coarsened (contentComposition U) T=U.val := by
  cases s
  · obtain ⟨i,rfl⟩ := all_rowTableaux U
    rw [row_contentComposition]
    exact coarsened_row i T
  · rw [all_columnTableaux U,column_contentComposition]
    exact coarsened_column T

def shapeComposition : Bool → WeakComposition
  | false => composition 0
  | true => composition 1

def murphyElement {s : Bool} (a b : Standard s) : H :=
  heckeBasis (standardPermutation a).symm * youngSymmetrizer (shapeComposition s) *
    heckeBasis (standardPermutation b)

theorem murphyElement_eq {s : Bool} (a b : Standard s) :
    murphyElement a b=youngSymmetrizer (shapeComposition s) := by
  simp only [murphyElement,standardPermutation_eq]
  have h : (1:G).symm=1 := rfl
  rw [h]
  simp [heckeBasis]

def mST {s : Bool} (U V : Tableau s) : H := by
  classical
  exact ∑ ab : Standard s × Standard s,
    if coarsened (contentComposition U) ab.1=U.val ∧
       coarsened (contentComposition V) ab.2=V.val
    then murphyElement ab.1 ab.2 else 0

theorem mST_eq {s : Bool} (U V : Tableau s) : mST U V=youngSymmetrizer (shapeComposition s) := by
  classical
  simp [mST,coarsened_content,murphyElement_eq]

@[simp] theorem mST_row (i j : Fin 3) : mST (s:=false) (rowTableau i) (rowTableau j)=eps := by
  rw [mST_eq (s:=false)]
  exact youngSymmetrizer_zero

@[simp] theorem mST_column (U V : Tableau true) : mST U V=1 := by
  rw [mST_eq]
  exact youngSymmetrizer_one

def permutationGenerator (μ : WeakComposition) (h : H) : PermutationSum :=
  Pi.single μ ⟨youngSymmetrizer μ*h,by
    rw [permutationIdeal,Ideal.mem_span_singleton]
    exact ⟨h,rfl⟩⟩

theorem permutationEquiv_val (x : M) (i : Fin 3) :
    (permutationEquiv x (composition i)).val=
      if i=0 then TrivSqZeroExt.inr x.1 else if i=1 then x.2.1 else TrivSqZeroExt.inr x.2.2 := by
  fin_cases i <;> rfl

theorem permutationEquiv_generator (i : Fin 3) (h : H) :
    permutationEquiv (h • inputVector i)=permutationGenerator (composition i) h := by
  funext μ
  apply Subtype.ext
  obtain ⟨j,rfl⟩ := all_compositions μ
  rw [permutationEquiv_val]
  fin_cases i <;> fin_cases j <;> ext <;>
    simp [permutationGenerator,composition_bijective.1.eq_iff,inputVector,topVector,
      eps,base_smul,smul_eq_mul]

theorem permutationEquiv_socle (i k : Fin 3) (h : H) :
    (permutationEquiv (h • socleVector i) (composition k)).val=
      if k=i then eps*h else 0 := by
  rw [permutationEquiv_val]
  fin_cases i <;> fin_cases k <;> ext <;> simp [socleVector,eps,base_smul,smul_eq_mul]

theorem fullQSchurEquiv_on_image (f : S) (x : M) :
    fullQSchurEquiv f (permutationEquiv x)=permutationEquiv (f x) := by
  change permutationEquiv (f (permutationEquiv.symm (permutationEquiv x)))=permutationEquiv (f x)
  rw [LinearEquiv.symm_apply_apply]

theorem phi_on_generator (i j k : Fin 3) (h : H) :
    phi i j (h • inputVector k)=if j=k then h • socleVector i else 0 := by
  rw [map_smul,phi_apply,row_input]
  split_ifs
  · simp
  · rw [zero_smul]
    ext <;> simp [base_smul,smul_eq_mul]

theorem e_on_generator (k : Fin 3) (h : H) :
    e (h • inputVector k)=if k=1 then h • topVector else 0 := by
  rw [map_smul]
  fin_cases k <;> simp [inputVector,topVector]

def cellOperator : (s : Bool) → Tableau s → Tableau s → S
  | false,U,V => phi (rowTableauEquiv.symm U) (rowTableauEquiv.symm V)
  | true,_,_ => e

@[simp] theorem cellOperator_row (i j : Fin 3) :
    cellOperator false (rowTableau i) (rowTableau j)=phi i j := by
  change phi (rowTableauEquiv.symm (rowTableauEquiv i))
    (rowTableauEquiv.symm (rowTableauEquiv j))=phi i j
  simp

@[simp] theorem cellOperator_column (U V : Tableau true) : cellOperator true U V=e := rfl

/-- The actual all-generator formula4.13, in every summand of the full native permutation sum. -/
theorem cellOperator_formula413 (s : Bool) (U V : Tableau s) (μ ν : WeakComposition) (h : H) :
    ((fullQSchurEquiv (cellOperator s U V)) (permutationGenerator μ h) ν).val=
      if μ=contentComposition V ∧ ν=contentComposition U then mST U V*h else 0 := by
  cases s
  · obtain ⟨i,rfl⟩ := all_rowTableaux U
    obtain ⟨j,rfl⟩ := all_rowTableaux V
    obtain ⟨k,rfl⟩ := all_compositions μ
    obtain ⟨l,rfl⟩ := all_compositions ν
    rw [cellOperator_row,← permutationEquiv_generator k h,fullQSchurEquiv_on_image,phi_on_generator]
    by_cases hjk : j=k
    · subst k
      rw [if_pos rfl,permutationEquiv_socle]
      simp [composition_bijective.1.eq_iff]
    · rw [if_neg hjk]
      simp [composition_bijective.1.eq_iff,hjk,Ne.symm hjk]
  · rw [all_columnTableaux U,all_columnTableaux V]
    obtain ⟨k,rfl⟩ := all_compositions μ
    obtain ⟨l,rfl⟩ := all_compositions ν
    rw [cellOperator_column,← permutationEquiv_generator k h,fullQSchurEquiv_on_image,e_on_generator]
    fin_cases k <;> fin_cases l <;>
      simp [permutationEquiv_val,composition_bijective.1.eq_iff,topVector,eps]

instance columnTableau_subsingleton : Subsingleton (BoundedTableau columnShape) where
  allEq T U := (all_columnTableaux T).trans (all_columnTableaux U).symm

instance tableauxFintype (s : Bool) : Fintype (Tableau s) := by
  cases s
  · exact Fintype.ofEquiv (Fin 3) rowTableauEquiv
  · exact Fintype.ofSubsingleton columnTableau

abbrev SemistandardIndex := Σ s : Bool, Tableau s × Tableau s

def semistandardIndexEquiv : CellIndex ≃ SemistandardIndex where
  toFun a := match a with
    | none => ⟨true,(columnTableau,columnTableau)⟩
    | some (i,j) => ⟨false,(rowTableau i,rowTableau j)⟩
  invFun a := match a with
    | ⟨true,_⟩ => none
    | ⟨false,(U,V)⟩ => some (rowTableauEquiv.symm U,rowTableauEquiv.symm V)
  left_inv a := by
    cases a with
    | none => rfl
    | some a =>
      rcases a with ⟨i,j⟩
      change some (rowTableauEquiv.symm (rowTableauEquiv i),rowTableauEquiv.symm (rowTableauEquiv j))=some (i,j)
      simp
  right_inv a := by
    rcases a with ⟨s,U,V⟩
    cases s
    · change (⟨false,(rowTableauEquiv (rowTableauEquiv.symm U),
        rowTableauEquiv (rowTableauEquiv.symm V))⟩ : SemistandardIndex)=⟨false,(U,V)⟩
      simp
    · rw [all_columnTableaux U,all_columnTableaux V]

def semistandardBasis : Basis SemistandardIndex K S := fullCellBasis.reindex semistandardIndexEquiv

theorem semistandardBasis_operator (s : Bool) (U V : Tableau s) :
    semistandardBasis ⟨s,(U,V)⟩=cellOperator s U V := by
  cases s <;>
    simp [semistandardBasis,Basis.reindex_apply,fullCellBasis_apply,semistandardIndexEquiv,cell,cellOperator]

theorem semistandard_index_card : Fintype.card SemistandardIndex=10 := by
  rw [← Fintype.card_congr semistandardIndexEquiv]
  simp [CellIndex]

theorem semistandard_anti (s : Bool) (U V : Tableau s) :
    cellAnti (cellOperator s U V)=cellOperator s V U := by
  cases s <;> simp [cellOperator]

theorem rowShape_ne_columnShape : rowShape≠columnShape := by
  intro h
  have hm : (0,1)∈rowShape := by decide
  rw [h,columnShape_mem] at hm
  omega

def higherCellSpan (s : Bool) : Submodule K S := Submodule.span K
  {f | ∃ t : Bool, ∃ U V : Tableau t,
    Dominates (diagram t) (diagram s) ∧ diagram t≠diagram s ∧ f=cellOperator t U V}

theorem higherCellSpan_column : higherCellSpan true=higherSpan := by
  unfold higherCellSpan higherSpan
  apply congrArg (Submodule.span K)
  apply Set.ext
  intro f
  constructor
  · rintro ⟨t,U,V,hd,hne,rfl⟩
    cases t
    · exact ⟨(rowTableauEquiv.symm U,rowTableauEquiv.symm V),rfl⟩
    · exact False.elim (hne rfl)
  · rintro ⟨⟨i,j⟩,rfl⟩
    exact ⟨false,rowTableau i,rowTableau j,row_dominates_column,rowShape_ne_columnShape,
      (cellOperator_row i j).symm⟩

theorem higherCellSpan_row : higherCellSpan false=⊥ := by
  unfold higherCellSpan
  have hs : {f | ∃ t : Bool, ∃ U V : Tableau t,
      Dominates (diagram t) (diagram false) ∧ diagram t≠diagram false ∧ f=cellOperator t U V} = ∅ := by
    apply Set.ext
    intro f
    constructor
    · rintro ⟨t,U,V,hd,hne,hf⟩
      cases t
      · exact False.elim (hne rfl)
      · exact False.elim (not_column_dominates_row hd)
    · intro h
      cases h
  rw [hs,Submodule.span_empty]

def rowRightCoefficient (f : S) (j k : Fin 3) : K :=
  if j=1 then if k=1 then alpha f else 0 else entry f j k

theorem row_cell_triangularity (i j : Fin 3) (f : S) :
    phi i j*f=∑ k : Fin 3, rowRightCoefficient f j k • phi i k := by
  conv_lhs => rw [end_reconstruction f]
  fin_cases j <;>
    simp [Fin.sum_univ_three,rowRightCoefficient,mul_add,mul_smul_comm]

theorem column_cell_triangularity (f : S) : e*f-alpha f • e∈higherCellSpan true := by
  rw [higherCellSpan_column,higherSpan_mem_iff]
  change alpha (e*f)-alpha (alpha f • e)=0
  simp

/-- This is the actual dominance ideal used by the native right cell quotient. -/
theorem column_higher_ideal (f : S) : f∈higherRight ↔ f∈higherCellSpan true := by
  rw [higherRight_mem_iff,higherCellSpan_column]

/-- The generator in the published column cell definition is e, not the global identity. -/
theorem column_generator_is_regular_projection :
    cellOperator true columnTableau columnTableau=e ∧
      (1:S)=e+phi 0 0+phi 2 2 := ⟨rfl,identity_decomposition⟩

/-- A genuine semisimple q-Schur cell module with a hook divisible by the root order. -/
theorem rank_two_cell_counterexample :
    IsPrimitiveRoot (-1:K) 2 ∧ 2≤5 ∧
    Module.finrank K S=10 ∧ Module.finrank K columnCell=1 ∧
    IsSimpleModule Sᵐᵒᵖ columnCell ∧ IsSemisimpleModule Sᵐᵒᵖ columnCell ∧
    ∃ a∈columnShape.cells, 2∣hookLength columnShape a :=
  ⟨q_primitive,by decide,fullEnd_finrank,columnCell_finrank,
    inferInstance,columnCell_semisimple,column_divisible_hook⟩

theorem printed_necessary_hook_condition_false :
    ¬(IsSemisimpleModule Sᵐᵒᵖ columnCell →
      ∀ a∈columnShape.cells, ¬2∣hookLength columnShape a) := by
  intro h
  obtain ⟨a,ha,hdiv⟩ := column_divisible_hook
  exact h columnCell_semisimple a ha hdiv

/-! The native cell quotient over End_H of the complete actual permutation sum. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def fullQSchurComplexEquiv : S ≃ₐ[K] ActualQSchur := fullQSchurEquiv.restrictScalars K

def actualSemistandardBasis : Basis SemistandardIndex K ActualQSchur :=
  semistandardBasis.map fullQSchurComplexEquiv.toLinearEquiv

theorem actualSemistandardBasis_operator (s : Bool) (U V : Tableau s) :
    actualSemistandardBasis ⟨s,(U,V)⟩=fullQSchurEquiv (cellOperator s U V) := by
  rw [actualSemistandardBasis,Basis.map_apply,semistandardBasis_operator]
  rfl

def actualAnti : ActualQSchur →ₗ[K] ActualQSchur :=
  fullQSchurComplexEquiv.toLinearEquiv.conj cellAnti

theorem actualAnti_image (f : S) : actualAnti (fullQSchurComplexEquiv f)=
    fullQSchurComplexEquiv (cellAnti f) := by
  change fullQSchurComplexEquiv (cellAnti (fullQSchurComplexEquiv.symm (fullQSchurComplexEquiv f)))=_
  rw [AlgEquiv.symm_apply_apply]

theorem actualAnti_involutive (f : ActualQSchur) : actualAnti (actualAnti f)=f := by
  obtain ⟨x,rfl⟩ := fullQSchurComplexEquiv.surjective f
  rw [actualAnti_image,actualAnti_image,cellAnti_involutive]

theorem actualAnti_mul (f g : ActualQSchur) : actualAnti (f*g)=actualAnti g*actualAnti f := by
  obtain ⟨x,rfl⟩ := fullQSchurComplexEquiv.surjective f
  obtain ⟨y,rfl⟩ := fullQSchurComplexEquiv.surjective g
  rw [← map_mul,actualAnti_image,cellAnti_mul,map_mul,actualAnti_image,actualAnti_image]

def actualCharacter : ActualQSchur →ₐ[K] K :=
  scalarCharacter.comp fullQSchurComplexEquiv.symm.toAlgHom

@[simp] theorem actualCharacter_image (f : S) : actualCharacter (fullQSchurComplexEquiv f)=alpha f := by
  change alpha (fullQSchurComplexEquiv.symm (fullQSchurComplexEquiv f))=alpha f
  rw [AlgEquiv.symm_apply_apply]

def actualProjection : ActualQSchur := fullQSchurComplexEquiv e

@[simp] theorem actualCharacter_projection : actualCharacter actualProjection=1 := actualCharacter_image e

def actualHigherSpan : Submodule K ActualQSchur :=
  (higherCellSpan true).map fullQSchurComplexEquiv.toLinearMap

theorem actualHigherSpan_mem (f : ActualQSchur) : f∈actualHigherSpan ↔ actualCharacter f=0 := by
  rw [actualHigherSpan,Submodule.mem_map]
  constructor
  · rintro ⟨x,hx,rfl⟩
    change actualCharacter (fullQSchurComplexEquiv x)=0
    rw [actualCharacter_image]
    rw [higherCellSpan_column,higherSpan_mem_iff] at hx
    exact hx
  · intro hf
    refine ⟨fullQSchurComplexEquiv.symm f,?_,fullQSchurComplexEquiv.apply_symm_apply f⟩
    rw [higherCellSpan_column,higherSpan_mem_iff]
    exact hf

def actualOppositeCharacter : ActualQSchurᵐᵒᵖ →+* K where
  toFun s := actualCharacter s.unop
  map_one' := map_one actualCharacter
  map_zero' := map_zero actualCharacter
  map_add' x y := map_add actualCharacter x.unop y.unop
  map_mul' x y := by change actualCharacter (y.unop*x.unop)=_;simp [mul_comm]

instance actualRightScalarModule : Module ActualQSchurᵐᵒᵖ K := Module.compHom K actualOppositeCharacter

@[simp] theorem actual_right_scalar_smul (s : ActualQSchurᵐᵒᵖ) (c : K) :
    s • c=actualCharacter s.unop*c := rfl

instance actualRightScalarTower : IsScalarTower K ActualQSchurᵐᵒᵖ K where
  smul_assoc c s x := by
    change actualCharacter ((c • s).unop)*x=c*(actualCharacter s.unop*x)
    simp [mul_assoc]

def actualRightCharacter : ActualQSchur →ₗ[ActualQSchurᵐᵒᵖ] K where
  toFun := actualCharacter
  map_add' := map_add actualCharacter
  map_smul' s f := by
    change actualCharacter (f*s.unop)=actualCharacter s.unop*actualCharacter f
    simp [mul_comm]

theorem actualRightCharacter_surjective : Function.Surjective actualRightCharacter := by
  intro c
  exact ⟨algebraMap K ActualQSchur c,actualCharacter.commutes c⟩

local instance actualQuotientAddGroup : AddCommGroup ActualQSchur :=
  { (inferInstance : AddCommGroup ActualQSchur) with
    toAddCommMonoid := (inferInstance : AddCommMonoid ActualQSchur) }

local instance actualQuotientOppositeRing : Ring ActualQSchurᵐᵒᵖ :=
  { (inferInstance : Ring ActualQSchurᵐᵒᵖ) with
    toSemiring := (inferInstance : Semiring ActualQSchurᵐᵒᵖ) }

instance actualRightEndTower : IsScalarTower K ActualQSchurᵐᵒᵖ ActualQSchur where
  smul_assoc c s f := by
    change f * (c • s.unop)=c • (f*s.unop)
    exact mul_smul_comm c f s.unop

def actualHigherRight : Submodule ActualQSchurᵐᵒᵖ ActualQSchur := LinearMap.ker actualRightCharacter
abbrev ActualCellQuotient := ActualQSchur ⧸ actualHigherRight

theorem actual_higher_ideal (f : ActualQSchur) : f∈actualHigherRight ↔ f∈actualHigherSpan := by
  rw [actualHigherSpan_mem]
  rfl

def actualQuotientCharacter : ActualCellQuotient ≃ₗ[ActualQSchurᵐᵒᵖ] K :=
  actualRightCharacter.quotKerEquivOfSurjective actualRightCharacter_surjective

@[simp] theorem actualQuotientCharacter_mk (f : ActualQSchur) :
    actualQuotientCharacter (actualHigherRight.mkQ f)=actualCharacter f :=
  actualRightCharacter.quotKerEquivOfSurjective_apply_mk actualRightCharacter_surjective f

instance actualRightScalar_simple : IsSimpleModule ActualQSchurᵐᵒᵖ K := by
  apply isSimpleModule_iff_toSpanSingleton_surjective.mpr
  refine ⟨inferInstance,?_⟩
  intro x hx y
  refine ⟨MulOpposite.op (algebraMap K ActualQSchur (y/x)),?_⟩
  change actualCharacter (algebraMap K ActualQSchur (y/x))*x=y
  rw [AlgHom.commutes]
  exact div_mul_cancel₀ y hx

def actualColumnCell : Submodule ActualQSchurᵐᵒᵖ ActualCellQuotient :=
  Submodule.span ActualQSchurᵐᵒᵖ {actualHigherRight.mkQ actualProjection}

theorem actualColumnCell_eq_top : actualColumnCell=⊤ := by
  apply top_unique
  intro q _
  have hz : actualHigherRight.mkQ actualProjection∈actualColumnCell := Submodule.subset_span (by simp)
  have heq : q=MulOpposite.op (algebraMap K ActualQSchur (actualQuotientCharacter q)) •
      actualHigherRight.mkQ actualProjection := by
    apply actualQuotientCharacter.injective
    rw [map_smul]
    change actualQuotientCharacter q=actualCharacter (algebraMap K ActualQSchur (actualQuotientCharacter q))*
      actualQuotientCharacter (actualHigherRight.mkQ actualProjection)
    rw [actualQuotientCharacter_mk,actualCharacter_projection,AlgHom.commutes,mul_one]
    simp
  rw [heq]
  exact actualColumnCell.smul_mem _ hz

def actualColumnCellEquiv : actualColumnCell ≃ₗ[ActualQSchurᵐᵒᵖ] K :=
  (LinearEquiv.ofEq _ _ actualColumnCell_eq_top).trans ((Submodule.topEquiv).trans actualQuotientCharacter)

instance actualColumnCell_simple : IsSimpleModule ActualQSchurᵐᵒᵖ actualColumnCell :=
  IsSimpleModule.congr actualColumnCellEquiv

def actualColumnCellComplexEquiv : actualColumnCell ≃ₗ[K] K := actualColumnCellEquiv.restrictScalars K

instance actualColumnCell_finite : Module.Finite K actualColumnCell :=
  Module.Finite.equiv actualColumnCellComplexEquiv.symm

theorem actualColumnCell_finrank : Module.finrank K actualColumnCell=1 := by
  simpa using actualColumnCellComplexEquiv.finrank_eq

theorem actualQSchur_finrank : Module.finrank K ActualQSchur=10 :=
  fullQSchurComplexEquiv.toLinearEquiv.finrank_eq.symm.trans fullEnd_finrank

theorem actual_column_generator :
    fullQSchurEquiv (cellOperator true columnTableau columnTableau)=actualProjection := rfl

theorem actual_qSchur_counterexample :
    IsPrimitiveRoot (-1:K) 2 ∧ 2≤5 ∧
    Module.finrank K ActualQSchur=10 ∧ Module.finrank K actualColumnCell=1 ∧
    IsSimpleModule ActualQSchurᵐᵒᵖ actualColumnCell ∧
    IsSemisimpleModule ActualQSchurᵐᵒᵖ actualColumnCell ∧
    ∃ a∈columnShape.cells, 2∣hookLength columnShape a :=
  ⟨q_primitive,by decide,actualQSchur_finrank,actualColumnCell_finrank,
    inferInstance,inferInstance,column_divisible_hook⟩

theorem actual_necessary_hook_condition_false :
    ¬(IsSemisimpleModule ActualQSchurᵐᵒᵖ actualColumnCell →
      ∀ a∈columnShape.cells, ¬2∣hookLength columnShape a) := by
  intro h
  obtain ⟨a,ha,hdiv⟩ := column_divisible_hook
  exact h inferInstance a ha hdiv

end
end TLMC1770
