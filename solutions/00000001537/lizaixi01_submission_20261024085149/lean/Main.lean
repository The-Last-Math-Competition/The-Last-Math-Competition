import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Logic.Equiv.Sum
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
Ordinary integral cyclic cohomology in its standard normalized (b*,B*) model.
The actual quotient algebra, full normalized multilinear spaces, standard
operators on every input, full native total complex and its native homology
are constructed below.  Degree zero has no element of additive order two,
whereas degree two has one, so the groups are not two-periodic from degree zero.
-/

open scoped BigOperators
open Polynomial

namespace TLMC1537

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

abbrev D := DualNumber ℤ
abbrev definingPolynomial : ℤ[X] := X ^ 2
abbrev R := AdjoinRoot definingPolynomial

def quotientToDual : R →ₐ[ℤ] D :=
  AdjoinRoot.liftAlgHom definingPolynomial (Algebra.ofId ℤ D) DualNumber.eps
    (by simp [definingPolynomial, DualNumber.eps_pow_two])

theorem root_square_zero : (AdjoinRoot.root definingPolynomial : R) ^ 2 = 0 := by
  simpa [definingPolynomial] using AdjoinRoot.eval₂_root definingPolynomial

def dualToQuotient : D →ₐ[ℤ] R :=
  DualNumber.lift ⟨(Algebra.ofId ℤ R, AdjoinRoot.root definingPolynomial),
    by simpa [pow_two] using root_square_zero, fun _ => Commute.all _ _⟩

@[simp] theorem quotientToDual_root :
    quotientToDual (AdjoinRoot.root definingPolynomial) = DualNumber.eps := by
  simp [quotientToDual]

@[simp] theorem dualToQuotient_eps :
    dualToQuotient DualNumber.eps = AdjoinRoot.root definingPolynomial := by
  simp [dualToQuotient]

theorem quotient_left_inverse : Function.LeftInverse dualToQuotient quotientToDual := by
  have h : dualToQuotient.comp quotientToDual = AlgHom.id ℤ R := by
    apply AdjoinRoot.algHom_ext
    simp
  exact fun x => DFunLike.congr_fun h x

theorem quotient_right_inverse : Function.RightInverse dualToQuotient quotientToDual := by
  have h : quotientToDual.comp dualToQuotient = AlgHom.id ℤ D := by
    apply DualNumber.algHom_ext
    simp
  exact fun x => DFunLike.congr_fun h x

def quotientDualEquiv : R ≃ₐ[ℤ] D where
  toFun := quotientToDual
  invFun := dualToQuotient
  left_inv := quotient_left_inverse
  right_inv := quotient_right_inverse
  map_mul' := quotientToDual.map_mul
  map_add' := quotientToDual.map_add
  commutes' := quotientToDual.commutes

def dualBasis : Module.Basis (Fin 2) ℤ D := Module.Basis.finTwoProd ℤ

@[simp] theorem dualBasis_zero : dualBasis 0 = 1 :=
  Module.Basis.finTwoProd_zero ℤ

@[simp] theorem dualBasis_one : dualBasis 1 = DualNumber.eps :=
  Module.Basis.finTwoProd_one ℤ

def constantPart : D →ₗ[ℤ] ℤ where
  toFun := TrivSqZeroExt.fst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def epsilonPart : D →ₗ[ℤ] ℤ where
  toFun := TrivSqZeroExt.snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def firstFunctional (a b : ℤ) : D →ₗ[ℤ] ℤ := a • constantPart + b • epsilonPart

abbrev Cochains (n : ℕ) := MultilinearMap ℤ (fun _ : Fin (n + 1) => D) ℤ

def normalizedSubmodule (n : ℕ) : Submodule ℤ (Cochains n) where
  carrier := {f | ∀ i : Fin (n + 1), i ≠ 0 →
    ∀ x : Fin (n + 1) → D, x i = 1 → f x = 0}
  zero_mem' := by
    change ∀ (i : Fin (n + 1)), i ≠ 0 →
      ∀ x : Fin (n + 1) → D, x i = 1 → (0 : Cochains n) x = 0
    intros
    rfl
  add_mem' hf hg i hi x hx := by simp [hf i hi x hx, hg i hi x hx]
  smul_mem' a f hf i hi x hx := by simp [hf i hi x hx]

abbrev NormalizedCochains (n : ℕ) := normalizedSubmodule n

def cochainForm (n : ℕ) (a b : ℤ) : Cochains n :=
  (MultilinearMap.mkPiAlgebra ℤ (Fin (n + 1)) ℤ).compLinearMap
    (fun i => if i = 0 then firstFunctional a b else epsilonPart)

theorem cochainForm_normalized (n : ℕ) (a b : ℤ) :
    cochainForm n a b ∈ normalizedSubmodule n := by
  intro i hi x hx
  change (∏ j : Fin (n + 1),
    (if j = 0 then firstFunctional a b else epsilonPart) (x j)) = 0
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hi, hx, epsilonPart, TrivSqZeroExt.snd_one]

def normalizedForm (n : ℕ) (a b : ℤ) : NormalizedCochains n :=
  ⟨cochainForm n a b, cochainForm_normalized n a b⟩

def unitFirst (n : ℕ) (i : Fin (n + 1)) : D :=
  if i = 0 then 1 else DualNumber.eps

def epsilonAll (n : ℕ) : Fin (n + 1) → D := fun _ => DualNumber.eps

@[simp] theorem form_on_unitFirst (n : ℕ) (a b : ℤ) :
    cochainForm n a b (unitFirst n) = a := by
  simp [cochainForm, unitFirst, firstFunctional, constantPart, epsilonPart,
    Fin.prod_univ_succ]

@[simp] theorem form_on_epsilonAll (n : ℕ) (a b : ℤ) :
    cochainForm n a b (epsilonAll n) = b := by
  simp [cochainForm, epsilonAll, firstFunctional, constantPart, epsilonPart,
    Fin.prod_univ_succ]

theorem normalized_ext {n : ℕ} (f g : NormalizedCochains n)
    (h₀ : f.1 (unitFirst n) = g.1 (unitFirst n))
    (h₁ : f.1 (epsilonAll n) = g.1 (epsilonAll n)) : f = g := by
  apply Subtype.ext
  apply Module.Basis.ext_multilinear (fun _ => dualBasis)
  intro c
  by_cases hz : ∃ i : Fin (n + 1), i ≠ 0 ∧ c i = 0
  · obtain ⟨i, hi, hc⟩ := hz
    rw [f.2 i hi _ (by simp [hc]), g.2 i hi _ (by simp [hc])]
  · have hc : ∀ i : Fin (n + 1), i ≠ 0 → c i = 1 := by
      intro i hi
      have hn : c i ≠ 0 := fun h => hz ⟨i, hi, h⟩
      apply Fin.ext
      have hb := (c i).isLt
      have hn' : (c i).val ≠ 0 := fun h => hn (Fin.ext h)
      change (c i).val = 1
      omega
    by_cases hzero : c 0 = 0
    · have he : (fun i => dualBasis (c i)) = unitFirst n := by
        funext i
        by_cases hi : i = 0
        · subst i; simp [hzero, unitFirst]
        · simp [hc i hi, unitFirst, hi]
      simpa only [he] using h₀
    · have hone : c 0 = 1 := by
        apply Fin.ext
        have hb := (c 0).isLt
        have hn' : (c 0).val ≠ 0 := fun h => hzero (Fin.ext h)
        change (c 0).val = 1
        omega
      have he : (fun i => dualBasis (c i)) = epsilonAll n := by
        funext i
        by_cases hi : i = 0
        · subst i; simp [hone, epsilonAll]
        · simp [hc i hi, epsilonAll]
      simpa only [he] using h₁

def normalizedCoordinates (n : ℕ) : NormalizedCochains n ≃ₗ[ℤ] (ℤ × ℤ) where
  toFun f := (f.1 (unitFirst n), f.1 (epsilonAll n))
  invFun ab := normalizedForm n ab.1 ab.2
  left_inv _f := normalized_ext _ _ (form_on_unitFirst _ _ _) (form_on_epsilonAll _ _ _)
  right_inv _ab := Prod.ext (form_on_unitFirst _ _ _) (form_on_epsilonAll _ _ _)
  map_add' _f _g := rfl
  map_smul' _a _f := rfl

/- The following tuple maps are the actual Hochschild faces, not assigned
   matrices.  The first n+1 faces multiply two adjacent entries; the last
   face multiplies the last and first entries in that order. -/
def adjacentTuple {n : ℕ} (x : Fin (n + 2) → D) (j : Fin (n + 1)) :
    Fin (n + 1) → D := fun k =>
  if k < j then x k.castSucc
  else if k = j then x k.castSucc * x k.succ
  else x k.succ

def finalTuple {n : ℕ} (x : Fin (n + 2) → D) : Fin (n + 1) → D :=
  Fin.cons (x (Fin.last (n + 1)) * x 0) (fun i => x i.succ.castSucc)

def hochschildEvaluation {n : ℕ} (f : Cochains n) (x : Fin (n + 2) → D) : ℤ :=
  (∑ j : Fin (n + 1), (-1 : ℤ) ^ j.val * f (adjacentTuple x j)) +
    (-1 : ℤ) ^ (n + 1) * f (finalTuple x)

theorem adjacent_unit_zero (n : ℕ) :
    adjacentTuple (unitFirst (n + 1)) 0 = epsilonAll n := by
  funext k
  by_cases hk : k = 0
  · subst k; simp [adjacentTuple, unitFirst, epsilonAll]
  · simp [adjacentTuple, unitFirst, epsilonAll, hk]

theorem adjacent_unit_positive {n : ℕ} (f : Cochains n) (j : Fin (n + 1))
    (hj : j ≠ 0) : f (adjacentTuple (unitFirst (n + 1)) j) = 0 := by
  apply f.map_coord_zero j
  simp [adjacentTuple, unitFirst, hj, ← pow_two, DualNumber.eps_pow_two]

theorem adjacent_epsilon {n : ℕ} (f : Cochains n) (j : Fin (n + 1)) :
    f (adjacentTuple (epsilonAll (n + 1)) j) = 0 := by
  apply f.map_coord_zero j
  simp [adjacentTuple, epsilonAll, ← pow_two, DualNumber.eps_pow_two]

theorem final_unit (n : ℕ) : finalTuple (unitFirst (n + 1)) = epsilonAll n := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [finalTuple, unitFirst, epsilonAll]
  · simp [finalTuple, unitFirst, epsilonAll]

theorem final_epsilon {n : ℕ} (f : Cochains n) :
    f (finalTuple (epsilonAll (n + 1))) = 0 := by
  apply f.map_coord_zero 0
  simp [finalTuple, epsilonAll, ← pow_two, DualNumber.eps_pow_two]

theorem hochschild_on_unit {n : ℕ} (f : Cochains n) :
    hochschildEvaluation f (unitFirst (n + 1)) =
      (1 + (-1 : ℤ) ^ (n + 1)) * f (epsilonAll n) := by
  rw [hochschildEvaluation]
  have h : (∑ j : Fin (n + 1), (-1 : ℤ) ^ j.val *
      f (adjacentTuple (unitFirst (n + 1)) j)) = f (epsilonAll n) := by
    rw [Finset.sum_eq_single 0]
    · simp [adjacent_unit_zero]
    · intro j _ hj
      simp [adjacent_unit_positive f j hj]
    · simp
  rw [h, final_unit]
  ring

theorem hochschild_on_epsilon {n : ℕ} (f : Cochains n) :
    hochschildEvaluation f (epsilonAll (n + 1)) = 0 := by
  simp [hochschildEvaluation, adjacent_epsilon, final_epsilon]

/- Actual cyclic rotations and the complete Connes expression (1-t)sN.
   On normalized cochains the t*s terms vanish because their second entry
   is the unit, a fact proved below rather than omitted as a definition. -/
def cyclicTuple {n : ℕ} (x : Fin (n + 1) → D) (i : Fin (n + 1)) :
    Fin (n + 1) → D := fun k => x (k - i)

def lastToFirst {m : ℕ} (x : Fin (m + 1) → D) : Fin (m + 1) → D :=
  Fin.cons (x (Fin.last m)) (fun i => x i.castSucc)

def connesEvaluation {n : ℕ} (f : Cochains (n + 1))
    (x : Fin (n + 1) → D) : ℤ :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ (n * i.val) *
    (f (Fin.cons 1 (cyclicTuple x i)) -
      (-1 : ℤ) ^ (n + 1) * f (lastToFirst (Fin.cons 1 (cyclicTuple x i))))

theorem connes_second_term_zero {n : ℕ} (f : NormalizedCochains (n + 1))
    (x : Fin (n + 1) → D) (i : Fin (n + 1)) :
    f.1 (lastToFirst (Fin.cons 1 (cyclicTuple x i))) = 0 := by
  apply f.2 (0 : Fin (n + 1)).succ (Fin.succ_ne_zero _)
  simp [lastToFirst]

theorem connes_on_unit {n : ℕ} (f : NormalizedCochains (n + 1)) :
    connesEvaluation f.1 (unitFirst n) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have h : f.1 (Fin.cons 1 (cyclicTuple (unitFirst n) i)) = 0 := by
    apply f.2 i.succ (Fin.succ_ne_zero _)
    simp [cyclicTuple, unitFirst]
  simp [h, connes_second_term_zero]

def connesCoefficient (n : ℕ) : ℤ :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ (n * i.val)

theorem connes_on_epsilon {n : ℕ} (f : NormalizedCochains (n + 1)) :
    connesEvaluation f.1 (epsilonAll n) =
      connesCoefficient n * f.1 (unitFirst (n + 1)) := by
  have h (i : Fin (n + 1)) : Fin.cons 1 (cyclicTuple (epsilonAll n) i) =
      unitFirst (n + 1) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [unitFirst]
    · simp [unitFirst, cyclicTuple, epsilonAll]
  calc
    connesEvaluation f.1 (epsilonAll n) =
        ∑ i : Fin (n + 1), (-1 : ℤ) ^ (n * i.val) * f.1 (unitFirst (n + 1)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [connes_second_term_zero f (epsilonAll n) i, h i]
      simp
    _ = _ := by rw [← Finset.sum_mul]; rfl

/- Native tensor-Hom and normalization: these are the actual tensor powers,
   the span of unit-degenerate tensors, and its quotient, in every degree. -/
abbrev HochschildChains (n : ℕ) :=
  PiTensorProduct ℤ (fun _ : Fin (n + 1) => D)

def tensorCochainEquiv (n : ℕ) :
    Cochains n ≃ₗ[ℤ] (HochschildChains n →ₗ[ℤ] ℤ) := PiTensorProduct.lift

def degenerateGenerators (n : ℕ) : Set (HochschildChains n) :=
  {t | ∃ (x : Fin (n + 1) → D) (i : Fin (n + 1)),
    i ≠ 0 ∧ x i = 1 ∧ t = PiTensorProduct.tprod ℤ x}

def degenerateSubmodule (n : ℕ) : Submodule ℤ (HochschildChains n) :=
  Submodule.span ℤ (degenerateGenerators n)

abbrev NormalizedChains (n : ℕ) := HochschildChains n ⧸ degenerateSubmodule n

theorem normalized_iff_annihilates_degenerates {n : ℕ} (f : Cochains n) :
    f ∈ normalizedSubmodule n ↔
      degenerateSubmodule n ≤ LinearMap.ker (tensorCochainEquiv n f) := by
  constructor
  · intro hf
    apply Submodule.span_le.mpr
    rintro t ⟨x, i, hi, hx, rfl⟩
    change PiTensorProduct.lift f (PiTensorProduct.tprod ℤ x) = 0
    simpa using hf i hi x hx
  · intro hf i hi x hx
    have ht : PiTensorProduct.tprod ℤ x ∈ degenerateSubmodule n :=
      Submodule.subset_span ⟨x, i, hi, hx, rfl⟩
    have h := hf ht
    change PiTensorProduct.lift f (PiTensorProduct.tprod ℤ x) = 0 at h
    simpa using h

def normalizedToQuotientHom (n : ℕ) :
    NormalizedCochains n →ₗ[ℤ] (NormalizedChains n →ₗ[ℤ] ℤ) where
  toFun f := (degenerateSubmodule n).liftQ (tensorCochainEquiv n f.1)
    ((normalized_iff_annihilates_degenerates f.1).mp f.2)
  map_add' f g := by
    apply Submodule.linearMap_qext
    ext x
    simp [tensorCochainEquiv, LinearMap.compMultilinearMap_apply]
  map_smul' a f := by
    apply Submodule.linearMap_qext
    ext x
    simp [tensorCochainEquiv, LinearMap.compMultilinearMap_apply]

def quotientHomToNormalized (n : ℕ)
    (f : NormalizedChains n →ₗ[ℤ] ℤ) : NormalizedCochains n :=
  ⟨(tensorCochainEquiv n).symm (f.comp (degenerateSubmodule n).mkQ), by
    apply (normalized_iff_annihilates_degenerates _).mpr
    rw [LinearEquiv.apply_symm_apply]
    intro x hx
    change f ((degenerateSubmodule n).mkQ x) = 0
    rw [show (degenerateSubmodule n).mkQ x = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr hx, map_zero]⟩

def normalizedTensorDualEquiv (n : ℕ) :
    NormalizedCochains n ≃ₗ[ℤ] (NormalizedChains n →ₗ[ℤ] ℤ) where
  toFun := normalizedToQuotientHom n
  invFun := quotientHomToNormalized n
  left_inv f := by
    apply Subtype.ext
    apply (tensorCochainEquiv n).injective
    simp [quotientHomToNormalized, normalizedToQuotientHom, Submodule.liftQ_mkQ]
  right_inv f := by
    apply Submodule.linearMap_qext
    ext x
    simp [normalizedToQuotientHom, quotientHomToNormalized]
  map_add' := (normalizedToQuotientHom n).map_add
  map_smul' := (normalizedToQuotientHom n).map_smul

def unitLine : Submodule ℤ D := Submodule.span ℤ ({1} : Set D)

theorem unitLine_eq_kernel : unitLine = LinearMap.ker epsilonPart := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    have hx' : x = 1 := Set.mem_singleton_iff.mp hx
    subst x
    rfl
  · intro x hx
    have hs : x.snd = 0 := hx
    have he : x = x.fst • (1 : D) := by
      apply TrivSqZeroExt.ext
      · simp
      · simpa using hs
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

abbrev Bar := D ⧸ unitLine

def barEquiv : Bar ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ unitLine_eq_kernel).trans
    (epsilonPart.quotKerEquivOfSurjective (fun z => ⟨⟨0, z⟩, rfl⟩))

@[simp] theorem barEquiv_mk (x : D) :
    barEquiv (Submodule.Quotient.mk x) = epsilonPart x := rfl

@[simp] theorem barEquiv_unit : barEquiv (Submodule.Quotient.mk (1 : D)) = 0 := rfl

@[simp] theorem barEquiv_epsilon :
    barEquiv (Submodule.Quotient.mk (DualNumber.eps : D)) = 1 := rfl

theorem normalized_reconstruction {n : ℕ} (f : NormalizedCochains n) :
    normalizedForm n (f.1 (unitFirst n)) (f.1 (epsilonAll n)) = f :=
  (normalizedCoordinates n).symm_apply_apply f

theorem normalized_apply {n : ℕ} (f : NormalizedCochains n)
    (x : Fin (n + 1) → D) :
    f.1 x = (f.1 (unitFirst n) * (x 0).fst + f.1 (epsilonAll n) * (x 0).snd) *
      ∏ i : Fin n, (x i.succ).snd := by
  conv_lhs => rw [← normalized_reconstruction f]
  simp [normalizedForm, cochainForm, firstFunctional, constantPart, epsilonPart,
    Fin.prod_univ_succ]

def barRepresentative (n : ℕ) (z : D) : Fin (n + 1) → D :=
  Fin.cons z (fun _ => DualNumber.eps)

theorem normalized_on_bar {n : ℕ} (f : NormalizedCochains n) (z : D) :
    f.1 (barRepresentative n z) =
      f.1 (unitFirst n) * z.fst + f.1 (epsilonAll n) * z.snd := by
  rw [normalized_apply]
  simp [barRepresentative]

theorem adjacent_bar_zero (n : ℕ) (z : D) :
    adjacentTuple (barRepresentative (n + 1) z) 0 =
      barRepresentative n (z * DualNumber.eps) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [adjacentTuple, barRepresentative]
  · simp [adjacentTuple, barRepresentative]

theorem adjacent_bar_positive {n : ℕ} (f : Cochains n) (z : D) (j : Fin (n + 1))
    (hj : j ≠ 0) : f (adjacentTuple (barRepresentative (n + 1) z) j) = 0 := by
  apply f.map_coord_zero j
  have h := Fin.eq_succ_of_ne_zero hj
  obtain ⟨k, rfl⟩ := h
  simp [adjacentTuple, barRepresentative, ← pow_two, DualNumber.eps_pow_two]

theorem final_bar (n : ℕ) (z : D) :
    finalTuple (barRepresentative (n + 1) z) =
      barRepresentative n (DualNumber.eps * z) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [finalTuple, barRepresentative]
  · simp [finalTuple, barRepresentative]

theorem hochschild_on_bar {n : ℕ} (f : NormalizedCochains n) (z : D) :
    hochschildEvaluation f.1 (barRepresentative (n + 1) z) =
      (1 + (-1 : ℤ) ^ (n + 1)) * f.1 (epsilonAll n) * z.fst := by
  rw [hochschildEvaluation]
  have h : (∑ j : Fin (n + 1), (-1 : ℤ) ^ j.val *
      f.1 (adjacentTuple (barRepresentative (n + 1) z) j)) =
        f.1 (barRepresentative n (z * DualNumber.eps)) := by
    rw [Finset.sum_eq_single 0]
    · simp [adjacent_bar_zero]
    · intro j _ hj
      simp [adjacent_bar_positive f.1 z j hj]
    · simp
  rw [h, final_bar, normalized_on_bar, normalized_on_bar]
  simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, DualNumber.fst_eps,
    DualNumber.snd_eps, op_smul_eq_smul, smul_eq_mul, mul_zero, mul_one, zero_mul,
    zero_add]
  ring

def cyclicIndexEquiv (n : ℕ) (i : Fin (n + 1)) : Fin (n + 1) ≃ Fin (n + 1) where
  toFun k := k - i
  invFun k := k + i
  left_inv k := sub_add_cancel k i
  right_inv k := add_sub_cancel_right k i

theorem cyclic_product {n : ℕ} (x : Fin (n + 1) → D) (i : Fin (n + 1)) :
    (∏ k : Fin (n + 1), (cyclicTuple x i k).snd) =
      ∏ k : Fin (n + 1), (x k).snd :=
  (cyclicIndexEquiv n i).prod_comp (fun k => (x k).snd)

theorem connes_formula {n : ℕ} (f : NormalizedCochains (n + 1))
    (x : Fin (n + 1) → D) :
    connesEvaluation f.1 x = connesCoefficient n *
      (f.1 (unitFirst (n + 1)) * ∏ k : Fin (n + 1), (x k).snd) := by
  have h (i : Fin (n + 1)) : f.1 (Fin.cons 1 (cyclicTuple x i)) =
      f.1 (unitFirst (n + 1)) * ∏ k : Fin (n + 1), (x k).snd := by
    rw [normalized_apply]
    simp only [Fin.cons_zero, TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one,
      mul_one, mul_zero, add_zero, Fin.cons_succ]
    rw [cyclic_product]
  calc
    _ = ∑ i : Fin (n + 1), (-1 : ℤ) ^ (n * i.val) *
        (f.1 (unitFirst (n + 1)) * ∏ k : Fin (n + 1), (x k).snd) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [connes_second_term_zero f x i, h i]
      simp
    _ = _ := by rw [← Finset.sum_mul]; rfl

def hochschildCoefficient (n : ℕ) : ℤ := 1 + (-1 : ℤ) ^ (n + 1)

def hochschildCoboundary (n : ℕ) :
    NormalizedCochains n →ₗ[ℤ] NormalizedCochains (n + 1) where
  toFun f := normalizedForm (n + 1)
    (hochschildCoefficient n * f.1 (epsilonAll n)) 0
  map_add' f g := by
    apply (normalizedCoordinates (n + 1)).injective
    ext <;> simp [normalizedCoordinates, normalizedForm, mul_add]
  map_smul' a f := by
    apply (normalizedCoordinates (n + 1)).injective
    ext <;> simp [normalizedCoordinates, normalizedForm, mul_left_comm]

theorem hochschild_coordinates {n : ℕ} (f : NormalizedCochains n) :
    normalizedCoordinates (n + 1) (hochschildCoboundary n f) =
      (hochschildCoefficient n * f.1 (epsilonAll n), 0) := by
  simp [hochschildCoboundary, normalizedCoordinates, normalizedForm]

theorem hochschild_bar_formula {n : ℕ} (f : NormalizedCochains n) (z : D) :
    (hochschildCoboundary n f).1 (barRepresentative (n + 1) z) =
      hochschildEvaluation f.1 (barRepresentative (n + 1) z) := by
  rw [normalized_on_bar, hochschild_on_bar]
  have h := hochschild_coordinates f
  have ha := congrArg Prod.fst h
  have hb := congrArg Prod.snd h
  change (hochschildCoboundary n f).1 (unitFirst (n + 1)) = _ at ha
  change (hochschildCoboundary n f).1 (epsilonAll (n + 1)) = 0 at hb
  rw [ha, hb]
  simp [hochschildCoefficient]

def connesCoboundary (n : ℕ) :
    NormalizedCochains (n + 1) →ₗ[ℤ] NormalizedCochains n where
  toFun f := normalizedForm n
    0 (connesCoefficient n * f.1 (unitFirst (n + 1)))
  map_add' f g := by
    apply (normalizedCoordinates n).injective
    ext <;> simp [normalizedCoordinates, normalizedForm, mul_add]
  map_smul' a f := by
    apply (normalizedCoordinates n).injective
    ext <;> simp [normalizedCoordinates, normalizedForm, mul_left_comm]

theorem connes_coordinates {n : ℕ} (f : NormalizedCochains (n + 1)) :
    normalizedCoordinates n (connesCoboundary n f) =
      (0, connesCoefficient n * f.1 (unitFirst (n + 1))) := by
  simp [connesCoboundary, normalizedCoordinates, normalizedForm]

theorem connes_full_formula {n : ℕ} (f : NormalizedCochains (n + 1))
    (x : Fin (n + 1) → D) :
    (connesCoboundary n f).1 x = connesEvaluation f.1 x := by
  rw [normalized_apply, connes_formula]
  have h := connes_coordinates f
  have ha := congrArg Prod.fst h
  have hb := congrArg Prod.snd h
  change (connesCoboundary n f).1 (unitFirst n) = 0 at ha
  change (connesCoboundary n f).1 (epsilonAll n) = _ at hb
  rw [ha, hb]
  rw [Fin.prod_univ_succ (fun i : Fin (n + 1) => (x i).snd)]
  simp only [zero_mul, zero_add]
  ring

theorem hochschild_coefficient_even (k : ℕ) : hochschildCoefficient (2 * k) = 0 := by
  simp [hochschildCoefficient, pow_add, pow_mul]

theorem hochschild_coefficient_odd (k : ℕ) : hochschildCoefficient (2 * k + 1) = 2 := by
  simp [hochschildCoefficient, pow_add, pow_mul]

theorem connes_coefficient_even (k : ℕ) : connesCoefficient (2 * k) = 2 * k + 1 := by
  simp [connesCoefficient, mul_assoc, pow_mul]

theorem alternating_sum_even (k : ℕ) :
    (∑ i : Fin (2 * k), (-1 : ℤ) ^ i.val) = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
      Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    simp [pow_add, pow_mul]

theorem connes_coefficient_odd (k : ℕ) : connesCoefficient (2 * k + 1) = 0 := by
  unfold connesCoefficient
  have h (i : Fin (2 * k + 1 + 1)) :
      (-1 : ℤ) ^ ((2 * k + 1) * i.val) = (-1 : ℤ) ^ i.val := by
    rw [pow_mul]
    simp [pow_add, pow_mul]
  simp_rw [h]
  convert alternating_sum_even (k + 1) using 1
  congr 1

/- Bundle the genuine full Hochschild faces as multilinear maps using the
   canonical equivalence between the inputs and the disjoint union of the
   fibers of a slot map.  Each fiber product is actual multiplication in D. -/
def mergeIndex {n : ℕ} (j : Fin (n + 1)) (k : Fin (n + 2)) : Fin (n + 1) :=
  ⟨if k.val ≤ j.val then k.val else k.val - 1, by
    split_ifs with h <;> have hj := j.isLt <;> have hk := k.isLt <;> omega⟩

def endIndex {n : ℕ} (k : Fin (n + 2)) : Fin (n + 1) :=
  if h : k.val = n + 1 then 0 else ⟨k.val, by have hk := k.isLt; omega⟩

def fiberContraction {n m : ℕ} (q : Fin (m + 1) → Fin (n + 1))
    (f : Cochains n) : Cochains m :=
  (f.compMultilinearMap (fun j =>
    MultilinearMap.mkPiAlgebra ℤ {k : Fin (m + 1) // q k = j} D)).domDomCongr
      (Equiv.sigmaFiberEquiv q)

theorem fiberContraction_apply {n m : ℕ} (q : Fin (m + 1) → Fin (n + 1))
    (f : Cochains n) (x : Fin (m + 1) → D) :
    fiberContraction q f x = f (fun j => ∏ k : {k // q k = j}, x k.val) := rfl

theorem merge_fiber {n : ℕ} (j u : Fin (n + 1)) :
    Finset.univ.filter (fun k : Fin (n + 2) => mergeIndex j k = u) =
      if u < j then {u.castSucc}
      else if u = j then {j.castSucc, j.succ} else {u.succ} := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with h₁ h₂
  · simp only [Finset.mem_singleton, Fin.ext_iff, mergeIndex,
      Fin.val_castSucc]
    have hj := j.isLt
    have hu := u.isLt
    have hk := k.isLt
    change u.val < j.val at h₁
    split_ifs <;> omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, mergeIndex,
      Fin.val_castSucc, Fin.val_succ]
    have hj := j.isLt
    have hk := k.isLt
    subst u
    split_ifs <;> omega
  · simp only [Finset.mem_singleton, Fin.ext_iff, mergeIndex, Fin.val_succ]
    have hj := j.isLt
    have hu := u.isLt
    have hk := k.isLt
    have hne : u.val ≠ j.val := fun h => h₂ (Fin.ext h)
    change ¬u.val < j.val at h₁
    split_ifs <;> omega

theorem end_fiber {n : ℕ} (u : Fin (n + 1)) :
    Finset.univ.filter (fun k : Fin (n + 2) => endIndex k = u) =
      if u = 0 then {0, Fin.last (n + 1)} else {u.castSucc} := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with hu
  · subst u
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, endIndex,
      Fin.val_zero, Fin.val_last]
    split_ifs <;> simp_all
  · simp only [Finset.mem_singleton]
    by_cases hlast : k.val = n + 1
    · rw [endIndex, dif_pos hlast]
      have hnu : (0 : Fin (n + 1)) ≠ u := Ne.symm hu
      have hnk : k ≠ u.castSucc := by
        intro h
        have hval := congrArg Fin.val h
        have hub := u.isLt
        simp only [Fin.val_castSucc] at hval
        omega
      simp [hnu, hnk]
    · rw [endIndex, dif_neg hlast]
      simp only [Fin.ext_iff, Fin.val_castSucc]

theorem fiber_product_filter {n m : ℕ} (q : Fin (m + 1) → Fin (n + 1))
    (x : Fin (m + 1) → D) (j : Fin (n + 1)) :
    (∏ k : {k // q k = j}, x k.val) =
      ∏ k ∈ Finset.univ.filter (fun k => q k = j), x k := by
  exact (Finset.prod_subtype _ (by intro k; simp) x).symm

theorem adjacent_contraction {n : ℕ} (f : Cochains n) (x : Fin (n + 2) → D)
    (j : Fin (n + 1)) : fiberContraction (mergeIndex j) f x = f (adjacentTuple x j) := by
  rw [fiberContraction_apply]
  congr 1
  funext u
  rw [fiber_product_filter, merge_fiber]
  unfold adjacentTuple
  split_ifs with h₁ h₂
  · simp
  · subst u
    have hne : j.castSucc ≠ j.succ := by
      intro h
      have := congrArg Fin.val h
      simp at this
    simp [hne]
  · simp

theorem final_contraction {n : ℕ} (f : Cochains n) (x : Fin (n + 2) → D) :
    fiberContraction endIndex f x = f (finalTuple x) := by
  rw [fiberContraction_apply]
  congr 1
  funext u
  rw [fiber_product_filter, end_fiber]
  refine Fin.cases ?_ (fun k => ?_) u
  · have hn : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := by
      intro h
      have := congrArg Fin.val h
      simp at this
    simp [finalTuple, hn, mul_comm]
  · simp [finalTuple]

def hochschildMultilinear {n : ℕ} (f : Cochains n) : Cochains (n + 1) :=
  (∑ j : Fin (n + 1), ((-1 : ℤ) ^ j.val) • fiberContraction (mergeIndex j) f) +
    ((-1 : ℤ) ^ (n + 1)) • fiberContraction endIndex f

theorem hochschildMultilinear_apply {n : ℕ} (f : Cochains n) (x : Fin (n + 2) → D) :
    hochschildMultilinear f x = hochschildEvaluation f x := by
  simp [hochschildMultilinear, hochschildEvaluation, adjacent_contraction, final_contraction]

theorem adjacent_unit_degenerate {n : ℕ} (f : NormalizedCochains n)
    (x : Fin (n + 2) → D) (i : Fin (n + 2)) (hi : i ≠ 0) (hx : x i = 1)
    (j : Fin (n + 1)) (hleft : j.val + 1 ≠ i.val) (hright : j.val ≠ i.val) :
    f.1 (adjacentTuple x j) = 0 := by
  have hiz : i.val ≠ 0 := fun h => hi (Fin.ext h)
  have hib := i.isLt
  have hjb := j.isLt
  by_cases hlt : i.val < j.val
  · let u : Fin (n + 1) := ⟨i.val, by omega⟩
    have hun : u ≠ 0 := fun h => hiz (congrArg Fin.val h)
    apply f.2 u hun
    have huj : u < j := hlt
    have hui : u.castSucc = i := Fin.ext rfl
    simp [adjacentTuple, huj, hui, hx]
  · have hgt : j.val + 1 < i.val := by omega
    let u : Fin (n + 1) := ⟨i.val - 1, by omega⟩
    have hun : u ≠ 0 := by intro h; have := congrArg Fin.val h; dsimp [u] at this; omega
    apply f.2 u hun
    have huj : ¬u < j := by change ¬i.val - 1 < j.val; omega
    have hune : u ≠ j := by intro h; have := congrArg Fin.val h; dsimp [u] at this; omega
    have hui : u.succ = i := by apply Fin.ext; dsimp [u]; omega
    simp [adjacentTuple, huj, hune, hui, hx]

theorem final_unit_degenerate {n : ℕ} (f : NormalizedCochains n)
    (x : Fin (n + 2) → D) (i : Fin (n + 2)) (hi : i ≠ 0) (hx : x i = 1)
    (hil : i ≠ Fin.last (n + 1)) : f.1 (finalTuple x) = 0 := by
  have hiz : i.val ≠ 0 := fun h => hi (Fin.ext h)
  have hib := i.isLt
  have hil' : i.val ≠ n + 1 := fun h => hil (Fin.ext h)
  let u : Fin (n + 1) := ⟨i.val, by omega⟩
  have hun : u ≠ 0 := fun h => hiz (congrArg Fin.val h)
  apply f.2 u hun
  obtain ⟨k, hk⟩ := Fin.eq_succ_of_ne_zero hun
  have hki : k.succ.castSucc = i := by rw [← hk]; exact Fin.ext rfl
  rw [hk]
  change x k.succ.castSucc = 1
  rw [hki, hx]

theorem adjacent_unit_pair {n : ℕ} (x : Fin (n + 2) → D) (j : Fin n)
    (hx : x j.succ.castSucc = 1) :
    adjacentTuple x j.castSucc = adjacentTuple x j.succ := by
  funext k
  have hcast : j.castSucc.succ = j.succ.castSucc := rfl
  have hx' : x j.castSucc.succ = 1 := by rw [hcast]; exact hx
  by_cases hlt : k < j.castSucc
  · have hlt' : k < j.succ := by change k.val < j.val + 1; exact Nat.lt_succ_of_lt hlt
    simp [adjacentTuple, hlt, hlt']
  · by_cases he : k = j.castSucc
    · subst k
      have hlt' : j.castSucc < j.succ := by change j.val < j.val + 1; omega
      simp [adjacentTuple, hlt', hx']
    · by_cases he' : k = j.succ
      · subst k
        have hn : ¬j.succ < j.castSucc := by change ¬j.val + 1 < j.val; omega
        have hne : j.succ ≠ j.castSucc := by intro h; have := congrArg Fin.val h; simp at this
        simp [adjacentTuple, hn, hne, hx']
      · have hlt' : ¬k < j.succ := by
          change ¬k.val < j.val + 1
          have hne : k.val ≠ j.val := fun h => he (Fin.ext h)
          change ¬k.val < j.val at hlt
          omega
        simp [adjacentTuple, hlt, he, hlt', he']

theorem adjacent_final_unit {n : ℕ} (x : Fin (n + 2) → D)
    (hx : x (Fin.last (n + 1)) = 1) :
    adjacentTuple x (Fin.last n) = finalTuple x := by
  have ha : adjacentTuple x (Fin.last n) = fun k => x k.castSucc := by
    funext k
    by_cases hk : k = Fin.last n
    · subst k
      simp [adjacentTuple, hx]
    · have hlt : k < Fin.last n := by
        have hkb := k.isLt
        have hne : k.val ≠ n := fun h => hk (Fin.ext h)
        change k.val < n
        omega
      simp [adjacentTuple, hlt]
  rw [ha]
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [finalTuple, hx]
  · rfl

theorem hochschild_preserves_normalized {n : ℕ} (f : NormalizedCochains n) :
    hochschildMultilinear f.1 ∈ normalizedSubmodule (n + 1) := by
  intro i hi x hx
  rw [hochschildMultilinear_apply, hochschildEvaluation]
  by_cases hil : i = Fin.last (n + 1)
  · subst i
    have hs : (∑ j : Fin (n + 1), (-1 : ℤ) ^ j.val * f.1 (adjacentTuple x j)) =
        (-1 : ℤ) ^ n * f.1 (adjacentTuple x (Fin.last n)) := by
      rw [Finset.sum_eq_single (Fin.last n)]
      · rfl
      · intro j _ hj
        have hleft : j.val + 1 ≠ n + 1 := by
          intro h
          apply hj
          apply Fin.ext
          change j.val = n
          omega
        have hright : j.val ≠ n + 1 := by have := j.isLt; omega
        rw [adjacent_unit_degenerate f x _ hi hx j hleft hright, mul_zero]
      · simp
    rw [hs, adjacent_final_unit x hx, pow_succ]
    ring
  · have hib := i.isLt
    have hin : i.val ≠ n + 1 := fun h => hil (Fin.ext h)
    let r : Fin (n + 1) := ⟨i.val, by omega⟩
    have hrn : r ≠ 0 := by
      intro h
      apply hi
      apply Fin.ext
      have hv := congrArg (fun z : Fin (n + 1) => z.val) h
      exact hv
    obtain ⟨j, hj⟩ := Fin.eq_succ_of_ne_zero hrn
    have hij : j.succ.castSucc = i := by rw [← hj]; exact Fin.ext rfl
    have hxj : x j.succ.castSucc = 1 := by rw [hij, hx]
    have hne : j.castSucc ≠ j.succ := by
      intro h
      have := congrArg Fin.val h
      simp at this
    have hs : (∑ k : Fin (n + 1), (-1 : ℤ) ^ k.val * f.1 (adjacentTuple x k)) =
        (-1 : ℤ) ^ j.val * f.1 (adjacentTuple x j.castSucc) +
        (-1 : ℤ) ^ (j.val + 1) * f.1 (adjacentTuple x j.succ) := by
      apply Finset.sum_eq_add_of_mem j.castSucc j.succ (Finset.mem_univ _) (Finset.mem_univ _) hne
      intro k _ hks
      have hv : i.val = j.val + 1 := by simpa only [Fin.val_castSucc, Fin.val_succ] using congrArg Fin.val hij.symm
      have hleft : k.val + 1 ≠ i.val := by
        intro h
        apply hks.1
        apply Fin.ext
        simp only [Fin.val_castSucc]
        omega
      have hright : k.val ≠ i.val := by
        intro h
        apply hks.2
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      rw [adjacent_unit_degenerate f x i hi hx k hleft hright, mul_zero]
    rw [hs, final_unit_degenerate f x i hi hx hil, mul_zero, add_zero,
      adjacent_unit_pair x j hxj, pow_succ]
    ring

def rawNormalizedHochschild {n : ℕ} (f : NormalizedCochains n) :
    NormalizedCochains (n + 1) :=
  ⟨hochschildMultilinear f.1, hochschild_preserves_normalized f⟩

theorem rawNormalizedHochschild_eq {n : ℕ} (f : NormalizedCochains n) :
    rawNormalizedHochschild f = hochschildCoboundary n f := by
  apply normalized_ext
  · simp [rawNormalizedHochschild, hochschildCoboundary, normalizedForm,
      hochschildMultilinear_apply, hochschild_on_unit, hochschildCoefficient]
  · simp [rawNormalizedHochschild, hochschildCoboundary, normalizedForm,
      hochschildMultilinear_apply, hochschild_on_epsilon]

theorem hochschild_full_formula {n : ℕ} (f : NormalizedCochains n)
    (x : Fin (n + 2) → D) :
    (hochschildCoboundary n f).1 x = hochschildEvaluation f.1 x := by
  rw [← rawNormalizedHochschild_eq]
  exact hochschildMultilinear_apply f.1 x

/- Full first-quadrant totalization.  Each diagonal contains all normalized
   cochain spaces of degrees n,n-2,... .  Coordinates are transported along
   the proved full normalized-space equivalences.  Each summand in d is a
   genuine b* or B* component, not a prescribed cohomology group. -/
abbrev TotalCochains (n : ℕ) :=
  (p : Fin (n / 2 + 1)) → NormalizedCochains (n - 2 * p.val)

abbrev TotalCoordinates (n : ℕ) := Fin (n / 2 + 1) → ℤ × ℤ

def totalCoordinates (n : ℕ) : TotalCochains n ≃ₗ[ℤ] TotalCoordinates n where
  toFun f p := normalizedCoordinates (n - 2 * p.val) (f p)
  invFun f p := (normalizedCoordinates (n - 2 * p.val)).symm (f p)
  left_inv f := by funext p; exact (normalizedCoordinates _).symm_apply_apply (f p)
  right_inv f := by funext p; exact (normalizedCoordinates _).apply_symm_apply (f p)
  map_add' f g := by funext p; exact (normalizedCoordinates _).map_add (f p) (g p)
  map_smul' a f := by funext p; exact (normalizedCoordinates _).map_smul a (f p)

def bCoordinates (n : ℕ) : (ℤ × ℤ) →ₗ[ℤ] ℤ × ℤ :=
  (normalizedCoordinates (n + 1)).toLinearMap.comp
    ((hochschildCoboundary n).comp (normalizedCoordinates n).symm.toLinearMap)

def BCoordinates (n : ℕ) : (ℤ × ℤ) →ₗ[ℤ] ℤ × ℤ :=
  (normalizedCoordinates n).toLinearMap.comp
    ((connesCoboundary n).comp (normalizedCoordinates (n + 1)).symm.toLinearMap)

theorem bCoordinates_apply (n : ℕ) (ab : ℤ × ℤ) :
    bCoordinates n ab = (hochschildCoefficient n * ab.2, 0) := by
  simp [bCoordinates, hochschildCoboundary, normalizedCoordinates, normalizedForm]

theorem BCoordinates_apply (n : ℕ) (ab : ℤ × ℤ) :
    BCoordinates n ab = (0, connesCoefficient n * ab.1) := by
  simp [BCoordinates, connesCoboundary, normalizedCoordinates, normalizedForm]

def coordinateDifferential (n : ℕ) : TotalCoordinates n →ₗ[ℤ] TotalCoordinates (n + 1) where
  toFun f i :=
    (∑ j : Fin (n / 2 + 1),
      if i.val = j.val then bCoordinates (n - 2 * j.val) (f j) else 0) +
    (∑ j : Fin (n / 2 + 1),
      if i.val = j.val + 1 ∧ 0 < n - 2 * j.val then
        BCoordinates (n - 2 * j.val - 1) (f j) else 0)
  map_add' f g := by
    funext i
    simp only [Pi.add_apply, map_add]
    have h (P : Prop) [Decidable P] (a b : ℤ × ℤ) :
        (if P then a + b else 0) = (if P then a else 0) + (if P then b else 0) := by
      split_ifs <;> simp
    simp_rw [h, Finset.sum_add_distrib]
    ac_rfl
  map_smul' a f := by
    funext i
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_ite, smul_zero,
      Finset.smul_sum, smul_add]

theorem coordinateDifferential_even_apply (k : ℕ) (f : TotalCoordinates (2 * k))
    (i : Fin ((2 * k + 1) / 2 + 1)) : coordinateDifferential (2 * k) f i = 0 := by
  dsimp only [coordinateDifferential, LinearMap.coe_mk, AddHom.coe_mk]
  have hjb (j : Fin (2 * k / 2 + 1)) : j.val ≤ k := by have := j.isLt; omega
  have hb : (∑ j : Fin (2 * k / 2 + 1),
      if i.val = j.val then bCoordinates (2 * k - 2 * j.val) (f j) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    split_ifs
    · have he : 2 * k - 2 * j.val = 2 * (k - j.val) := by have := hjb j; omega
      rw [he, bCoordinates_apply, hochschild_coefficient_even]
      simp
    · rfl
  have hB : (∑ j : Fin (2 * k / 2 + 1),
      if i.val = j.val + 1 ∧ 0 < 2 * k - 2 * j.val then
        BCoordinates (2 * k - 2 * j.val - 1) (f j) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    split_ifs with h
    · have he : 2 * k - 2 * j.val - 1 = 2 * (k - j.val - 1) + 1 := by omega
      rw [he, BCoordinates_apply, connes_coefficient_odd]
      simp
    · rfl
  rw [hb, hB, add_zero]

theorem coordinateDifferential_even (k : ℕ) : coordinateDifferential (2 * k) = 0 := by
  apply LinearMap.ext
  intro f
  funext i
  exact coordinateDifferential_even_apply k f i

theorem coordinateDifferential_square (n : ℕ) (f : TotalCoordinates n) :
    coordinateDifferential (n + 1) (coordinateDifferential n f) = 0 := by
  by_cases hn : n % 2 = 0
  · have he : n = 2 * (n / 2) := by omega
    have hd : coordinateDifferential n = 0 := by rw [he, coordinateDifferential_even]
    rw [hd, LinearMap.zero_apply, map_zero]
  · have he : n + 1 = 2 * ((n + 1) / 2) := by omega
    have hd : coordinateDifferential (n + 1) = 0 := by rw [he, coordinateDifferential_even]
    rw [hd, LinearMap.zero_apply]

def totalDifferential (n : ℕ) : TotalCochains n →ₗ[ℤ] TotalCochains (n + 1) :=
  (totalCoordinates (n + 1)).symm.toLinearMap.comp
    ((coordinateDifferential n).comp (totalCoordinates n).toLinearMap)

theorem totalDifferential_square (n : ℕ) :
    (totalDifferential (n + 1)).comp (totalDifferential n) = 0 := by
  apply LinearMap.ext
  intro f
  apply (totalCoordinates (n + 2)).injective
  simp [totalDifferential, coordinateDifferential_square]

open CategoryTheory

def cyclicCochainComplex : CochainComplex (ModuleCat ℤ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℤ (TotalCochains n))
    (fun n => ModuleCat.ofHom (totalDifferential n))
    (fun n => ModuleCat.hom_ext (totalDifferential_square n))

abbrev HC (n : ℕ) := (cyclicCochainComplex.homology n)

def coordinateCochainComplex : CochainComplex (ModuleCat ℤ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℤ (TotalCoordinates n))
    (fun n => ModuleCat.ofHom (coordinateDifferential n)) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact coordinateDifferential_square n f)

def totalComplexIso : cyclicCochainComplex ≅ coordinateCochainComplex :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (totalCoordinates n).toModuleIso) (by
    intro i j hij
    have hj : i + 1 = j := hij
    subst j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    simp [cyclicCochainComplex, coordinateCochainComplex, CochainComplex.of.d,
      totalDifferential])

def homologyCoordinateEquiv (n : ℕ) :
    HC n ≃ₗ[ℤ] coordinateCochainComplex.homology n :=
  (HomologicalComplex.homologyMapIso totalComplexIso n).toLinearEquiv

theorem coordinate_complex_d (n : ℕ) :
    coordinateCochainComplex.d n (n + 1) = ModuleCat.ofHom (coordinateDifferential n) := by
  simp [coordinateCochainComplex, CochainComplex.of.d]

abbrev zeroShortComplex := coordinateCochainComplex.sc' 0 0 1
abbrev twoShortComplex := coordinateCochainComplex.sc' 1 2 3

theorem zeroShort_f : zeroShortComplex.f = 0 :=
  coordinateCochainComplex.shape 0 0 (by decide)

theorem zeroShort_g : zeroShortComplex.g = 0 := by
  change coordinateCochainComplex.d 0 1 = 0
  rw [coordinate_complex_d, show coordinateDifferential 0 = 0 from coordinateDifferential_even 0]
  rfl

theorem twoShort_g : twoShortComplex.g = 0 := by
  change coordinateCochainComplex.d 2 3 = 0
  rw [coordinate_complex_d, show coordinateDifferential 2 = 0 from coordinateDifferential_even 1]
  rfl

theorem up_prev_zero : (ComplexShape.up ℕ).prev 0 = 0 :=
  (ComplexShape.up ℕ).prev_eq_self' 0 (by intro k hk; change k + 1 = 0 at hk; omega)

def zeroNativeEquiv : coordinateCochainComplex.homology 0 ≃ₗ[ℤ] TotalCoordinates 0 :=
  ((coordinateCochainComplex.homologyIsoSc' 0 0 1 up_prev_zero
      ((ComplexShape.up ℕ).next_eq' (by rfl))) ≪≫
    (zeroShortComplex.asIsoHomologyι zeroShort_g) ≪≫
    zeroShortComplex.moduleCatOpcyclesIso ≪≫
    ((LinearMap.range zeroShortComplex.f.hom).quotEquivOfEqBot
      (by rw [zeroShort_f]; simp)).toModuleIso).toLinearEquiv

abbrev H2Quotient := TotalCoordinates 2 ⧸ LinearMap.range (coordinateDifferential 1)

def twoNativeEquiv : coordinateCochainComplex.homology 2 ≃ₗ[ℤ] H2Quotient :=
  ((coordinateCochainComplex.homologyIsoSc' 1 2 3
      ((ComplexShape.up ℕ).prev_eq' (by rfl)) ((ComplexShape.up ℕ).next_eq' (by rfl))) ≪≫
    (twoShortComplex.asIsoHomologyι twoShort_g) ≪≫
    twoShortComplex.moduleCatOpcyclesIso).toLinearEquiv

def HC0Equiv : HC 0 ≃ₗ[ℤ] TotalCoordinates 0 :=
  (homologyCoordinateEquiv 0).trans zeroNativeEquiv

def HC2Equiv : HC 2 ≃ₗ[ℤ] H2Quotient :=
  (homologyCoordinateEquiv 2).trans twoNativeEquiv

theorem HC0_no_two_torsion (x : HC 0) (hx : (2 : ℤ) • x = 0) : x = 0 := by
  apply HC0Equiv.injective
  have h : (2 : ℤ) • HC0Equiv x = 0 := by simpa using congrArg HC0Equiv hx
  simpa using (smul_eq_zero.mp h).resolve_left (by norm_num)

theorem differential_one_zero (f : TotalCoordinates 1) :
    coordinateDifferential 1 f 0 = (2 * (f 0).2, 0) := by
  simp [coordinateDifferential, bCoordinates_apply, BCoordinates_apply,
    hochschildCoefficient, connesCoefficient]

theorem differential_one_one (f : TotalCoordinates 1) :
    coordinateDifferential 1 f 1 = (0, (f 0).1) := by
  simp [coordinateDifferential, bCoordinates_apply, BCoordinates_apply,
    hochschildCoefficient, connesCoefficient]

def torsionRepresentative : TotalCoordinates 2 := fun p => if p = 0 then (1, 0) else 0

def torsionBoundaryPreimage : TotalCoordinates 1 := fun _ => (0, 1)

theorem twice_representative_is_boundary :
    coordinateDifferential 1 torsionBoundaryPreimage = (2 : ℤ) • torsionRepresentative := by
  funext p
  fin_cases p
  · simp [differential_one_zero, torsionBoundaryPreimage, torsionRepresentative]
  · simp [differential_one_one, torsionBoundaryPreimage, torsionRepresentative]

theorem representative_not_boundary :
    torsionRepresentative ∉ LinearMap.range (coordinateDifferential 1) := by
  rintro ⟨f, hf⟩
  have ht := congrFun hf 0
  rw [differential_one_zero] at ht
  have h := congrArg Prod.fst ht
  change 2 * (f 0).2 = 1 at h
  omega

def torsionQuotientClass : H2Quotient :=
  (LinearMap.range (coordinateDifferential 1)).mkQ torsionRepresentative

theorem torsionQuotientClass_nonzero : torsionQuotientClass ≠ 0 := by
  intro h
  exact representative_not_boundary ((Submodule.Quotient.mk_eq_zero _).mp h)

theorem twice_torsionQuotientClass : (2 : ℤ) • torsionQuotientClass = 0 := by
  rw [torsionQuotientClass, ← map_smul]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨torsionBoundaryPreimage, twice_representative_is_boundary⟩

def torsionHC2 : HC 2 := HC2Equiv.symm torsionQuotientClass

theorem torsionHC2_nonzero : torsionHC2 ≠ 0 := by
  intro h
  apply torsionQuotientClass_nonzero
  simpa [torsionHC2] using congrArg HC2Equiv h

theorem twice_torsionHC2 : (2 : ℤ) • torsionHC2 = 0 := by
  apply HC2Equiv.injective
  simpa [torsionHC2] using twice_torsionQuotientClass

theorem HC0_no_add_two_torsion (x : HC 0) (hx : x + x = 0) : x = 0 := by
  apply HC0Equiv.injective
  have h : HC0Equiv x + HC0Equiv x = 0 := by simpa using congrArg HC0Equiv hx
  have hz : HC0Equiv x = 0 := by
    funext i
    apply Prod.ext
    · have hi := congrArg (fun v : TotalCoordinates 0 => (v i).1) h
      change (HC0Equiv x i).1 + (HC0Equiv x i).1 = 0 at hi
      change (HC0Equiv x i).1 = 0
      omega
    · have hi := congrArg (fun v : TotalCoordinates 0 => (v i).2) h
      change (HC0Equiv x i).2 + (HC0Equiv x i).2 = 0 at hi
      change (HC0Equiv x i).2 = 0
      omega
  simpa using hz

theorem add_twice_torsionQuotientClass : torsionQuotientClass + torsionQuotientClass = 0 := by
  rw [torsionQuotientClass, ← map_add]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨torsionBoundaryPreimage, ?_⟩
  funext p
  fin_cases p
  · simp [differential_one_zero, torsionBoundaryPreimage, torsionRepresentative]
  · simp [differential_one_one, torsionBoundaryPreimage, torsionRepresentative]

theorem add_twice_torsionHC2 : torsionHC2 + torsionHC2 = 0 := by
  apply HC2Equiv.injective
  simpa [torsionHC2] using add_twice_torsionQuotientClass

theorem no_degree_two_group_isomorphism : ¬Nonempty (HC 0 ≃+ HC 2) := by
  rintro ⟨e⟩
  have hpre : e.symm torsionHC2 + e.symm torsionHC2 = 0 := by
    rw [← map_add, add_twice_torsionHC2, map_zero]
  have hz := HC0_no_add_two_torsion (e.symm torsionHC2) hpre
  apply torsionHC2_nonzero
  simpa using congrArg e hz

theorem dual_number_counterexample :
    Nonempty (R ≃ₐ[ℤ] D) ∧
    (∀ x : HC 0, (2 : ℤ) • x = 0 → x = 0) ∧
    (∃ x : HC 2, x ≠ 0 ∧ (2 : ℤ) • x = 0) ∧
    ¬Nonempty (HC 0 ≃+ HC 2) :=
  ⟨⟨quotientDualEquiv⟩, HC0_no_two_torsion,
    ⟨torsionHC2, torsionHC2_nonzero, twice_torsionHC2⟩, no_degree_two_group_isomorphism⟩

/- The source algebra itself, not just a separately isomorphic algebra.
   Transport the full normalized multilinear spaces along the actual
   algebra equivalence and check both standard operators on every input. -/
abbrev SourceCochains (n : ℕ) := MultilinearMap ℤ (fun _ : Fin (n + 1) => R) ℤ

def sourceTensorCochainEquiv (n : ℕ) : SourceCochains n ≃ₗ[ℤ]
    ((PiTensorProduct ℤ (fun _ : Fin (n + 1) => R)) →ₗ[ℤ] ℤ) := PiTensorProduct.lift

def sourceNormalizedSubmodule (n : ℕ) : Submodule ℤ (SourceCochains n) where
  carrier := {f | ∀ i : Fin (n + 1), i ≠ 0 →
    ∀ x : Fin (n + 1) → R, x i = 1 → f x = 0}
  zero_mem' := by
    change ∀ (i : Fin (n + 1)), i ≠ 0 →
      ∀ x : Fin (n + 1) → R, x i = 1 → (0 : SourceCochains n) x = 0
    intros
    rfl
  add_mem' hf hg i hi x hx := by simp [hf i hi x hx, hg i hi x hx]
  smul_mem' a f hf i hi x hx := by simp [hf i hi x hx]

abbrev SourceNormalized (n : ℕ) := sourceNormalizedSubmodule n

def sourceNormalizedEquiv (n : ℕ) : SourceNormalized n ≃ₗ[ℤ] NormalizedCochains n where
  toFun f := ⟨f.1.compLinearMap (fun _ => quotientDualEquiv.symm.toLinearMap), by
    intro i hi x hx
    apply f.2 i hi (fun j => quotientDualEquiv.symm (x j))
    rw [hx, map_one]⟩
  invFun f := ⟨f.1.compLinearMap (fun _ => quotientDualEquiv.toLinearMap), by
    intro i hi x hx
    apply f.2 i hi (fun j => quotientDualEquiv (x j))
    rw [hx, map_one]⟩
  left_inv f := by
    apply Subtype.ext
    apply MultilinearMap.ext
    intro x
    change f.1 (fun j => quotientDualEquiv.symm (quotientDualEquiv (x j))) = f.1 x
    simp
  right_inv f := by
    apply Subtype.ext
    apply MultilinearMap.ext
    intro x
    change f.1 (fun j => quotientDualEquiv (quotientDualEquiv.symm (x j))) = f.1 x
    simp
  map_add' f g := by apply Subtype.ext; apply MultilinearMap.ext; intro x; rfl
  map_smul' a f := by apply Subtype.ext; apply MultilinearMap.ext; intro x; rfl

@[simp] theorem sourceNormalized_apply {n : ℕ} (f : SourceNormalized n)
    (x : Fin (n + 1) → D) :
    (sourceNormalizedEquiv n f).1 x = f.1 (fun k => quotientDualEquiv.symm (x k)) := rfl

def sourceAdjacentTuple {n : ℕ} (x : Fin (n + 2) → R) (j : Fin (n + 1)) :
    Fin (n + 1) → R := fun k =>
  if k < j then x k.castSucc
  else if k = j then x k.castSucc * x k.succ else x k.succ

def sourceFinalTuple {n : ℕ} (x : Fin (n + 2) → R) : Fin (n + 1) → R :=
  Fin.cons (x (Fin.last (n + 1)) * x 0) (fun i => x i.succ.castSucc)

def sourceHochschildEvaluation {n : ℕ} (f : SourceCochains n)
    (x : Fin (n + 2) → R) : ℤ :=
  (∑ j : Fin (n + 1), (-1 : ℤ) ^ j.val * f (sourceAdjacentTuple x j)) +
    (-1 : ℤ) ^ (n + 1) * f (sourceFinalTuple x)

def sourceHochschildCoboundary (n : ℕ) : SourceNormalized n →ₗ[ℤ] SourceNormalized (n + 1) :=
  (sourceNormalizedEquiv (n + 1)).symm.toLinearMap.comp
    ((hochschildCoboundary n).comp (sourceNormalizedEquiv n).toLinearMap)

theorem sourceHochschild_full_formula {n : ℕ} (f : SourceNormalized n)
    (x : Fin (n + 2) → R) :
    (sourceHochschildCoboundary n f).1 x = sourceHochschildEvaluation f.1 x := by
  change (hochschildCoboundary n (sourceNormalizedEquiv n f)).1
      (fun k => quotientDualEquiv (x k)) = _
  rw [hochschild_full_formula]
  have ha (j : Fin (n + 1)) :
      (fun k => quotientDualEquiv.symm (adjacentTuple (fun l => quotientDualEquiv (x l)) j k)) =
        sourceAdjacentTuple x j := by
    funext k
    unfold adjacentTuple sourceAdjacentTuple
    split_ifs <;> simp only [map_mul, AlgEquiv.symm_apply_apply]
  have he : (fun k => quotientDualEquiv.symm
      (finalTuple (fun l => quotientDualEquiv (x l)) k)) = sourceFinalTuple x := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [finalTuple, sourceFinalTuple]
    · simp [finalTuple, sourceFinalTuple]
  simp only [hochschildEvaluation, sourceHochschildEvaluation, sourceNormalized_apply, ha, he]

def sourceCyclicTuple {n : ℕ} (x : Fin (n + 1) → R) (i : Fin (n + 1)) :
    Fin (n + 1) → R := fun k => x (k - i)

def sourceLastToFirst {m : ℕ} (x : Fin (m + 1) → R) : Fin (m + 1) → R :=
  Fin.cons (x (Fin.last m)) (fun i => x i.castSucc)

def sourceConnesEvaluation {n : ℕ} (f : SourceCochains (n + 1))
    (x : Fin (n + 1) → R) : ℤ :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ (n * i.val) *
    (f (Fin.cons 1 (sourceCyclicTuple x i)) -
      (-1 : ℤ) ^ (n + 1) * f (sourceLastToFirst (Fin.cons 1 (sourceCyclicTuple x i))))

def sourceConnesCoboundary (n : ℕ) : SourceNormalized (n + 1) →ₗ[ℤ] SourceNormalized n :=
  (sourceNormalizedEquiv n).symm.toLinearMap.comp
    ((connesCoboundary n).comp (sourceNormalizedEquiv (n + 1)).toLinearMap)

theorem sourceConnes_full_formula {n : ℕ} (f : SourceNormalized (n + 1))
    (x : Fin (n + 1) → R) :
    (sourceConnesCoboundary n f).1 x = sourceConnesEvaluation f.1 x := by
  change (connesCoboundary n (sourceNormalizedEquiv (n + 1) f)).1
      (fun k => quotientDualEquiv (x k)) = _
  rw [connes_full_formula]
  have hs (i : Fin (n + 1)) : (fun k : Fin (n + 2) => quotientDualEquiv.symm
      ((Fin.cons (1 : D) (cyclicTuple (fun l => quotientDualEquiv (x l)) i) :
        Fin (n + 2) → D) k)) =
        Fin.cons 1 (sourceCyclicTuple x i) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp
    · simp [cyclicTuple, sourceCyclicTuple]
  have ht (i : Fin (n + 1)) : (fun k : Fin (n + 2) => quotientDualEquiv.symm
      (lastToFirst (Fin.cons (1 : D) (cyclicTuple (fun l => quotientDualEquiv (x l)) i)) k)) =
        sourceLastToFirst (Fin.cons 1 (sourceCyclicTuple x i)) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [lastToFirst, sourceLastToFirst, cyclicTuple, sourceCyclicTuple]
    · simp [lastToFirst, sourceLastToFirst, ← hs i]
  simp only [connesEvaluation, sourceConnesEvaluation, sourceNormalized_apply, hs, ht]

abbrev SourceTotalCochains (n : ℕ) :=
  (p : Fin (n / 2 + 1)) → SourceNormalized (n - 2 * p.val)

def sourceTotalEquiv (n : ℕ) : SourceTotalCochains n ≃ₗ[ℤ] TotalCochains n where
  toFun f p := sourceNormalizedEquiv (n - 2 * p.val) (f p)
  invFun f p := (sourceNormalizedEquiv (n - 2 * p.val)).symm (f p)
  left_inv f := by funext p; exact (sourceNormalizedEquiv _).symm_apply_apply (f p)
  right_inv f := by funext p; exact (sourceNormalizedEquiv _).apply_symm_apply (f p)
  map_add' f g := by funext p; exact (sourceNormalizedEquiv _).map_add (f p) (g p)
  map_smul' a f := by funext p; exact (sourceNormalizedEquiv _).map_smul a (f p)

def sourceTotalDifferential (n : ℕ) : SourceTotalCochains n →ₗ[ℤ] SourceTotalCochains (n + 1) :=
  (sourceTotalEquiv (n + 1)).symm.toLinearMap.comp
    ((totalDifferential n).comp (sourceTotalEquiv n).toLinearMap)

theorem sourceTotalDifferential_square (n : ℕ) :
    (sourceTotalDifferential (n + 1)).comp (sourceTotalDifferential n) = 0 := by
  apply LinearMap.ext
  intro f
  apply (sourceTotalEquiv (n + 2)).injective
  have h := LinearMap.congr_fun (totalDifferential_square n) (sourceTotalEquiv n f)
  simpa [sourceTotalDifferential] using h

def sourceCyclicCochainComplex : CochainComplex (ModuleCat ℤ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℤ (SourceTotalCochains n))
    (fun n => ModuleCat.ofHom (sourceTotalDifferential n))
    (fun n => ModuleCat.hom_ext (sourceTotalDifferential_square n))

def sourceComplexIso : sourceCyclicCochainComplex ≅ cyclicCochainComplex :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (sourceTotalEquiv n).toModuleIso) (by
    intro i j hij
    have hj : i + 1 = j := hij
    subst j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    simp [sourceCyclicCochainComplex, cyclicCochainComplex, CochainComplex.of.d,
      sourceTotalDifferential])

abbrev SourceHC (n : ℕ) := sourceCyclicCochainComplex.homology n

def sourceHomologyEquiv (n : ℕ) : SourceHC n ≃ₗ[ℤ] HC n :=
  (HomologicalComplex.homologyMapIso sourceComplexIso n).toLinearEquiv

theorem sourceHC0_no_two_torsion (x : SourceHC 0) (hx : x + x = 0) : x = 0 := by
  apply (sourceHomologyEquiv 0).injective
  have h : sourceHomologyEquiv 0 x + sourceHomologyEquiv 0 x = 0 := by
    simpa using congrArg (sourceHomologyEquiv 0) hx
  simpa using HC0_no_add_two_torsion _ h

def sourceTorsionHC2 : SourceHC 2 := (sourceHomologyEquiv 2).symm torsionHC2

theorem sourceTorsion_nonzero : sourceTorsionHC2 ≠ 0 := by
  intro h
  apply torsionHC2_nonzero
  simpa [sourceTorsionHC2] using congrArg (sourceHomologyEquiv 2) h

theorem sourceTorsion_order_two : sourceTorsionHC2 + sourceTorsionHC2 = 0 := by
  apply (sourceHomologyEquiv 2).injective
  simpa [sourceTorsionHC2] using add_twice_torsionHC2

theorem source_no_degree_two_group_isomorphism : ¬Nonempty (SourceHC 0 ≃+ SourceHC 2) := by
  rintro ⟨e⟩
  apply no_degree_two_group_isomorphism
  exact ⟨(sourceHomologyEquiv 0).symm.toAddEquiv.trans
    (e.trans (sourceHomologyEquiv 2).toAddEquiv)⟩

theorem complete_counterexample :
    Nonempty (R ≃ₐ[ℤ] D) ∧
    (∀ x : SourceHC 0, x + x = 0 → x = 0) ∧
    (∃ x : SourceHC 2, x ≠ 0 ∧ x + x = 0) ∧
    ¬Nonempty (SourceHC 0 ≃+ SourceHC 2) :=
  ⟨⟨quotientDualEquiv⟩, sourceHC0_no_two_torsion,
    ⟨sourceTorsionHC2, sourceTorsion_nonzero, sourceTorsion_order_two⟩,
    source_no_degree_two_group_isomorphism⟩

/- Check the finite norm sum against genuine iterates of a cyclic rotation. -/
open Fin.NatCast

def tupleRotation (n : ℕ) (x : Fin (n + 1) → D) : Fin (n + 1) → D :=
  cyclicTuple x 1

theorem cyclicTuple_zero {n : ℕ} (x : Fin (n + 1) → D) : cyclicTuple x 0 = x := by
  funext k
  simp [cyclicTuple]

theorem cyclicTuple_add {n : ℕ} (x : Fin (n + 1) → D) (i j : Fin (n + 1)) :
    cyclicTuple (cyclicTuple x i) j = cyclicTuple x (i + j) := by
  funext k
  change x ((k - j) - i) = x (k - (i + j))
  congr 1
  abel

theorem cyclicTuple_iterate (n m : ℕ) (x : Fin (n + 1) → D) :
    (tupleRotation n)^[m] x = cyclicTuple x (m : Fin (n + 1)) := by
  induction m with
  | zero => simp [cyclicTuple_zero]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    change cyclicTuple (cyclicTuple x (m : Fin (n + 1))) 1 = _
    rw [cyclicTuple_add]
    simp

theorem connes_is_signed_rotation_norm {n : ℕ} (f : Cochains (n + 1))
    (x : Fin (n + 1) → D) :
    connesEvaluation f x = ∑ i : Fin (n + 1), ((-1 : ℤ) ^ n) ^ i.val *
      (f (Fin.cons 1 ((tupleRotation n)^[i.val] x)) -
        (-1 : ℤ) ^ (n + 1) * f (lastToFirst (Fin.cons 1 ((tupleRotation n)^[i.val] x)))) := by
  simp only [connesEvaluation, cyclicTuple_iterate, ← pow_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (i.val : Fin (n + 1)) = i := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt
  rw [hi]

end
end TLMC1537
