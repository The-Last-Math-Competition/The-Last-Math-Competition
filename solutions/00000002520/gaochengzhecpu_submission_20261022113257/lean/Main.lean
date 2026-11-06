import Mathlib.Analysis.Fourier.ZMod
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Tactic.Ring

open scoped BigOperators TensorProduct

namespace TensorFourier

def Grid : List ℕ → Type
  | [] => Unit
  | n :: ns => ZMod (n+1) × Grid ns

instance gridFintype : (ns : List ℕ) → Fintype (Grid ns)
  | [] => inferInstanceAs (Fintype Unit)
  | n :: ns => by
    letI := gridFintype ns
    exact inferInstanceAs (Fintype (ZMod (n+1) × Grid ns))

instance gridDecidableEq : (ns : List ℕ) → DecidableEq (Grid ns)
  | [] => inferInstanceAs (DecidableEq Unit)
  | n :: ns => by
    letI := gridDecidableEq ns
    exact inferInstanceAs (DecidableEq (ZMod (n+1) × Grid ns))

def Factors : List ℕ → Type
  | [] => Unit
  | n :: ns => (ZMod (n+1) → ℂ) × Factors ns

noncomputable def pure : (ns : List ℕ) → Factors ns → Grid ns → ℂ
  | [], _, _ => 1
  | _ :: ns, f, j => f.1 j.1 * pure ns f.2 j.2

noncomputable def forwardFactors : (ns : List ℕ) → Factors ns → Factors ns
  | [], f => f
  | _ :: ns, f => (ZMod.dft f.1, forwardFactors ns f.2)

noncomputable def inverseFactors : (ns : List ℕ) → Factors ns → Factors ns
  | [], f => f
  | _ :: ns, f => (ZMod.dft.symm f.1, inverseFactors ns f.2)

noncomputable def curryEquiv (A B : Type) : ((A × B) → ℂ) ≃ₗ[ℂ] (A → B → ℂ) where
  toFun f a b := f (a,b)
  invFun f j := f j.1 j.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def dftAll : (ns : List ℕ) → (Grid ns → ℂ) ≃ₗ[ℂ] (Grid ns → ℂ)
  | [] => LinearEquiv.refl _ _
  | n :: ns =>
    (curryEquiv (ZMod (n+1)) (Grid ns)).trans
      ((LinearEquiv.piCongrRight (fun _ : ZMod (n+1) => dftAll ns)).trans
        ((ZMod.dft (N := n+1) (E := Grid ns → ℂ)).trans
          (curryEquiv (ZMod (n+1)) (Grid ns)).symm))

theorem dftAll_cons (n : ℕ) (ns : List ℕ) (f : Grid (n::ns) → ℂ)
    (k : Grid (n::ns)) :
    dftAll (n::ns) f k =
      ∑ j : ZMod (n+1), ZMod.stdAddChar (-(j*k.1)) *
        dftAll ns (fun l => f (j,l)) k.2 := by
  change (ZMod.dft (fun j => dftAll ns (fun l => f (j,l))) k.1) k.2 = _
  rw [ZMod.dft_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem dftAll_pure (ns : List ℕ) (f : Factors ns) :
    dftAll ns (pure ns f) = pure ns (forwardFactors ns f) := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    ext k
    rw [dftAll_cons]
    simp only [pure, forwardFactors]
    have he (j : ZMod (n+1)) :
        dftAll ns (fun l => f.1 j * pure ns f.2 l) =
          f.1 j • dftAll ns (pure ns f.2) := by
      exact (dftAll ns).map_smul (f.1 j) (pure ns f.2)
    simp_rw [he, ih f.2, Pi.smul_apply, smul_eq_mul]
    simp_rw [ZMod.dft_apply, smul_eq_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring

noncomputable def phase : (ns : List ℕ) → Grid ns → Grid ns → ℂ
  | [], _, _ => 1
  | _ :: ns, k, j => ZMod.stdAddChar (-(j.1*k.1)) * phase ns k.2 j.2

noncomputable def positivePhase : (ns : List ℕ) → Grid ns → Grid ns → ℂ
  | [], _, _ => 1
  | _ :: ns, j, k => ZMod.stdAddChar (j.1*k.1) * positivePhase ns j.2 k.2

noncomputable def normalization : List ℕ → ℂ
  | [] => 1
  | n :: ns => (n+1 : ℂ)⁻¹ * normalization ns

theorem dftAll_sum (ns : List ℕ) (f : Grid ns → ℂ) (k : Grid ns) :
    dftAll ns f k = ∑ j, phase ns k j * f j := by
  induction ns with
  | nil => cases k; simp [dftAll, Grid, phase]
  | cons n ns ih =>
    rw [dftAll_cons]
    simp_rw [ih]
    simp only [Grid, Fintype.sum_prod_type, phase, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring

theorem forward_inverse_factors (ns : List ℕ) (f : Factors ns) :
    forwardFactors ns (inverseFactors ns f) = f := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    change (ZMod.dft (ZMod.dft.symm f.1),
      forwardFactors ns (inverseFactors ns f.2)) = f
    rw [LinearEquiv.apply_symm_apply, ih]
    exact Prod.eta f

theorem inverse_pure (ns : List ℕ) (f : Factors ns) :
    (dftAll ns).symm (pure ns f) = pure ns (inverseFactors ns f) := by
  apply (dftAll ns).injective
  rw [LinearEquiv.apply_symm_apply, dftAll_pure, forward_inverse_factors]

theorem inverse_cons (n : ℕ) (ns : List ℕ) (f : Grid (n::ns) → ℂ)
    (j : Grid (n::ns)) :
    (dftAll (n::ns)).symm f j =
      (dftAll ns).symm (fun l => (n+1 : ℂ)⁻¹ *
        ∑ k : ZMod (n+1), ZMod.stdAddChar (j.1*k) * f (k,l)) j.2 := by
  change (dftAll ns).symm
    (fun l => (ZMod.dft.symm (fun k => fun r => f (k,r)) j.1) l) j.2 = _
  have he : (fun l => (ZMod.dft.symm (fun k => fun r => f (k,r)) j.1) l) =
      (fun l => (n+1 : ℂ)⁻¹ * ∑ k : ZMod (n+1),
        ZMod.stdAddChar (j.1*k) * f (k,l)) := by
    funext l
    rw [ZMod.invDFT_apply]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, mul_comm j.1]
    norm_cast
  rw [he]

theorem inverse_sum (ns : List ℕ) (f : Grid ns → ℂ) (j : Grid ns) :
    (dftAll ns).symm f j = normalization ns * ∑ k, positivePhase ns j k * f k := by
  induction ns with
  | nil => cases j; simp [dftAll, Grid, positivePhase, normalization]
  | cons n ns ih =>
    rw [inverse_cons, ih]
    simp only [Grid, Fintype.sum_prod_type, positivePhase, normalization,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring

noncomputable def fourierBasis (ns : List ℕ) : Basis (Grid ns) ℂ (Grid ns → ℂ) :=
  Basis.ofEquivFun (dftAll ns)

theorem fourierBasis_apply (ns : List ℕ) (k j : Grid ns) :
    fourierBasis ns k j = normalization ns * positivePhase ns j k := by
  rw [fourierBasis, Basis.coe_ofEquivFun]
  change (dftAll ns).symm (Pi.single k 1) j = _
  rw [inverse_sum]
  simp [Pi.single_apply, mul_ite, Finset.sum_ite_eq']

noncomputable def oneDimBasis (n : ℕ) : Basis (ZMod (n+1)) ℂ (ZMod (n+1) → ℂ) :=
  Basis.ofEquivFun (ZMod.dft (N := n+1) (E := ℂ))

theorem oneDimBasis_apply (n : ℕ) (k j : ZMod (n+1)) :
    oneDimBasis n k j = (n+1 : ℂ)⁻¹ * ZMod.stdAddChar (j*k) := by
  rw [oneDimBasis, Basis.coe_ofEquivFun]
  change ZMod.dft.symm (Pi.single k (1 : ℂ)) j = _
  rw [ZMod.invDFT_apply]
  simp [Pi.single_apply, mul_comm j, mul_ite, Finset.sum_ite_eq']

noncomputable def productBasisVector : (ns : List ℕ) → Grid ns → Grid ns → ℂ
  | [], _, _ => 1
  | n :: ns, k, j => oneDimBasis n k.1 j.1 * productBasisVector ns k.2 j.2

theorem productBasisVector_formula (ns : List ℕ) (k j : Grid ns) :
    productBasisVector ns k j = normalization ns * positivePhase ns j k := by
  induction ns with
  | nil => simp [productBasisVector, normalization, positivePhase]
  | cons n ns ih =>
    simp only [productBasisVector, oneDimBasis_apply, ih, normalization, positivePhase]
    ring

theorem separated_basis (ns : List ℕ) (k j : Grid ns) :
    fourierBasis ns k j = productBasisVector ns k j := by
  rw [fourierBasis_apply, productBasisVector_formula]

theorem fourier_coefficients (ns : List ℕ) (f : Grid ns → ℂ) (k : Grid ns) :
    (fourierBasis ns).repr f k = dftAll ns f k :=
  Basis.ofEquivFun_repr_apply _ _ _

theorem dftAll_separable_axis (n : ℕ) (ns : List ℕ)
    (f : ZMod (n+1) → ℂ) (g : Grid ns → ℂ) (k : Grid (n::ns)) :
    dftAll (n::ns) (fun j => f j.1 * g j.2) k =
      ZMod.dft f k.1 * dftAll ns g k.2 := by
  rw [dftAll_cons]
  have he (j : ZMod (n+1)) :
      dftAll ns (fun l => f j * g l) = f j • dftAll ns g :=
    (dftAll ns).map_smul (f j) g
  simp_rw [he, Pi.smul_apply, smul_eq_mul, ZMod.dft_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

noncomputable def tensorCoordinates (n : ℕ) (ns : List ℕ) :
    ((Grid ns → ℂ) ⊗[ℂ] (ZMod (n+1) → ℂ)) ≃ₗ[ℂ] (Grid (n::ns) → ℂ) :=
  (TensorProduct.piScalarRight ℂ ℂ (Grid ns → ℂ) (ZMod (n+1))).trans
    (curryEquiv (ZMod (n+1)) (Grid ns)).symm

theorem tensorCoordinates_tmul (n : ℕ) (ns : List ℕ)
    (g : Grid ns → ℂ) (f : ZMod (n+1) → ℂ) (j : Grid (n::ns)) :
    tensorCoordinates n ns (g ⊗ₜ[ℂ] f) j = f j.1 * g j.2 := by
  change TensorProduct.piScalarRight ℂ ℂ (Grid ns → ℂ) (ZMod (n+1))
    (g ⊗ₜ[ℂ] f) j.1 j.2 = _
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  rfl

theorem tensor_factorization (n : ℕ) (ns : List ℕ)
    (t : (Grid ns → ℂ) ⊗[ℂ] (ZMod (n+1) → ℂ)) :
    tensorCoordinates n ns (TensorProduct.congr (dftAll ns) ZMod.dft t) =
      dftAll (n::ns) (tensorCoordinates n ns t) := by
  induction t using TensorProduct.induction_on with
  | zero =>
    rw [(TensorProduct.congr (dftAll ns) (ZMod.dft (N := n+1) (E := ℂ))).map_zero,
      (tensorCoordinates n ns).map_zero, (dftAll (n::ns)).map_zero]
  | tmul g f =>
    ext j
    rw [TensorProduct.congr_tmul, tensorCoordinates_tmul]
    have he : tensorCoordinates n ns (g ⊗ₜ[ℂ] f) = fun l => f l.1 * g l.2 := by
      ext l
      exact tensorCoordinates_tmul n ns g f l
    rw [he, dftAll_separable_axis]
  | add t s ht hs => simp only [map_add, ht, hs]

theorem tensor_product_basis (n : ℕ) (ns : List ℕ)
    (k : ZMod (n+1)) (l : Grid ns) :
    tensorCoordinates n ns ((fourierBasis ns).tensorProduct (oneDimBasis n) (l,k)) =
      fourierBasis (n::ns) (k,l) := by
  ext j
  rw [Basis.tensorProduct_apply, tensorCoordinates_tmul, fourierBasis_apply,
    fourierBasis_apply, oneDimBasis_apply]
  simp only [normalization, positivePhase]
  ring

theorem inverse_tensor_factorization (n : ℕ) (ns : List ℕ)
    (t : (Grid ns → ℂ) ⊗[ℂ] (ZMod (n+1) → ℂ)) :
    tensorCoordinates n ns
        ((TensorProduct.congr (dftAll ns) (ZMod.dft (N := n+1) (E := ℂ))).symm t) =
      (dftAll (n::ns)).symm (tensorCoordinates n ns t) := by
  apply (dftAll (n::ns)).injective
  rw [LinearEquiv.apply_symm_apply]
  have he := tensor_factorization n ns
    ((TensorProduct.congr (dftAll ns) (ZMod.dft (N := n+1) (E := ℂ))).symm t)
  rw [LinearEquiv.apply_symm_apply] at he
  exact he.symm

/-- Every positive axis length is represented by an entry plus one. -/
theorem encode_positive_dimensions (ds : List ℕ) (h : ∀ d ∈ ds, 0 < d) :
    ∃ ns : List ℕ, ns.map Nat.succ = ds := by
  induction ds with
  | nil => exact ⟨[], rfl⟩
  | cons d ds ih =>
    obtain ⟨ns, hns⟩ := ih (fun a ha => h a (List.mem_cons_of_mem d ha))
    refine ⟨d.pred :: ns, ?_⟩
    simp only [List.map_cons, hns]
    rw [Nat.succ_pred_eq_of_pos (h d (List.mem_cons_self))]

def Conjecture : Prop := ∀ ns : List ℕ,
  (∀ (f : Grid ns → ℂ) k,
    dftAll ns f k = ∑ j, phase ns k j * f j) ∧
  (∀ (f : Grid ns → ℂ) j,
    (dftAll ns).symm f j = normalization ns * ∑ k, positivePhase ns j k * f k) ∧
  (∀ f : Factors ns, dftAll ns (pure ns f) = pure ns (forwardFactors ns f)) ∧
  (∀ f : Factors ns, (dftAll ns).symm (pure ns f) = pure ns (inverseFactors ns f)) ∧
  (∀ k j : Grid ns, fourierBasis ns k j = productBasisVector ns k j) ∧
  (∀ (n : ℕ) (t : (Grid ns → ℂ) ⊗[ℂ] (ZMod (n+1) → ℂ)),
    tensorCoordinates n ns (TensorProduct.congr (dftAll ns) ZMod.dft t) =
      dftAll (n::ns) (tensorCoordinates n ns t)) ∧
  (∀ (n : ℕ) (k : ZMod (n+1)) (l : Grid ns),
    tensorCoordinates n ns ((fourierBasis ns).tensorProduct (oneDimBasis n) (l,k)) =
      fourierBasis (n::ns) (k,l))

theorem conjecture : Conjecture := by
  intro ns
  exact ⟨dftAll_sum ns, inverse_sum ns, dftAll_pure ns, inverse_pure ns,
    separated_basis ns, fun n t => tensor_factorization n ns t,
    fun n k l => tensor_product_basis n ns k l⟩

end TensorFourier

#print axioms TensorFourier.dftAll_sum
#print axioms TensorFourier.inverse_sum
#print axioms TensorFourier.dftAll_pure
#print axioms TensorFourier.inverse_pure
#print axioms TensorFourier.separated_basis
#print axioms TensorFourier.tensor_factorization
#print axioms TensorFourier.tensor_product_basis
#print axioms TensorFourier.inverse_tensor_factorization
#print axioms TensorFourier.conjecture
