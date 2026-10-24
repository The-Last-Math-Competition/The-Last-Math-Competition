import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Ideal.Prod
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
The algebra is Q x Q.  All finite-dimensional modules, rather than a chosen list
of representatives, occur in the sequence type below.  The right-hand object is
the positive rational atlas of the coefficient-free A cluster variety of its
actual Ext-quiver.  This file concerns these conventions in the printed claim.
-/

open CategoryTheory CategoryTheory.Abelian
open scoped BigOperators ModuleCat.Algebra

namespace TLMC553

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

abbrev A := ℚ × ℚ
abbrev Vertex := Fin 2

instance algebra_finite : Module.Finite ℚ A := inferInstance
instance algebra_semisimple : IsSemisimpleRing A := inferInstance

def vertexIdeal (i : Vertex) : Ideal A :=
  if i = 0 then RingHom.ker (RingHom.fst ℚ ℚ) else RingHom.ker (RingHom.snd ℚ ℚ)

theorem vertexIdeal_zero : vertexIdeal 0 = Ideal.prod (⊥ : Ideal ℚ) ⊤ := by
  ext x
  simp [vertexIdeal, RingHom.mem_ker]

theorem vertexIdeal_one : vertexIdeal 1 = Ideal.prod (⊤ : Ideal ℚ) ⊥ := by
  ext x
  simp [vertexIdeal, RingHom.mem_ker]

theorem vertexIdeal_maximal (i : Vertex) : (vertexIdeal i).IsMaximal := by
  fin_cases i
  · exact RingHom.ker_isMaximal_of_surjective (RingHom.fst ℚ ℚ) Prod.fst_surjective
  · exact RingHom.ker_isMaximal_of_surjective (RingHom.snd ℚ ℚ) Prod.snd_surjective

theorem vertexIdeal_injective : Function.Injective vertexIdeal := by
  intro i j h
  fin_cases i <;> fin_cases j <;> try rfl
  · have hm := congrArg (fun I : Ideal A => (0, 1) ∈ I) h
    simp [vertexIdeal, RingHom.mem_ker] at hm
  · have hm := congrArg (fun I : Ideal A => (0, 1) ∈ I) h
    simp [vertexIdeal, RingHom.mem_ker] at hm

theorem maximal_classification (I : Ideal A) (hI : I.IsMaximal) :
    ∃ i : Vertex, I = vertexIdeal i := by
  rcases (Ideal.ideal_prod_prime I).mp hI.isPrime with
    ⟨J, hJ, h⟩ | ⟨J, hJ, h⟩
  · have hbot : J = ⊥ := (Ideal.eq_bot_or_top J).resolve_right hJ.ne_top
    exact ⟨0, h.trans (by rw [hbot, vertexIdeal_zero])⟩
  · have hbot : J = ⊥ := (Ideal.eq_bot_or_top J).resolve_right hJ.ne_top
    exact ⟨1, h.trans (by rw [hbot, vertexIdeal_one])⟩

abbrev Standard (i : Vertex) := A ⧸ vertexIdeal i

instance standard_simple (i : Vertex) : IsSimpleModule A (Standard i) := by
  rw [isSimpleModule_iff_isCoatom]
  exact (vertexIdeal_maximal i).out

instance standard_finite (i : Vertex) : Module.Finite A (Standard i) := inferInstance

def standardObject (i : Vertex) : ModuleCat.{0} A := ModuleCat.of A (Standard i)

instance standard_object_simple (i : Vertex) : IsSimpleModule A (standardObject i) :=
  standard_simple i

theorem standard_annihilator (i : Vertex) :
    Module.annihilator A (standardObject i) = vertexIdeal i :=
  Ideal.annihilator_quotient

theorem standard_nonisomorphic {i j : Vertex}
    (e : standardObject i ≃ₗ[A] standardObject j) : i = j := by
  apply vertexIdeal_injective
  simpa only [standard_annihilator] using e.annihilator_eq

def Indecomposable (M : ModuleCat.{0} A) : Prop :=
  Nontrivial M ∧ ∀ P Q : Submodule A M, IsCompl P Q → P = ⊥ ∨ Q = ⊥

theorem indecomposable_iff_simple (M : ModuleCat.{0} A) :
    Indecomposable M ↔ IsSimpleModule A M := by
  constructor
  · rintro ⟨hn, h⟩
    letI := hn
    apply (isSimpleModule_iff A M).mpr
    refine ⟨fun P => ?_⟩
    obtain ⟨Q, hQ⟩ := exists_isCompl P
    rcases h P Q hQ with hp | hq
    · exact Or.inl hp
    · right
      simpa [hq] using hQ.sup_eq_top
  · intro h
    letI := h
    refine ⟨IsSimpleModule.nontrivial A M, fun P Q hc => ?_⟩
    rcases eq_bot_or_eq_top P with hp | hp
    · exact Or.inl hp
    · right
      simpa [hp] using hc.inf_eq_bot

theorem simple_classification (M : ModuleCat.{0} A) [IsSimpleModule A M] :
    ∃ i : Vertex, Nonempty (M ≃ₗ[A] standardObject i) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := A) (M := M)).mp inferInstance
  obtain ⟨i, rfl⟩ := maximal_classification I hI
  exact ⟨i, ⟨e⟩⟩

theorem simple_finite_dimensional (M : ModuleCat.{0} A) [IsSimpleModule A M] :
    Module.Finite ℚ M := by
  letI : Module.Finite A M := inferInstance
  exact Module.Finite.trans A M

abbrev SimpleObject := {M : ModuleCat.{0} A // IsSimpleModule A M}

def simpleIso : Setoid SimpleObject where
  r M N := Nonempty (M.1 ≃ₗ[A] N.1)
  iseqv := ⟨fun _ => ⟨LinearEquiv.refl A _⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

abbrev SimpleClass := Quotient simpleIso

def standardClass (i : Vertex) : SimpleClass :=
  Quotient.mk _ ⟨standardObject i, standard_simple i⟩

theorem standardClass_bijective : Function.Bijective standardClass := by
  constructor
  · intro i j h
    obtain ⟨e⟩ := Quotient.exact h
    exact standard_nonisomorphic e
  · intro q
    induction q using Quotient.inductionOn with
    | h M =>
      letI := M.property
      obtain ⟨i, ⟨e⟩⟩ := simple_classification M.1
      exact ⟨i, Quotient.sound ⟨e.symm⟩⟩

def simpleClassEquiv : Vertex ≃ SimpleClass :=
  Equiv.ofBijective standardClass standardClass_bijective

instance simpleClass_finite : Finite SimpleClass :=
  Finite.of_surjective standardClass standardClass_bijective.surjective

def algebraRank : ℕ := Nat.card SimpleClass

theorem algebraRank_two : algebraRank = 2 := by
  rw [algebraRank, ← Nat.card_congr simpleClassEquiv]
  simp

theorem all_modules_projective (M : ModuleCat.{0} A) : Module.Projective A M := by
  apply Module.Projective.of_lifting_property''
  intro f hf
  exact IsSemisimpleModule.lifting_property f hf LinearMap.id

instance all_objects_projective (M : ModuleCat.{0} A) : Projective M := by
  letI := all_modules_projective M
  infer_instance

theorem all_ext_one_zero (M N : ModuleCat.{0} A) (e : Ext M N 1) : e = 0 :=
  Ext.eq_zero_of_projective e

instance ext_one_subsingleton (M N : ModuleCat.{0} A) : Subsingleton (Ext M N 1) :=
  ⟨fun x y => (all_ext_one_zero M N x).trans (all_ext_one_zero M N y).symm⟩

theorem every_surjection_splits (M N : ModuleCat.{0} A) (f : M →ₗ[A] N)
    (hf : Function.Surjective f) : ∃ s : N →ₗ[A] M, f.comp s = LinearMap.id :=
  IsSemisimpleModule.lifting_property f hf LinearMap.id

theorem ext_vanishing_iff_splitting (M : ModuleCat.{0} A) :
    (∀ N : ModuleCat.{0} A, ∀ e : Ext M N 1, e = 0) ↔
      (∀ E : ModuleCat.{0} A, ∀ f : E →ₗ[A] M,
        Function.Surjective f → ∃ s : M →ₗ[A] E, f.comp s = LinearMap.id) := by
  constructor
  · intro _ E f hf
    exact every_surjection_splits E M f hf
  · intro _ N e
    exact all_ext_one_zero M N e

theorem indecomposable_end_division (M : ModuleCat.{0} A) (h : Indecomposable M)
    (f : Module.End A M) (hf : f ≠ 0) : IsUnit f := by
  letI := (indecomposable_iff_simple M).mp h
  letI := Classical.decEq (Module.End A M)
  letI : DivisionRing (Module.End A M) := Module.End.instDivisionRing
  exact isUnit_iff_ne_zero.mpr hf

theorem standard_cross_hom_zero {i j : Vertex} (hij : i ≠ j)
    (f : standardObject i →ₗ[A] standardObject j) : f = 0 := by
  rcases f.bijective_or_eq_zero with hf | hf
  · exact False.elim (hij (standard_nonisomorphic (LinearEquiv.ofBijective f hf)))
  · exact hf

theorem standard_hom_nonzero (i : Vertex) :
    (LinearMap.id : standardObject i →ₗ[A] standardObject i) ≠ 0 := by
  letI := IsSimpleModule.nontrivial A (standardObject i)
  obtain ⟨x, hx⟩ := exists_ne (0 : standardObject i)
  intro h
  exact hx (DFunLike.congr_fun h x)

def extExchange (i j : Vertex) : ℤ :=
  (Module.finrank ℚ (Ext (standardObject i) (standardObject j) 1) : ℤ) -
    Module.finrank ℚ (Ext (standardObject j) (standardObject i) 1)

theorem ext_dimensions_zero (i j : Vertex) :
    Module.finrank ℚ (Ext (standardObject i) (standardObject j) 1) = 0 :=
  Module.finrank_zero_of_subsingleton

theorem extExchange_zero (i j : Vertex) : extExchange i j = 0 := by
  simp [extExchange, ext_dimensions_zero]

/- The indecomposable finite-dimensional module type and its actual isomorphism
quotient are used here.  No list of two labels replaces the module category. -/
structure CompleteSequence where
  obj : Vertex → ModuleCat.{0} A
  finite : ∀ i, Module.Finite A (obj i)
  indecomposable : ∀ i, Indecomposable (obj i)
  backward_hom : ∀ i j, j < i → ∀ f : obj i →ₗ[A] obj j, f = 0
  backward_ext : ∀ i j, j < i → ∀ e : Ext (obj i) (obj j) 1, e = 0

theorem complete_length (_E : CompleteSequence) : Fintype.card Vertex = algebraRank := by
  simp [algebraRank_two]

theorem sequence_objects_finite_dimensional (E : CompleteSequence) (i : Vertex) :
    Module.Finite ℚ (E.obj i) := by
  letI := E.finite i
  exact Module.Finite.trans A (E.obj i)

def sequenceIso : Setoid CompleteSequence where
  r E F := ∀ i, Nonempty (E.obj i ≃ₗ[A] F.obj i)
  iseqv := ⟨fun _ _ => ⟨LinearEquiv.refl A _⟩,
    fun h i => let ⟨e⟩ := h i; ⟨e.symm⟩,
    fun h g i => let ⟨e⟩ := h i; let ⟨f⟩ := g i; ⟨e.trans f⟩⟩

abbrev SequenceClass := Quotient sequenceIso

def sequenceClasses (E : CompleteSequence) : Vertex → SimpleClass :=
  fun i => Quotient.mk _ ⟨E.obj i, (indecomposable_iff_simple _).mp (E.indecomposable i)⟩

def sequenceClassMap : SequenceClass → (Vertex → SimpleClass) :=
  Quotient.lift sequenceClasses (by
    intro E F h
    funext i
    exact Quotient.sound (h i))

theorem sequenceClassMap_injective : Function.Injective sequenceClassMap := by
  intro E F
  induction E using Quotient.inductionOn with
  | h E =>
    induction F using Quotient.inductionOn with
    | h F =>
      intro h
      apply Quotient.sound
      intro i
      exact Quotient.exact (congrFun h i)

instance sequenceClass_finite : Finite SequenceClass :=
  Finite.of_injective sequenceClassMap sequenceClassMap_injective

def standardSequence : CompleteSequence where
  obj := standardObject
  finite := standard_finite
  indecomposable i := (indecomposable_iff_simple _).mpr (standard_simple i)
  backward_hom _i _j h := standard_cross_hom_zero (ne_of_gt h)
  backward_ext _i _j _h := all_ext_one_zero _ _

theorem sequence_class_nonempty : Nonempty SequenceClass :=
  ⟨Quotient.mk _ standardSequence⟩

/- The residue fields at the actual two simple modules are Q.  Consequently the
two vertices of the associated Ext-quiver are split vertices of weight one. -/
def standardResidueEquiv (i : Vertex) : Standard i ≃+* ℚ := by
  by_cases hi : i = 0
  · subst i
    exact (RingHom.fst ℚ ℚ).quotientKerEquivOfSurjective Prod.fst_surjective
  · have hi1 : i = 1 := by
      apply Fin.ext
      have hb := i.isLt
      have hz : i.val ≠ 0 := by
        intro hz
        exact hi (Fin.ext hz)
      change i.val = 1
      change i.val < 2 at hb
      omega
    subst i
    exact (RingHom.snd ℚ ℚ).quotientKerEquivOfSurjective Prod.snd_surjective

theorem standard_end_value (i : Vertex) (f : Module.End A (Standard i)) (x : Standard i) :
    f x = x * f 1 := by
  refine Quotient.inductionOn' x (fun a => ?_)
  have h : (Quotient.mk'' a : Standard i) = a • (1 : Standard i) := by
    change (Submodule.Quotient.mk a : Standard i) = Submodule.Quotient.mk (a * 1)
    rw [mul_one]
  rw [h, f.map_smul]
  refine Quotient.inductionOn' (f 1) (fun b => ?_)
  change (Submodule.Quotient.mk (a * b) : Standard i) =
    Submodule.Quotient.mk ((a * 1) * b)
  rw [mul_one]

def standardMultiplyEnd (i : Vertex) (r : Standard i) : Module.End A (Standard i) where
  toFun x := x * r
  map_add' x y := add_mul x y r
  map_smul' a x := by
    refine Quotient.inductionOn' x (fun b => ?_)
    refine Quotient.inductionOn' r (fun c => ?_)
    change (Submodule.Quotient.mk ((a * b) * c) : Standard i) =
      Submodule.Quotient.mk (a * (b * c))
    rw [mul_assoc]

def standardEndResidueEquiv (i : Vertex) : Module.End A (Standard i) ≃+* Standard i where
  toFun f := f 1
  invFun := standardMultiplyEnd i
  left_inv f := by
    apply LinearMap.ext
    intro x
    exact (standard_end_value i f x).symm
  right_inv r := one_mul r
  map_mul' f g := by
    change f (g 1) = f 1 * g 1
    rw [standard_end_value]
    exact mul_comm _ _
  map_add' f g := rfl

def standardEndFieldEquiv (i : Vertex) : Module.End A (Standard i) ≃+* ℚ :=
  (standardEndResidueEquiv i).trans (standardResidueEquiv i)

def ExtAdjacent (i j : Vertex) : Prop :=
  (∃ e : Ext (standardObject i) (standardObject j) 1, e ≠ 0) ∨
    (∃ e : Ext (standardObject j) (standardObject i) 1, e ≠ 0)

theorem no_ext_edges (i j : Vertex) : ¬ ExtAdjacent i j := by
  rintro (⟨e, h⟩ | ⟨e, h⟩)
  · exact h (all_ext_one_zero _ _ e)
  · exact h (all_ext_one_zero _ _ e)

structure LabelledSeed where
  exchange : Vertex → Vertex → ℤ
  multiplier : Vertex → ℕ
  frozen : Set Vertex

def algebraSeed : LabelledSeed where
  exchange := extExchange
  multiplier := fun _ => 1
  frozen := ∅

theorem algebraSeed_skew (i j : Vertex) :
    algebraSeed.exchange i j = -algebraSeed.exchange j i := by
  simp [algebraSeed, extExchange_zero]

def mutateExchange (B : Vertex → Vertex → ℤ) (k i j : Vertex) : ℤ :=
  if i = k ∨ j = k then -B i j
  else B i j + (|B i k| * B k j + B i k * |B k j|) / 2

def mutateSeed (S : LabelledSeed) (k : Vertex) : LabelledSeed where
  exchange := mutateExchange S.exchange k
  multiplier := S.multiplier
  frozen := S.frozen

def seedAt : List Vertex → LabelledSeed
  | [] => algebraSeed
  | k :: w => mutateSeed (seedAt w) k

theorem seedAt_zero (w : List Vertex) (i j : Vertex) :
    (seedAt w).exchange i j = 0 := by
  induction w generalizing i j with
  | nil => exact extExchange_zero i j
  | cons k w ih =>
    simp only [seedAt, mutateSeed, mutateExchange, ih, abs_zero,
      mul_zero, zero_add, Int.zero_ediv, neg_zero, ite_self]

theorem seedAt_unfrozen (w : List Vertex) : (seedAt w).frozen = ∅ := by
  induction w <;> simp_all [seedAt, mutateSeed, algebraSeed]

theorem seedAt_weight (w : List Vertex) (i : Vertex) :
    (seedAt w).multiplier i = 1 := by
  induction w <;> simp_all [seedAt, mutateSeed, algebraSeed]

/- Actual rational points of the lattice torus Hom(Z^2,G_m), and its positive
part.  Coordinates are proved equivalent to these characters before gluing. -/
abbrev CharacterLattice := Vertex →₀ ℤ
abbrev TorusCharacter := CharacterLattice →+ Additive ℚˣ

def characterOfUnits (u : Vertex → ℚˣ) : TorusCharacter :=
  (Finsupp.linearCombination ℤ (fun i => Additive.ofMul (u i))).toAddMonoidHom

def characterCoordinates (χ : TorusCharacter) (i : Vertex) : ℚˣ :=
  (χ (Finsupp.single i 1)).toMul

theorem characterOfUnits_basis (u : Vertex → ℚˣ) (i : Vertex) :
    characterCoordinates (characterOfUnits u) i = u i := by
  simp [characterCoordinates, characterOfUnits]

theorem torusCharacter_ext {χ ψ : TorusCharacter}
    (h : ∀ i, characterCoordinates χ i = characterCoordinates ψ i) : χ = ψ := by
  apply Finsupp.addHom_ext
  intro i n
  have hs : Finsupp.single i n = n • (Finsupp.single i (1 : ℤ)) := by
    ext j
    by_cases hj : i = j <;> simp [hj, eq_comm]
  rw [hs, map_zsmul, map_zsmul]
  congr 1
  exact congrArg Additive.ofMul (h i)

def torusCoordinatesEquiv : TorusCharacter ≃ (Vertex → ℚˣ) where
  toFun := characterCoordinates
  invFun := characterOfUnits
  left_inv _χ := torusCharacter_ext (fun i => characterOfUnits_basis _ i)
  right_inv u := funext (characterOfUnits_basis u)

abbrev PositiveCoordinates := {x : Vertex → ℚ // ∀ i, 0 < x i}
abbrev PositiveCharacter :=
  {χ : TorusCharacter // ∀ i, 0 < (characterCoordinates χ i : ℚ)}

def unitsOfPositive (x : PositiveCoordinates) (i : Vertex) : ℚˣ :=
  Units.mk0 (x.1 i) (ne_of_gt (x.2 i))

def positiveCharacterEquiv : PositiveCoordinates ≃ PositiveCharacter where
  toFun x := ⟨characterOfUnits (unitsOfPositive x), by
    intro i
    simpa [characterOfUnits_basis, unitsOfPositive] using x.2 i⟩
  invFun χ := ⟨fun i => (characterCoordinates χ.1 i : ℚ), χ.2⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    simp [characterOfUnits_basis, unitsOfPositive]
  right_inv χ := by
    apply Subtype.ext
    apply torusCharacter_ext
    intro i
    apply Units.ext
    simp [characterOfUnits_basis, unitsOfPositive]

/- Equation (14) of Fock--Goncharov, with no frozen variables.  Both monomials
are actual products.  They become one because the Ext exchange matrix is zero. -/
def aMutationFormula (S : LabelledSeed) (k : Vertex)
    (x : PositiveCoordinates) (i : Vertex) : ℚ :=
  if i = k then
    ((∏ j : Vertex, x.1 j ^ (max (S.exchange k j) 0).toNat) +
      (∏ j : Vertex, x.1 j ^ (max (-S.exchange k j) 0).toNat)) / x.1 k
  else x.1 i

theorem aMutationFormula_zero (w : List Vertex) (k i : Vertex)
    (x : PositiveCoordinates) :
    aMutationFormula (seedAt w) k x i = if i = k then 2 / x.1 k else x.1 i := by
  norm_num [aMutationFormula, seedAt_zero]

def mutatePositive (k : Vertex) (x : PositiveCoordinates) : PositiveCoordinates :=
  ⟨fun i => if i = k then 2 / x.1 k else x.1 i, by
    intro i
    change 0 < if i = k then 2 / x.1 k else x.1 i
    split
    · exact div_pos (by norm_num) (x.2 k)
    · exact x.2 i⟩

theorem mutatePositive_involutive (k : Vertex) : Function.Involutive (mutatePositive k) := by
  intro x
  apply Subtype.ext
  funext i
  by_cases h : i = k
  · subst i
    simp [mutatePositive]
  · simp [mutatePositive, h]

def mutationEquiv (k : Vertex) : PositiveCoordinates ≃ PositiveCoordinates :=
  (mutatePositive_involutive k).toPerm (mutatePositive k)

theorem mutation_exchange_relation (k : Vertex) (x : PositiveCoordinates) :
    x.1 k * (mutationEquiv k x).1 k = 2 := by
  change x.1 k * (if k = k then 2 / x.1 k else x.1 k) = 2
  simp only [ite_true]
  field_simp [ne_of_gt (x.2 k)]

theorem mutations_commute (i j : Vertex) (x : PositiveCoordinates) :
    mutationEquiv i (mutationEquiv j x) = mutationEquiv j (mutationEquiv i x) := by
  by_cases hij : i = j
  · subst j
    rfl
  apply Subtype.ext
  funext k
  change (mutatePositive i (mutatePositive j x)).1 k =
    (mutatePositive j (mutatePositive i x)).1 k
  by_cases hki : k = i
  · subst k
    simp [mutatePositive, hij, Ne.symm hij]
  · by_cases hkj : k = j
    · subst k
      simp [mutatePositive, hij, Ne.symm hij]
    · simp [mutatePositive, hki, hkj]

theorem mutation_is_formula14 (w : List Vertex) (k : Vertex) (x : PositiveCoordinates) :
    (mutationEquiv k x).1 = aMutationFormula (seedAt w) k x := by
  funext i
  exact (aMutationFormula_zero w k i x).symm

/- Words enumerate the entire labelled mutation tree.  To avoid quotienting a
single chart by the mutation action, an atlas point keeps its chart label.
Only points related by the actual transition map are identified. -/
def toBase : List Vertex → (PositiveCoordinates ≃ PositiveCoordinates)
  | [] => Equiv.refl _
  | k :: w => (mutationEquiv k).trans (toBase w)

def chartTransition (u v : List Vertex) : PositiveCoordinates ≃ PositiveCoordinates :=
  (toBase u).trans (toBase v).symm

theorem transition_identity (w : List Vertex) (x : PositiveCoordinates) :
    chartTransition w w x = x := by
  simp [chartTransition]

theorem transition_cocycle (u v w : List Vertex) (x : PositiveCoordinates) :
    chartTransition v w (chartTransition u v x) = chartTransition u w x := by
  simp [chartTransition]

theorem transition_mutation (w : List Vertex) (k : Vertex) (x : PositiveCoordinates) :
    chartTransition w (k :: w) x = mutationEquiv k x := by
  simp [chartTransition, toBase, mutationEquiv, Equiv.trans_apply]

abbrev AtlasPoint := List Vertex × PositiveCoordinates

def positiveAtlasSetoid : Setoid AtlasPoint where
  r p q := toBase p.1 p.2 = toBase q.1 q.2
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

abbrev GlobalPositive := Quotient positiveAtlasSetoid

def chartPoint (w : List Vertex) (x : PositiveCoordinates) : GlobalPositive :=
  Quotient.mk _ (w, x)

theorem chartPoint_eq_iff (u v : List Vertex) (x y : PositiveCoordinates) :
    chartPoint u x = chartPoint v y ↔ chartTransition u v x = y := by
  change Quotient.mk _ (u, x) = Quotient.mk _ (v, y) ↔ _
  rw [Quotient.eq]
  change toBase u x = toBase v y ↔ _
  constructor
  · intro h
    simpa [chartTransition] using congrArg (toBase v).symm h
  · intro h
    simpa [chartTransition] using congrArg (toBase v) h

theorem every_chart_bijective (w : List Vertex) : Function.Bijective (chartPoint w) := by
  constructor
  · intro x y h
    simpa [chartTransition] using (chartPoint_eq_iff w w x y).mp h
  · intro p
    induction p using Quotient.inductionOn with
    | h p =>
      refine ⟨chartTransition p.1 w p.2, ?_⟩
      exact ((chartPoint_eq_iff p.1 w p.2 _).mpr rfl).symm

def chartEquiv (w : List Vertex) : PositiveCoordinates ≃ GlobalPositive :=
  Equiv.ofBijective (chartPoint w) (every_chart_bijective w)

theorem adjacent_charts_glue_by_formula14
    (w : List Vertex) (k : Vertex) (x : PositiveCoordinates) :
    chartPoint w x = chartPoint (k :: w) (mutationEquiv k x) :=
  (chartPoint_eq_iff _ _ _ _).mpr (transition_mutation w k x)

def naturalCoordinate (n : ℕ) : PositiveCoordinates :=
  ⟨fun i => if i = 0 then (n : ℚ) + 1 else 1, by
    intro i
    change 0 < if i = 0 then (n : ℚ) + 1 else 1
    split <;> positivity⟩

theorem naturalCoordinate_injective : Function.Injective naturalCoordinate := by
  intro n m h
  have h0 := congrArg (fun x : PositiveCoordinates => x.1 0) h
  simpa [naturalCoordinate] using h0

def infiniteGlobalFamily (n : ℕ) : GlobalPositive := chartPoint [] (naturalCoordinate n)

theorem infiniteGlobalFamily_injective : Function.Injective infiniteGlobalFamily :=
  (every_chart_bijective []).injective.comp naturalCoordinate_injective

instance globalPositive_infinite : Infinite GlobalPositive :=
  Infinite.of_injective infiniteGlobalFamily infiniteGlobalFamily_injective

theorem no_counting_bijection : ¬ Nonempty (SequenceClass ≃ GlobalPositive) := by
  rintro ⟨e⟩
  haveI : Finite GlobalPositive := Finite.of_equiv SequenceClass e
  exact not_finite GlobalPositive

theorem complete_counterexample :
    algebraRank = 2 ∧ Nonempty SequenceClass ∧ Finite SequenceClass ∧
      Infinite GlobalPositive ∧ ¬ Nonempty (SequenceClass ≃ GlobalPositive) :=
  ⟨algebraRank_two, sequence_class_nonempty, inferInstance, inferInstance, no_counting_bijection⟩

end
end TLMC553
