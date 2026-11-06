import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Equiv.TransferInstance
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel

/-! A genuine Grothendieck group of finite-dimensional vector spaces.
The objects are bundled modules, and the defining relation is linear equivalence
of cross direct sums. Dimension is a theorem about this quotient, not its definition. -/

noncomputable section
namespace Conjecture6291

structure FD (K : Type) [Field K] where
  carrier : Type
  [addGroup : AddCommGroup carrier]
  [module : Module K carrier]
  [finite : Module.Finite K carrier]

attribute [instance] FD.addGroup FD.module FD.finite
instance (K : Type) [Field K] : CoeSort (FD K) Type := ⟨FD.carrier⟩

variable (K : Type) [Field K]

def space (n : ℕ) : FD K := ⟨Fin n → K⟩
def sum (P Q : FD K) : FD K := ⟨P × Q⟩
def dim (P : FD K) : ℕ := Module.finrank K P

@[simp] theorem dim_space (n : ℕ) : dim K (space K n) = n := by
  exact Module.finrank_fin_fun K

@[simp] theorem dim_sum (P Q : FD K) : dim K (sum K P Q) = dim K P + dim K Q := by
  exact Module.finrank_prod

/-- These are precisely finitely generated projective modules over the field. -/
theorem objects_projective (P : FD K) : Module.Finite K P ∧ Module.Projective K P :=
  ⟨inferInstance, inferInstance⟩

/-- Every finitely generated module over a field is an object used here. -/
def ofModule (V : Type) [AddCommGroup V] [Module K V] [Module.Finite K V] : FD K := ⟨V⟩

theorem object_has_standard_basis (P : FD K) :
    Nonempty (P ≃ₗ[K] (Fin (dim K P) → K)) := by
  apply FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
  simp [dim]

def pairRank (p : FD K × FD K) : ℤ := (dim K p.1 : ℤ) - dim K p.2

def StableRel (p q : FD K × FD K) : Prop :=
  Nonempty ((p.1 × q.2) ≃ₗ[K] (q.1 × p.2))

theorem stableRel_iff (p q : FD K × FD K) :
    StableRel K p q ↔ pairRank K p = pairRank K q := by
  unfold StableRel pairRank dim
  rw [FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq]
  simp only [Module.finrank_prod]
  omega

/-- The usual stable-isomorphism relation gives exactly the same quotient. -/
theorem stableRel_iff_stabilized (p q : FD K × FD K) :
    StableRel K p q ↔ ∃ T : FD K,
      Nonempty (((p.1 × q.2) × T) ≃ₗ[K] ((q.1 × p.2) × T)) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨space K 0, ⟨e.prodCongr (LinearEquiv.refl K _)⟩⟩
  · rintro ⟨T, ⟨e⟩⟩
    apply (stableRel_iff K p q).mpr
    have h := e.finrank_eq
    simp only [Module.finrank_prod] at h
    unfold pairRank dim
    omega

def stableSetoid : Setoid (FD K × FD K) where
  r := StableRel K
  iseqv := ⟨fun p => (stableRel_iff K p p).mpr rfl,
    fun h => (stableRel_iff K _ _).mpr ((stableRel_iff K _ _).mp h).symm,
    fun h₁ h₂ => (stableRel_iff K _ _).mpr
      (((stableRel_iff K _ _).mp h₁).trans ((stableRel_iff K _ _).mp h₂))⟩

def K0 := Quotient (stableSetoid K)

def pairClass (P Q : FD K) : K0 K := Quotient.mk _ (P, Q)

def rank : K0 K → ℤ := Quotient.lift (pairRank K)
  (fun p q h => (stableRel_iff K p q).mp h)

@[simp] theorem rank_pairClass (P Q : FD K) :
    rank K (pairClass K P Q) = (dim K P : ℤ) - dim K Q := rfl

theorem rank_injective : Function.Injective (rank K) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro p q h
  exact Quotient.sound ((stableRel_iff K p q).mpr h)

theorem rank_surjective : Function.Surjective (rank K) := by
  intro z
  refine ⟨pairClass K (space K z.toNat) (space K (-z).toNat), ?_⟩
  simp only [rank_pairClass, dim_space]
  omega

def rankEquiv : K0 K ≃ ℤ := Equiv.ofBijective (rank K)
  ⟨rank_injective K, rank_surjective K⟩

instance : AddCommGroup (K0 K) := (rankEquiv K).addCommGroup

def rankIso : K0 K ≃+ ℤ := (rankEquiv K).addEquiv

@[simp] theorem rank_zero : rank K 0 = 0 := (rankIso K).map_zero
@[simp] theorem rank_add (x y : K0 K) : rank K (x + y) = rank K x + rank K y :=
  (rankIso K).map_add x y
@[simp] theorem rank_neg (x : K0 K) : rank K (-x) = -rank K x :=
  (rankIso K).map_neg x

instance : PartialOrder (K0 K) := PartialOrder.lift (rank K) (rank_injective K)

instance : IsOrderedAddMonoid (K0 K) where
  add_le_add_left a b h c := by
    change rank K (c + a) ≤ rank K (c + b)
    change rank K a ≤ rank K b at h
    simpa only [rank_add] using add_le_add_left h (rank K c)

def rankOrderIso : K0 K ≃+o ℤ where
  toAddEquiv := rankIso K
  map_le_map_iff' := Iff.rfl

/-- Addition really is direct sum in both coordinates. -/
theorem pairClass_add (P Q R S : FD K) :
    pairClass K P Q + pairClass K R S = pairClass K (sum K P R) (sum K Q S) := by
  apply rank_injective K
  simp only [rank_add, rank_pairClass, dim_sum, Nat.cast_add]
  omega

theorem pairClass_neg (P Q : FD K) :
    -pairClass K P Q = pairClass K Q P := by
  apply rank_injective K
  simp only [rank_neg, rank_pairClass]
  omega

theorem pairClass_zero : pairClass K (space K 0) (space K 0) = 0 := by
  apply rank_injective K
  simp

def objectClass (P : FD K) : K0 K := pairClass K P (space K 0)

theorem pairClass_eq_sub (P Q : FD K) :
    pairClass K P Q = objectClass K P - objectClass K Q := by
  apply rank_injective K
  change _ = (rankIso K) (objectClass K P - objectClass K Q)
  rw [map_sub]
  simp [objectClass, rankIso, rankEquiv]

theorem class_isomorphism (P Q : FD K) (e : P ≃ₗ[K] Q) :
    objectClass K P = objectClass K Q := by
  apply rank_injective K
  simp only [objectClass, rank_pairClass, dim_space, Nat.cast_zero, sub_zero]
  exact_mod_cast e.finrank_eq

theorem class_direct_sum (P Q : FD K) :
    objectClass K (sum K P Q) = objectClass K P + objectClass K Q := by
  apply rank_injective K
  simp [objectClass]

section UniversalProperty

variable {A : Type*} [AddCommGroup A]
variable (f : FD K → A)
variable (hiso : ∀ (P Q : FD K), Nonempty (P ≃ₗ[K] Q) → f P = f Q)
variable (hadd : ∀ (P Q : FD K), f (sum K P Q) = f P + f Q)
variable (hzero : f (space K 0) = 0)

def liftFunction : K0 K → A := Quotient.lift
  (fun p => f p.1 - f p.2) (by
    intro p q h
    have h' := hiso (sum K p.1 q.2) (sum K q.1 p.2) h
    rw [hadd, hadd] at h'
    exact sub_eq_sub_iff_add_eq_add.mpr h')

@[simp] theorem liftFunction_pairClass (P Q : FD K) :
    liftFunction K f hiso hadd (pairClass K P Q) = f P - f Q := rfl

/-- Universal group completion property, for arbitrary abelian target groups. -/
def lift : K0 K →+ A where
  toFun := liftFunction K f hiso hadd
  map_zero' := by
    rw [← pairClass_zero K]
    simp
  map_add' := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro p q
    change liftFunction K f hiso hadd (pairClass K p.1 p.2 + pairClass K q.1 q.2) =
      (f p.1 - f p.2) + (f q.1 - f q.2)
    rw [pairClass_add]
    simp only [liftFunction_pairClass, hadd]
    abel

include hzero in
@[simp] theorem lift_class (P : FD K) :
    lift K f hiso hadd (objectClass K P) = f P := by
  change f P - f (space K 0) = f P
  rw [hzero, sub_zero]

theorem lift_unique (g : K0 K →+ A) (hg : ∀ P, g (objectClass K P) = f P) :
    g = lift K f hiso hadd := by
  ext x
  refine Quotient.inductionOn x ?_
  intro p
  change g (pairClass K p.1 p.2) = f p.1 - f p.2
  rw [pairClass_eq_sub, map_sub, hg, hg]

include hiso hadd hzero in
theorem group_completion_universal :
    ∃! g : K0 K →+ A, ∀ P, g (objectClass K P) = f P := by
  refine ⟨lift K f hiso hadd, ?_, ?_⟩
  · intro P
    exact lift_class K f hiso hadd hzero P
  · intro g hg
    exact lift_unique K f hiso hadd g hg

end UniversalProperty

def Positive (x : K0 K) : Prop := ∃ P : FD K, x = pairClass K P (space K 0)

theorem positive_iff_rank (x : K0 K) : Positive K x ↔ 0 ≤ rank K x := by
  constructor
  · rintro ⟨P, rfl⟩
    simp [rank_pairClass]
  · intro h
    refine ⟨space K (rank K x).toNat, ?_⟩
    apply rank_injective K
    simp only [rank_pairClass, dim_space, Nat.cast_zero, sub_zero]
    omega

/-- The transported order is exactly the order generated by module classes. -/
theorem le_iff_positive_difference (x y : K0 K) : x ≤ y ↔ Positive K (y - x) := by
  rw [positive_iff_rank]
  change rank K x ≤ rank K y ↔ 0 ≤ (rankIso K) (y - x)
  rw [map_sub]
  change rank K x ≤ rank K y ↔ 0 ≤ rank K y - rank K x
  omega

def unitClass : K0 K := pairClass K (space K 1) (space K 0)

@[simp] theorem rank_unit : rank K (unitClass K) = 1 := by
  simp [unitClass]

theorem unit_is_regular_module : objectClass K (ofModule K K) = unitClass K := by
  apply rank_injective K
  simp [objectClass, unitClass, dim, ofModule, space]

def IsScaledOrderedIso (L : Type) [Field L] : Prop :=
  ∃ e : K0 K ≃+o K0 L, e (unitClass K) = unitClass L

theorem fields_same_scaled_ordered_K0 (L : Type) [Field L] : IsScaledOrderedIso K L := by
  let e := (rankOrderIso K).trans (rankOrderIso L).symm
  have he (x : K0 K) : rank L (e x) = rank K x := by
    exact (rankIso L).apply_symm_apply ((rankIso K) x)
  refine ⟨e, ?_⟩
  apply rank_injective L
  rw [he, rank_unit, rank_unit]

def RegularRing (R : Type) [Ring R] : Prop := ∀ a : R, ∃ b : R, a * b * a = a

theorem field_regular : RegularRing K := by
  intro a
  refine ⟨a⁻¹, ?_⟩
  by_cases h : a = 0
  · simp [h]
  · simp [h]

/-- A necessary restriction of the claimed completeness to regular fields. -/
def FieldCompleteness : Prop :=
  ∀ (F E : Type) [Field F] [Field E],
    RegularRing F → RegularRing E → IsScaledOrderedIso F E → Nonempty (F ≃+* E)

instance : Fact (Nat.Prime 2) := ⟨by decide⟩
instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem finite_fields_not_isomorphic : ¬ Nonempty ((ZMod 2) ≃+* (ZMod 3)) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr e.toEquiv
  norm_num only [ZMod.card] at h

theorem finite_fields_witness :
    RegularRing (ZMod 2) ∧ RegularRing (ZMod 3) ∧
    IsScaledOrderedIso (ZMod 2) (ZMod 3) ∧
    ¬ Nonempty ((ZMod 2) ≃+* (ZMod 3)) :=
  ⟨field_regular _, field_regular _, fields_same_scaled_ordered_K0 _ _,
    finite_fields_not_isomorphic⟩

theorem conjecture_6291_false : ¬ FieldCompleteness := by
  intro h
  exact finite_fields_not_isomorphic
    (h (ZMod 2) (ZMod 3) (field_regular _) (field_regular _)
      (fields_same_scaled_ordered_K0 _ _))

#print axioms fields_same_scaled_ordered_K0
#print axioms group_completion_universal
#print axioms stableRel_iff_stabilized
#print axioms le_iff_positive_difference
#print axioms conjecture_6291_false

end Conjecture6291
