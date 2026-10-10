import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Conjecture6338

abbrev G := ZMod 21

def D : Finset G := {3, 6, 7, 12, 14}

def differenceCount (S : Finset G) (g : G) : ℕ :=
  ((S.product S).filter (fun p => p.1 - p.2 = g)).card

/-- The usual ordered-difference definition of a (v,k,lambda)-difference set. -/
def IsDifferenceSet (S : Finset G) (v k lam : ℕ) : Prop :=
  Fintype.card G = v ∧ S.card = k ∧
    ∀ g : G, g ≠ 0 → differenceCount S g = lam

theorem difference_set : IsDifferenceSet D 21 5 1 := by
  unfold IsDifferenceSet
  decide +kernel

def translate (a : G) (S : Finset G) : Finset G := S.image (a + ·)

def dilate (m : G) (S : Finset G) : Finset G := S.image (m * ·)

/-- Numerical multipliers allow a translate, rather than requiring setwise fixing. -/
def IsMultiplier (m : G) : Prop :=
  Nat.Coprime m.val 21 ∧ ∃ a : G, dilate m D = translate a D

theorem multiplier_classification :
    ∀ m : G, IsMultiplier m ↔ m = 1 ∨ m = 2 ∨ m = 4 ∨ m = 8 ∨ m = 16 ∨ m = 11 := by
  unfold IsMultiplier
  decide +kernel

theorem translate_must_be_zero :
    ∀ m a : G, Nat.Coprime m.val 21 → dilate m D = translate a D → a = 0 := by decide +kernel

/-- Development into the 21 translated blocks of a symmetric 2-design. -/
def blocks : Finset (Finset G) := Finset.univ.image (fun a : G => translate a D)

theorem block_count : blocks.card = 21 := by decide +kernel

theorem translated_block_size : ∀ a : G, (translate a D).card = 5 := by decide +kernel

theorem block_size (B : Finset G) (hB : B ∈ blocks) : B.card = 5 := by
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hB
  exact translated_block_size a

theorem every_pair_in_one_block : ∀ x y : G, x ≠ y →
    (blocks.filter (fun B => x ∈ B ∧ y ∈ B)).card = 1 := by decide +kernel

/-- Every additive map on a cyclic group is multiplication by its value at one. -/
theorem additive_map_formula (f : G →+ G) (x : G) : f x = x * f 1 := by
  have h := map_nsmul f x.val (1 : G)
  simpa only [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one] using h

def unitOfAddAut (f : G ≃+ G) : Gˣ where
  val := f 1
  inv := f.symm 1
  val_inv := by
    have h := additive_map_formula f.toAddMonoidHom (f.symm 1)
    change f (f.symm 1) = f.symm 1 * f 1 at h
    simpa only [AddEquiv.apply_symm_apply, mul_comm] using h.symm
  inv_val := by
    have h := additive_map_formula f.toAddMonoidHom (f.symm 1)
    change f (f.symm 1) = f.symm 1 * f 1 at h
    simpa only [AddEquiv.apply_symm_apply] using h.symm

theorem every_add_aut_is_unit_multiplication (f : G ≃+ G) (x : G) :
    f x = (unitOfAddAut f : G) * x := by
  simpa only [unitOfAddAut, mul_comm] using additive_map_formula f.toAddMonoidHom x

def u2 : Gˣ := ⟨2, 11, by decide, by decide⟩
def u4 : Gˣ := ⟨4, 16, by decide, by decide⟩
def u8 : Gˣ := ⟨8, 8, by decide, by decide⟩
def u16 : Gˣ := ⟨16, 4, by decide, by decide⟩
def u11 : Gˣ := ⟨11, 2, by decide, by decide⟩

def multiplierElements : Finset Gˣ := {1, u2, u4, u8, u16, u11}

def multiplierGroup : Subgroup Gˣ where
  carrier := {u | u ∈ multiplierElements}
  one_mem' := by decide
  mul_mem' := by
    intro a b ha hb
    simp only [multiplierElements, Finset.mem_insert, Finset.mem_singleton] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  inv_mem' := by
    intro a ha
    simp only [multiplierElements, Finset.mem_insert, Finset.mem_singleton] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem group_is_full_multiplier_group (u : Gˣ) :
    u ∈ multiplierGroup ↔ IsMultiplier (u : G) := by
  rw [multiplier_classification]
  change u ∈ multiplierElements ↔ _
  simp only [multiplierElements, Finset.mem_insert, Finset.mem_singleton, Units.ext_iff]
  rfl

theorem all_automorphism_multipliers (f : G ≃+ G) :
    (∃ a : G, D.image f = translate a D) ↔ unitOfAddAut f ∈ multiplierGroup := by
  rw [group_is_full_multiplier_group]
  unfold IsMultiplier
  have hfun : (f : G → G) = fun x => (unitOfAddAut f : G) * x :=
    funext (every_add_aut_is_unit_multiplication f)
  rw [hfun]
  exact (and_iff_right (ZMod.val_coe_unit_coprime (unitOfAddAut f))).symm

instance : Fintype multiplierGroup :=
  Fintype.ofFinset multiplierElements (fun _ => Iff.rfl)

theorem group_order : Fintype.card multiplierGroup = 6 := by decide +kernel

theorem divides_no_parameter :
    ¬ Fintype.card multiplierGroup ∣ 21 ∧
    ¬ Fintype.card multiplierGroup ∣ 5 ∧
    ¬ Fintype.card multiplierGroup ∣ 1 ∧
    ¬ Fintype.card multiplierGroup ∣ (5 - 1) ∧
    ¬ Fintype.card multiplierGroup ∣ (21 * 5 * 1) := by
  rw [group_order]
  decide

theorem counterexample :
    IsDifferenceSet D 21 5 1 ∧
    (∀ u : Gˣ, u ∈ multiplierGroup ↔ IsMultiplier (u : G)) ∧
    Fintype.card multiplierGroup = 6 ∧
    ¬ Fintype.card multiplierGroup ∣ 21 ∧
    ¬ Fintype.card multiplierGroup ∣ 5 ∧
    ¬ Fintype.card multiplierGroup ∣ 1 ∧
    ¬ Fintype.card multiplierGroup ∣ (5 - 1) ∧
    ¬ Fintype.card multiplierGroup ∣ (21 * 5 * 1) :=
  ⟨difference_set, group_is_full_multiplier_group, group_order, divides_no_parameter⟩

end Conjecture6338

#print axioms Conjecture6338.difference_set
#print axioms Conjecture6338.multiplier_classification
#print axioms Conjecture6338.translate_must_be_zero
#print axioms Conjecture6338.group_is_full_multiplier_group
#print axioms Conjecture6338.group_order
#print axioms Conjecture6338.every_pair_in_one_block
#print axioms Conjecture6338.all_automorphism_multipliers
#print axioms Conjecture6338.counterexample
