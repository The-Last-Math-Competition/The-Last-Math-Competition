import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

noncomputable section

namespace Involution5838

abbrev G := Multiplicative (ZMod 2)

def involution : G := Multiplicative.ofAdd 1

theorem involution_ne_one : involution ≠ 1 := by decide

theorem involution_square : involution * involution = 1 := by decide

theorem group_card : Nat.card G = 2 := by
  rw [Nat.card_congr (Multiplicative.toAdd : G ≃ ZMod 2)]
  simp

def centralizer : Subgroup G := Subgroup.centralizer {involution}

theorem centralizer_eq_top : centralizer = ⊤ := by
  apply le_antisymm le_top
  intro g _
  exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_comm g involution)

def centralizerEquiv : centralizer ≃* G where
  toFun := Subtype.val
  invFun g := ⟨g, by rw [centralizer_eq_top]; exact Subgroup.mem_top g⟩
  left_inv g := Subtype.ext rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem centralizer_card : Nat.card centralizer = 2 := by
  rw [Nat.card_congr centralizerEquiv.toEquiv, group_card]

def centralizerAlgebraEquiv (K : Type*) [CommSemiring K] :
    MonoidAlgebra K centralizer ≃ₐ[K] MonoidAlgebra K G :=
  MonoidAlgebra.domCongr K K centralizerEquiv

end Involution5838
