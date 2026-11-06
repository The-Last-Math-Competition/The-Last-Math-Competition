import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-! The source defines support as a minimum of natural fixed-space dimensions.
On actual SL₂(F₂), this minimum is zero, whereas the proposed n²-1 is three.
No standard codimension/adjoint support invariant is being substituted. -/
namespace TLMC1189
open Matrix Module

abbrev F := ZMod 2
abbrev V := Fin 2 → F
abbrev G := Matrix.SpecialLinearGroup (Fin 2) F

noncomputable def fixed (A : G) : Submodule F V :=
  LinearMap.ker (A.toLin'.toLinearMap - LinearMap.id)

theorem fixed_mem (A : G) (v : V) : v ∈ fixed A ↔ A • v = v := by
  change (A.toLin' v - v = 0) ↔ A • v = v
  rw [sub_eq_zero]
  rfl

noncomputable def commonFixed (A B : G) : Submodule F V := fixed A ⊓ fixed B

theorem commonFixed_mem (A B : G) (v : V) :
    v ∈ commonFixed A B ↔ A • v = v ∧ B • v = v := by
  simp only [commonFixed, Submodule.mem_inf, fixed_mem]

def Generated (A B : G) : Subgroup G := Subgroup.closure {A, B}
def GeneratingPair (A B : G) : Prop := Generated A B = ⊤

noncomputable def imageFixed (H : Subgroup G) : Submodule F V := ⨅ A : H, fixed A.1

theorem imageFixed_mem (H : Subgroup G) (v : V) :
    v ∈ imageFixed H ↔ ∀ A ∈ H, A • v = v := by
  simp only [imageFixed, Submodule.mem_iInf, fixed_mem]
  exact ⟨fun h A hA => h ⟨A, hA⟩, fun h A => h A.1 A.2⟩

theorem commonFixed_eq_generatedImage (A B : G) :
    commonFixed A B = imageFixed (Generated A B) := by
  ext v
  rw [commonFixed_mem, imageFixed_mem]
  constructor
  · rintro ⟨hA, hB⟩
    have h : Generated A B ≤ MulAction.stabilizer G v := by
      apply (Subgroup.closure_le (MulAction.stabilizer G v)).mpr
      intro C hC
      rcases (Set.mem_insert_iff.mp hC) with rfl | hC
      · exact hA
      · have : C = B := Set.mem_singleton_iff.mp hC
        simpa [this] using hB
    exact fun C hC => h hC
  · intro h
    exact ⟨h A (Subgroup.subset_closure (by simp)),
      h B (Subgroup.subset_closure (by simp))⟩

theorem natural_dimension : finrank F V = 2 := by simp [V, F]

theorem commonFixed_dimension_le_two (A B : G) : finrank F (commonFixed A B) ≤ 2 := by
  calc
    finrank F (commonFixed A B) ≤ finrank F V := Submodule.finrank_le _
    _ = 2 := natural_dimension

theorem imageFixed_dimension_le_two (H : Subgroup G) : finrank F (imageFixed H) ≤ 2 := by
  calc
    finrank F (imageFixed H) ≤ finrank F V := Submodule.finrank_le _
    _ = 2 := natural_dimension

def U : G := Matrix.SpecialLinearGroup.transvection
  (show (0 : Fin 2) ≠ 1 by decide) (1 : F)
def L : G := Matrix.SpecialLinearGroup.transvection
  (show (1 : Fin 2) ≠ 0 by decide) (1 : F)

theorem transvection_in_pair_closure (i j : Fin 2) (hij : i ≠ j) (c : F) :
    Matrix.SpecialLinearGroup.transvection hij c ∈ Generated U L := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · fin_cases c
    · change Matrix.SpecialLinearGroup.transvection hij (0 : F) ∈ Generated U L
      simpa only [Matrix.SpecialLinearGroup.transvection_coeff_zero] using
        Subgroup.one_mem (Generated U L)
    · change U ∈ Generated U L
      exact Subgroup.subset_closure (by simp)
  · fin_cases c
    · change Matrix.SpecialLinearGroup.transvection hij (0 : F) ∈ Generated U L
      simpa only [Matrix.SpecialLinearGroup.transvection_coeff_zero] using
        Subgroup.one_mem (Generated U L)
    · change L ∈ Generated U L
      exact Subgroup.subset_closure (by simp)
  · exact (hij rfl).elim

theorem actual_generating_pair : GeneratingPair U L := by
  apply top_unique
  intro A _
  exact Matrix.SL2.transvection_induction
    (fun A => A ∈ Generated U L) transvection_in_pair_closure
    (fun A B hA hB => Subgroup.mul_mem _ hA hB) A

theorem U_fixed_coordinate (v : V) : U • v = v ↔ v 1 = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    simpa [U, Matrix.SpecialLinearGroup.smul_def, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0
  · intro h
    ext i
    fin_cases i <;>
      simp [U, Matrix.SpecialLinearGroup.smul_def, Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two, h]

theorem L_fixed_coordinate (v : V) : L • v = v ↔ v 0 = 0 := by
  constructor
  · intro h
    have h1 := congrFun h 1
    simpa [L, Matrix.SpecialLinearGroup.smul_def, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h1
  · intro h
    ext i
    fin_cases i <;>
      simp [L, Matrix.SpecialLinearGroup.smul_def, Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two, h]

theorem U_fixed_dimension_le_one : finrank F (fixed U) ≤ 1 := by
  have hne : fixed U ≠ ⊤ := by
    intro h
    have hv : (Pi.single (1 : Fin 2) (1 : F) : V) ∈ fixed U := by
      rw [h]
      exact Submodule.mem_top
    have hz := (U_fixed_coordinate _).mp ((fixed_mem U _).mp hv)
    norm_num at hz
  have h := Submodule.finrank_lt hne
  rw [natural_dimension] at h
  exact Nat.le_of_lt_succ h

theorem L_fixed_dimension_le_one : finrank F (fixed L) ≤ 1 := by
  have hne : fixed L ≠ ⊤ := by
    intro h
    have hv : (Pi.single (0 : Fin 2) (1 : F) : V) ∈ fixed L := by
      rw [h]
      exact Submodule.mem_top
    have hz := (L_fixed_coordinate _).mp ((fixed_mem L _).mp hv)
    norm_num at hz
  have h := Submodule.finrank_lt hne
  rw [natural_dimension] at h
  exact Nat.le_of_lt_succ h

theorem commonFixed_U_L_eq_bot : commonFixed U L = ⊥ := by
  apply le_antisymm
  · intro v hv
    rw [Submodule.mem_bot]
    obtain ⟨hU, hL⟩ := (commonFixed_mem U L v).mp hv
    have h1 := (U_fixed_coordinate v).mp hU
    have h0 := (L_fixed_coordinate v).mp hL
    ext i
    fin_cases i <;> assumption
  · exact bot_le

theorem actual_zero_fixed_dimension : finrank F (commonFixed U L) = 0 := by
  simp [commonFixed_U_L_eq_bot]

theorem actual_pair_satisfies_fixed_conditions :
    GeneratingPair U L ∧ finrank F (commonFixed U L) = 0 ∧
    finrank F (fixed U) ≤ 1 ∧ finrank F (fixed L) ≤ 1 :=
  ⟨actual_generating_pair, actual_zero_fixed_dimension,
    U_fixed_dimension_le_one, L_fixed_dimension_le_one⟩

theorem full_image_fixed_eq_bot : imageFixed (⊤ : Subgroup G) = ⊥ := by
  rw [← actual_generating_pair, ← commonFixed_eq_generatedImage]
  exact commonFixed_U_L_eq_bot

def SupportValues : Set ℕ :=
  {d | ∃ A B : G, GeneratingPair A B ∧ finrank F (commonFixed A B) = d}

theorem zero_in_actual_support_values : 0 ∈ SupportValues :=
  ⟨U, L, actual_generating_pair, actual_zero_fixed_dimension⟩

theorem actual_support_values_nonempty : SupportValues.Nonempty :=
  ⟨0, zero_in_actual_support_values⟩

theorem least_actual_support_zero : IsLeast SupportValues 0 :=
  ⟨zero_in_actual_support_values, fun _ _ => Nat.zero_le _⟩

noncomputable def minimumSupport : ℕ := sInf SupportValues

theorem minimumSupport_eq_zero : minimumSupport = 0 := least_actual_support_zero.csInf_eq

theorem support_formula_false : minimumSupport ≠ (2 : ℕ)^2 - 1 := by
  rw [minimumSupport_eq_zero]
  decide

/-- Every nonempty choice of natural image fixed-space dimensions has minimum at most two. -/
theorem any_image_minimum_le_two (S : Set (Subgroup G)) (hS : S.Nonempty) :
    sInf ((fun H => finrank F (imageFixed H)) '' S) ≤ 2 := by
  obtain ⟨H, hH⟩ := hS
  have hmin : sInf ((fun H => finrank F (imageFixed H)) '' S) ≤
      finrank F (imageFixed H) := csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ ⟨H, hH, rfl⟩
  exact hmin.trans (imageFixed_dimension_le_two H)

theorem printed_necessary_conjunction_false :
    ¬ ((∃ A B : G, GeneratingPair A B ∧ finrank F (commonFixed A B) = 0 ∧
        finrank F (fixed A) ≤ 1 ∧ finrank F (fixed B) ≤ 1) ∧
      minimumSupport = (2 : ℕ)^2 - 1) := by
  rintro ⟨_, h⟩
  exact support_formula_false h

end TLMC1189
