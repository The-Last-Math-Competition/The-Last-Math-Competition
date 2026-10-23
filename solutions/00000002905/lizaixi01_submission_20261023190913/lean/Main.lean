import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Matrix Set Function
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace TLMC2905

instance prime_five : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev F := ZMod 5
abbrev V := Fin 2 → F
abbrev G := DihedralGroup 3

def r : G := DihedralGroup.r 1
def s : G := DihedralGroup.sr 0

def R : Matrix (Fin 2) (Fin 2) F := !![0, -1; 1, -1]
def S : Matrix (Fin 2) (Fin 2) F := !![0, 1; 1, 0]

def rotation (i : ZMod 3) : Matrix (Fin 2) (Fin 2) F := R ^ i.val

def matrix : G → Matrix (Fin 2) (Fin 2) F
  | .r i => rotation i
  | .sr i => S * rotation i

theorem matrix_mul_table : ∀ g h : G, matrix (g * h) = matrix g * matrix h := by
  decide

def matrixHom : G →* Matrix (Fin 2) (Fin 2) F where
  toFun := matrix
  map_one' := by decide
  map_mul' := matrix_mul_table

def matrixUnits : G →* Matrix.GeneralLinearGroup (Fin 2) F :=
  MonoidHom.toHomUnits matrixHom

theorem matrix_injective : Injective matrix := by decide

theorem matrixUnits_injective : Injective matrixUnits := by
  intro g h heq
  apply matrix_injective
  exact congrArg Units.val heq

def representation : Representation F G V :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin 2) (Fin 2) F ≃ₐ[F] Module.End F V).toMonoidHom.comp
    matrixHom

theorem representation_apply (g : G) (v : V) :
    representation g v = matrix g *ᵥ v := rfl

instance vectorAction : MulAction G V where
  smul g v := representation g v
  one_smul v := by
    change representation 1 v = v
    rw [representation.map_one]
    rfl
  mul_smul g h v := by
    change representation (g * h) v = representation g (representation h v)
    rw [representation.map_mul]
    rfl

theorem action_eq_matrix (g : G) (v : V) : g • v = matrix g *ᵥ v := rfl

theorem matrix_r : matrix r = R := by decide
theorem matrix_s : matrix s = S := by decide

theorem rotation_determinant : Matrix.det (matrix r) = 1 := by decide
theorem reflection_determinant : Matrix.det (matrix s) = -1 := by decide

theorem actual_group_card : Nat.card G = 6 := by
  rw [DihedralGroup.nat_card]

theorem nonmodular : ¬ 5 ∣ Nat.card G := by
  rw [actual_group_card]
  decide

theorem image_group_card : Nat.card matrixUnits.range = 6 := by
  have e : G ≃ matrixUnits.range := Equiv.ofInjective matrixUnits matrixUnits_injective
  rw [← Nat.card_congr e, actual_group_card]

theorem actual_generators : Subgroup.closure ({r, s} : Set G) = ⊤ := by
  apply top_unique
  intro g _
  have hr : r ∈ Subgroup.closure ({r, s} : Set G) := Subgroup.subset_closure (by simp)
  have hs : s ∈ Subgroup.closure ({r, s} : Set G) := Subgroup.subset_closure (by simp)
  cases g with
  | r i =>
    have hp := (Subgroup.closure ({r, s} : Set G)).pow_mem hr i.val
    simpa [r, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val] using hp
  | sr i =>
    have hp := (Subgroup.closure ({r, s} : Set G)).pow_mem hr i.val
    have hm := (Subgroup.closure ({r, s} : Set G)).mul_mem hs hp
    simpa [r, s, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val] using hm

theorem image_generators :
    Subgroup.closure ({matrixUnits r, matrixUnits s} : Set (Matrix.GeneralLinearGroup (Fin 2) F)) =
      matrixUnits.range := by
  have himg : matrixUnits '' ({r, s} : Set G) = {matrixUnits r, matrixUnits s} := by
    ext x
    simp [eq_comm]
  rw [MonoidHom.range_eq_map, ← actual_generators, MonoidHom.map_closure, himg]

theorem generator_order : orderOf s = 2 := DihedralGroup.orderOf_sr 0

theorem matrix_generator_order : orderOf (matrixUnits s) = 2 := by
  rw [orderOf_injective matrixUnits matrixUnits_injective]
  exact generator_order

def determinant (v : V) : F := v 0 * (v 0 - v 1) + v 1 * v 1

theorem quadratic_anisotropic : ∀ x y : F, x * (x - y) + y * y = 0 → x = 0 ∧ y = 0 := by
  decide

theorem determinant_ne_zero (v : V) (hv : v ≠ 0) : determinant v ≠ 0 := by
  intro h
  obtain ⟨h0, h1⟩ := quadratic_anisotropic (v 0) (v 1) h
  apply hv
  ext i
  fin_cases i <;> assumption

theorem spanning_formula (v w : V) (hv : v ≠ 0) :
    (((v 0 - v 1) * w 0 + v 1 * w 1) / determinant v) • v +
      ((-v 1 * w 0 + v 0 * w 1) / determinant v) • representation r v = w := by
  have hd := determinant_ne_zero v hv
  rw [representation_apply, matrix_r]
  ext i
  fin_cases i <;>
    simp [R, Matrix.vecHead, Matrix.vecTail] <;>
    field_simp [hd] <;> simp only [determinant] <;> ring

theorem subrepresentation_bot_or_top (W : Subrepresentation representation) : W = ⊥ ∨ W = ⊤ := by
  by_cases hb : W = ⊥
  · exact Or.inl hb
  right
  have hn : W.toSubmodule ≠ ⊥ := by
    intro h
    apply hb
    exact Subrepresentation.toSubmodule_injective h
  obtain ⟨v, hv, hv0⟩ := W.toSubmodule.ne_bot_iff.mp hn
  have hr : representation r v ∈ W.toSubmodule := W.apply_mem_toSubmodule r hv
  apply top_unique
  intro w _
  have hm := W.toSubmodule.add_mem
    (W.toSubmodule.smul_mem (((v 0 - v 1) * w 0 + v 1 * w 1) / determinant v) hv)
    (W.toSubmodule.smul_mem ((-v 1 * w 0 + v 0 * w 1) / determinant v) hr)
  rwa [spanning_formula v w hv0] at hm

theorem representation_irreducible : Representation.IsIrreducible representation := by
  refine { exists_pair_ne := ?_, eq_bot_or_eq_top := subrepresentation_bot_or_top }
  refine ⟨⊥, ⊤, ?_⟩
  intro h
  have h' : (⊥ : Submodule F V) = ⊤ := congrArg Subrepresentation.toSubmodule h
  have hx : (fun _ : Fin 2 => (1 : F)) ∈ (⊥ : Submodule F V) := by
    rw [h']
    exact Submodule.mem_top
  have hx0 : (fun _ : Fin 2 => (1 : F)) = 0 := by simpa using hx
  have hz := congrFun hx0 0
  norm_num at hz

def v : V := ![1, 1]
def v1 : V := ![4, 0]
def v2 : V := ![0, 4]

theorem vector_nonzero : v ≠ 0 := by decide

theorem reflection_fixes : s • v = v := by decide

theorem full_orbit : MulAction.orbit G v = {v, v1, v2} := by
  ext w
  rw [MulAction.mem_orbit_iff]
  change (∃ g : G, representation g v = w) ↔ w = v ∨ w = v1 ∨ w = v2
  have h : ∀ w : V, (∃ g : G, representation g v = w) ↔ w = v ∨ w = v1 ∨ w = v2 := by
    decide
  exact h w

theorem full_orbit_finite : (MulAction.orbit G v).Finite := Set.toFinite _

theorem full_orbit_card : (MulAction.orbit G v).ncard = 3 := by
  rw [full_orbit]
  have h0 : v ∉ ({v1, v2} : Set V) := by decide
  have h1 : v1 ≠ v2 := by decide
  rw [Set.ncard_insert_of_notMem h0, Set.ncard_pair h1]

theorem cyclic_orbit : MulAction.orbit (Subgroup.zpowers s) v = {v} := by
  have hs : s ∈ MulAction.stabilizer G v := reflection_fixes
  have hle : Subgroup.zpowers s ≤ MulAction.stabilizer G v := Subgroup.zpowers_le.mpr hs
  ext w
  rw [MulAction.mem_orbit_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact hle g.property
  · rintro rfl
    exact ⟨1, one_smul _ _⟩

theorem cyclic_orbit_finite : (MulAction.orbit (Subgroup.zpowers s) v).Finite := Set.toFinite _

theorem cyclic_orbit_card : (MulAction.orbit (Subgroup.zpowers s) v).ncard = 1 := by
  rw [cyclic_orbit, Set.ncard_singleton]

theorem generator_prime_divisor : Nat.Prime 2 ∧ 2 ∣ orderOf (matrixUnits s) := by
  rw [matrix_generator_order]
  exact ⟨by decide, dvd_refl _⟩

theorem not_divides_cyclic_orbit : ¬ 2 ∣ (MulAction.orbit (Subgroup.zpowers s) v).ncard := by
  rw [cyclic_orbit_card]
  decide

theorem not_divides_group_orbit : ¬ 2 ∣ (MulAction.orbit G v).ncard := by
  rw [full_orbit_card]
  decide

theorem generator_orbit_divisibility_fails :
    ¬ (∀ (g : G) (w : V), w ≠ 0 → ∀ p : ℕ, Nat.Prime p →
      p ∣ orderOf (matrixUnits g) → p ∣ (MulAction.orbit (Subgroup.zpowers g) w).ncard) := by
  intro h
  exact not_divides_cyclic_orbit (h s v vector_nonzero 2 generator_prime_divisor.1
    generator_prime_divisor.2)

theorem whole_group_orbit_divisibility_fails :
    ¬ (∀ (g : G) (w : V), w ≠ 0 → ∀ p : ℕ, Nat.Prime p →
      p ∣ orderOf (matrixUnits g) → p ∣ (MulAction.orbit G w).ncard) := by
  intro h
  exact not_divides_group_orbit (h s v vector_nonzero 2 generator_prime_divisor.1
    generator_prime_divisor.2)

theorem counterexample :
    Representation.IsIrreducible representation ∧
    Subgroup.closure ({r, s} : Set G) = ⊤ ∧
    Injective matrixUnits ∧ ¬ 5 ∣ Nat.card G ∧ v ≠ 0 ∧
    orderOf (matrixUnits s) = 2 ∧
    ¬ 2 ∣ (MulAction.orbit (Subgroup.zpowers s) v).ncard ∧
    ¬ 2 ∣ (MulAction.orbit G v).ncard :=
  ⟨representation_irreducible, actual_generators, matrixUnits_injective, nonmodular,
    vector_nonzero, matrix_generator_order, not_divides_cyclic_orbit, not_divides_group_orbit⟩

end TLMC2905
