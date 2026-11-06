import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.RepresentationTheory.Character
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-
The literal real-character sufficiency and pairwise exclusion in problem 25
cannot both hold. Every field, character, representation and L-function below
is an actual native mathematical object; no zero of an L-function is assumed.
-/

set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace TLMC25

open NumberField

abbrev K := CyclotomicField 8 ℚ
abbrev G := K ≃ₐ[ℚ] K
abbrev U := (ZMod 8)ˣ

instance prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩
instance eight_nonzero_rat : NeZero (8 : ℚ) := ⟨by norm_num⟩

noncomputable instance cyclotomic_eight : IsCyclotomicExtension {8} ℚ K :=
  CyclotomicField.isCyclotomicExtension (n := 8) (K := ℚ)

noncomputable def galEquiv : G ≃* U :=
  IsCyclotomicExtension.autEquivPow K (Polynomial.cyclotomic.irreducible_rat (by decide))

theorem extension_galois : IsGalois ℚ K :=
  IsCyclotomicExtension.isGalois {8} ℚ K

theorem extension_degree : Module.finrank ℚ K = 4 := by
  simpa [show Nat.totient 8 = 4 by decide] using IsCyclotomicExtension.finrank K
    (Polynomial.cyclotomic.irreducible_rat (by decide : 0 < 8))

theorem actual_discriminant : NumberField.discr K = 256 := by
  have h := IsCyclotomicExtension.Rat.discr_prime_pow 2 3 K
  norm_num at h
  exact h

noncomputable def absoluteDiscriminant : ℝ := |(NumberField.discr K : ℝ)|

theorem absoluteDiscriminant_eq : absoluteDiscriminant = 256 := by
  norm_num [absoluteDiscriminant, actual_discriminant]

theorem absoluteDiscriminant_gt_one : 1 < absoluteDiscriminant := by
  rw [absoluteDiscriminant_eq]
  norm_num

def u3 : U := ⟨3, 3, by decide, by decide⟩
def u5 : U := ⟨5, 5, by decide, by decide⟩
def u7 : U := ⟨7, 7, by decide, by decide⟩

@[simp] theorem val1 : (1 : ZMod 8).val = 1 := rfl
@[simp] theorem val3 : (3 : ZMod 8).val = 3 := rfl
@[simp] theorem val5 : (5 : ZMod 8).val = 5 := rfl
@[simp] theorem val7 : (7 : ZMod 8).val = 7 := rfl
@[simp] theorem val9 : (9 : ZMod 8).val = 1 := rfl
@[simp] theorem val15 : (15 : ZMod 8).val = 7 := rfl
@[simp] theorem val21 : (21 : ZMod 8).val = 5 := rfl
@[simp] theorem val25 : (25 : ZMod 8).val = 1 := rfl
@[simp] theorem val35 : (35 : ZMod 8).val = 3 := rfl
@[simp] theorem val49 : (49 : ZMod 8).val = 1 := rfl

theorem unit_cases (u : U) : u = 1 ∨ u = u3 ∨ u = u5 ∨ u = u7 := by
  revert u
  decide

def unitCharacterA : U →* ℂˣ where
  toFun u := if (u : ZMod 8).val = 1 ∨ (u : ZMod 8).val = 7 then 1 else -1
  map_one' := by norm_num
  map_mul' := by
    intro u v
    rcases unit_cases u with rfl | rfl | rfl | rfl <;>
      rcases unit_cases v with rfl | rfl | rfl | rfl <;>
      norm_num [u3, u5, u7, ZMod.val_natCast]

def unitCharacterB : U →* ℂˣ where
  toFun u := if (u : ZMod 8).val = 1 ∨ (u : ZMod 8).val = 3 then 1 else -1
  map_one' := by norm_num
  map_mul' := by
    intro u v
    rcases unit_cases u with rfl | rfl | rfl | rfl <;>
      rcases unit_cases v with rfl | rfl | rfl | rfl <;>
      norm_num [u3, u5, u7, ZMod.val_natCast]

noncomputable def chiA : DirichletCharacter ℂ 8 := MulChar.ofUnitHom unitCharacterA
noncomputable def chiB : DirichletCharacter ℂ 8 := MulChar.ofUnitHom unitCharacterB

theorem chiA_at_three : chiA (3 : ZMod 8) = -1 := by
  change chiA (u3 : ZMod 8) = -1
  rw [chiA, MulChar.ofUnitHom_coe]
  norm_num [unitCharacterA, u3, ZMod.val_natCast]

theorem chiB_at_three : chiB (3 : ZMod 8) = 1 := by
  change chiB (u3 : ZMod 8) = 1
  rw [chiB, MulChar.ofUnitHom_coe]
  norm_num [unitCharacterB, u3, ZMod.val_natCast]

theorem chiA_at_five : chiA (5 : ZMod 8) = -1 := by
  change chiA (u5 : ZMod 8) = -1
  rw [chiA, MulChar.ofUnitHom_coe]
  norm_num [unitCharacterA, u5, ZMod.val_natCast]

theorem chiB_at_five : chiB (5 : ZMod 8) = -1 := by
  change chiB (u5 : ZMod 8) = -1
  rw [chiB, MulChar.ofUnitHom_coe]
  norm_num [unitCharacterB, u5, ZMod.val_natCast]

theorem chiA_at_seven : chiA (7 : ZMod 8) = 1 := by
  change chiA (u7 : ZMod 8) = 1
  rw [chiA, MulChar.ofUnitHom_coe]
  norm_num [unitCharacterA, u7]

theorem chiB_at_seven : chiB (7 : ZMod 8) = -1 := by
  change chiB (u7 : ZMod 8) = -1
  rw [chiB, MulChar.ofUnitHom_coe]
  norm_num [unitCharacterB, u7]

theorem characters_distinct : chiA ≠ chiB := by
  intro h
  have h3 := congrArg (fun χ : DirichletCharacter ℂ 8 => χ 3) h
  rw [chiA_at_three, chiB_at_three] at h3
  norm_num at h3

theorem primitive_of_at_five (χ : DirichletCharacter ℂ 8)
    (h5 : χ (5 : ZMod 8) = -1) : χ.IsPrimitive := by
  have hn4 : ¬ χ.FactorsThrough 4 := by
    intro hf
    have h := DirichletCharacter.changeLevel_eq_cast_of_dvd hf.χ₀ hf.dvd u5
    rw [← hf.eq_changeLevel] at h
    have h1 : χ (5 : ZMod 8) = 1 := by
      simp only [u5, Units.val_mk] at h
      rw [show (ZMod.cast (5 : ZMod 8) : ZMod 4) = 1 by decide, map_one] at h
      exact h
    rw [h5] at h1
    norm_num at h1
  have hd := χ.conductor_dvd_level
  have hc := χ.factorsThrough_conductor
  have divisor_cases : ∀ d : ℕ, d ∣ 8 → d = 1 ∨ d = 2 ∨ d = 4 ∨ d = 8 := by
    intro d hd
    have hle : d ≤ 8 := Nat.le_of_dvd (by decide) hd
    interval_cases d <;> (try norm_num at hd) <;> omega
  rcases divisor_cases χ.conductor hd with h | h | h | h
  · exact False.elim (hn4 (DirichletCharacter.FactorsThrough.mono χ hc
      (by rw [h]; decide) (by decide)))
  · exact False.elim (hn4 (DirichletCharacter.FactorsThrough.mono χ hc
      (by rw [h]; decide) (by decide)))
  · exact False.elim (hn4 (h ▸ hc))
  · exact h

theorem chiA_primitive : chiA.IsPrimitive := primitive_of_at_five chiA chiA_at_five
theorem chiB_primitive : chiB.IsPrimitive := primitive_of_at_five chiB chiB_at_five

theorem chiA_nontrivial : chiA ≠ 1 := by
  intro h
  have h5 := chiA_at_five
  rw [h] at h5
  have h1 : (1 : DirichletCharacter ℂ 8) (5 : ZMod 8) = 1 :=
    MulChar.one_apply (show IsUnit (5 : ZMod 8) from u5.isUnit)
  rw [h1] at h5
  norm_num at h5

theorem chiB_nontrivial : chiB ≠ 1 := by
  intro h
  have h5 := chiB_at_five
  rw [h] at h5
  have h1 : (1 : DirichletCharacter ℂ 8) (5 : ZMod 8) = 1 :=
    MulChar.one_apply (show IsUnit (5 : ZMod 8) from u5.isUnit)
  rw [h1] at h5
  norm_num at h5

noncomputable def galoisScalar (χ : DirichletCharacter ℂ 8) : G →* ℂ :=
  (Units.coeHom ℂ).comp (χ.toUnitHom.comp galEquiv.toMonoidHom)

noncomputable def scalarRepresentation (h : G →* ℂ) : Representation ℂ G ℂ where
  toFun g := h g • LinearMap.id
  map_one' := by ext; simp
  map_mul' := by intro g h'; ext; simp [mul_smul, mul_comm]

noncomputable def galoisRepresentation (χ : DirichletCharacter ℂ 8) : Representation ℂ G ℂ :=
  scalarRepresentation (galoisScalar χ)

theorem galois_character (χ : DirichletCharacter ℂ 8) (g : G) :
    (galoisRepresentation χ).character g = χ (galEquiv g : ZMod 8) := by
  simp [galoisRepresentation, scalarRepresentation, Representation.character,
    galoisScalar]

theorem line_irreducible (ρ : Representation ℂ G ℂ) : Representation.IsIrreducible ρ := by
  refine { exists_pair_ne := ?_, eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, ?_⟩
    intro heq
    have h' : (⊥ : Submodule ℂ ℂ) = ⊤ := congrArg Subrepresentation.toSubmodule heq
    have h1 : (1 : ℂ) ∈ (⊥ : Submodule ℂ ℂ) := by rw [h']; trivial
    simp at h1
  · intro S
    rcases eq_bot_or_eq_top S.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)

theorem chiA_irreducible : Representation.IsIrreducible (galoisRepresentation chiA) :=
  line_irreducible _

theorem chiB_irreducible : Representation.IsIrreducible (galoisRepresentation chiB) :=
  line_irreducible _

noncomputable instance galFintype : Fintype G := Fintype.ofEquiv U galEquiv.symm.toEquiv

theorem univ_units : (Finset.univ : Finset U) = {1, u3, u5, u7} := by
  classical
  ext u
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact unit_cases u

theorem galois_card : Fintype.card G = 4 := by
  calc
    Fintype.card G = Fintype.card U := Fintype.card_congr galEquiv.toEquiv
    _ = 4 := by rw [← Finset.card_univ, univ_units]; decide

theorem galois_representation_apply (χ : DirichletCharacter ℂ 8) (u : U) (z : ℂ) :
    galoisRepresentation χ (galEquiv.symm u) z = χ (u : ZMod 8) * z := by
  simp [galoisRepresentation, scalarRepresentation, galoisScalar]

theorem galois_characters_distinct :
    (galoisRepresentation chiA).character ≠ (galoisRepresentation chiB).character := by
  intro h
  have hh := congrFun h (galEquiv.symm u3)
  simp only [galois_character, galEquiv.apply_symm_apply] at hh
  change chiA (3 : ZMod 8) = chiB (3 : ZMod 8) at hh
  rw [chiA_at_three, chiB_at_three] at hh
  norm_num at hh

theorem representations_inequivalent :
    ¬ Nonempty (Representation.Equiv (galoisRepresentation chiA) (galoisRepresentation chiB)) := by
  rintro ⟨e⟩
  exact galois_characters_distinct (Representation.char_iso e)

theorem no_intertwiner
    (f : Representation.IntertwiningMap (galoisRepresentation chiA) (galoisRepresentation chiB)) :
    f = 0 := by
  apply Representation.IntertwiningMap.toLinearMap_injective _ _
  apply LinearMap.ext
  intro z
  change f z = 0
  have hh := Representation.IntertwiningMap.isIntertwining _ _ f (galEquiv.symm u3) z
  rw [galois_representation_apply, galois_representation_apply] at hh
  change f (chiA (3 : ZMod 8) * z) = chiB (3 : ZMod 8) * f z at hh
  rw [chiA_at_three, chiB_at_three, neg_one_mul, one_mul, map_neg] at hh
  linear_combination -(1 / 2 : ℂ) * hh

theorem invariants_zero_of_at_five (χ : DirichletCharacter ℂ 8)
    (h5 : χ (5 : ZMod 8) = -1) : (galoisRepresentation χ).invariants = ⊥ := by
  apply bot_unique
  intro z hz
  have hh := (Representation.mem_invariants _ _).mp hz (galEquiv.symm u5)
  rw [galois_representation_apply] at hh
  change χ (5 : ZMod 8) * z = z at hh
  rw [h5, neg_one_mul] at hh
  have hz0 : z = 0 := by linear_combination -(1 / 2 : ℂ) * hh
  simpa using hz0

theorem chiA_invariants_zero : (galoisRepresentation chiA).invariants = ⊥ :=
  invariants_zero_of_at_five chiA chiA_at_five

theorem chiB_invariants_zero : (galoisRepresentation chiB).invariants = ⊥ :=
  invariants_zero_of_at_five chiB chiB_at_five

def RealCharacter (χ : DirichletCharacter ℂ 8) : Prop :=
  ∀ g : G, ((galoisRepresentation χ).character g).im = 0

theorem chiA_real : RealCharacter chiA := by
  intro g
  rw [galois_character, chiA, MulChar.ofUnitHom_coe]
  rcases unit_cases (galEquiv g) with h | h | h | h <;>
    rw [h] <;> norm_num [unitCharacterA, u3, u5, u7]

theorem chiB_real : RealCharacter chiB := by
  intro g
  rw [galois_character, chiB, MulChar.ofUnitHom_coe]
  rcases unit_cases (galEquiv g) with h | h | h | h <;>
    rw [h] <;> norm_num [unitCharacterB, u3, u5, u7]

noncomputable def characterInner (χ ψ : DirichletCharacter ℂ 8) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ *
    ∑ g : G, (galoisRepresentation χ).character g *
      star ((galoisRepresentation ψ).character g)

theorem characters_orthogonal : characterInner chiA chiB = 0 := by
  classical
  have hs : (∑ g : G, (galoisRepresentation chiA).character g *
      star ((galoisRepresentation chiB).character g)) =
      ∑ u : U, chiA (u : ZMod 8) * star (chiB (u : ZMod 8)) := by
    apply Fintype.sum_equiv galEquiv.toEquiv
    intro g
    simp only [galois_character]
    rfl
  have hn1 : (1 : U) ∉ ({u3, u5, u7} : Finset U) := by decide
  have hn3 : u3 ∉ ({u5, u7} : Finset U) := by decide
  have hn5 : u5 ∉ ({u7} : Finset U) := by decide
  rw [characterInner, hs, univ_units, Finset.sum_insert hn1, Finset.sum_insert hn3,
    Finset.sum_insert hn5, Finset.sum_singleton]
  norm_num [u3, u5, u7, chiA_at_three, chiB_at_three, chiA_at_five,
    chiB_at_five, chiA_at_seven, chiB_at_seven]

theorem chiA_at_two : chiA (2 : ZMod 8) = 0 := by
  simp [chiA, MulChar.ofUnitHom, show ¬ IsUnit (2 : ZMod 8) by decide]

theorem chiB_at_two : chiB (2 : ZMod 8) = 0 := by
  simp [chiB, MulChar.ofUnitHom, show ¬ IsUnit (2 : ZMod 8) by decide]

noncomputable def dirichletEulerFactor (χ : DirichletCharacter ℂ 8) (p : ℕ) (s : ℂ) : ℂ :=
  (1 - χ (p : ZMod 8) * (p : ℂ) ^ (-s))⁻¹

theorem chiA_eulerFactor_two (s : ℂ) : dirichletEulerFactor chiA 2 s = 1 := by
  simp [dirichletEulerFactor, chiA_at_two]

theorem chiB_eulerFactor_two (s : ℂ) : dirichletEulerFactor chiB 2 s = 1 := by
  simp [dirichletEulerFactor, chiB_at_two]

def twoPrime : Ideal ℤ := Ideal.span {(2 : ℤ)}

instance twoPrime_maximal : twoPrime.IsMaximal := Int.ideal_span_isMaximal_of_prime 2

noncomputable def ramifiedPrime : Ideal (𝓞 K) :=
  Ideal.span {(IsCyclotomicExtension.zeta_spec 8 ℚ K).toInteger - 1}

noncomputable instance ramifiedPrime_prime : ramifiedPrime.IsPrime :=
  IsCyclotomicExtension.Rat.isPrime_span_zeta_sub_one 2 2
    (IsCyclotomicExtension.zeta_spec 8 ℚ K)

noncomputable instance ramifiedPrime_over_two : ramifiedPrime.LiesOver twoPrime :=
  IsCyclotomicExtension.Rat.liesOver_span_zeta_sub_one 2 2
    (IsCyclotomicExtension.zeta_spec 8 ℚ K)

theorem ramification_index_two : twoPrime.ramificationIdxIn (𝓞 K) = 4 := by
  have h := IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_prime_pow 2 2 K
  norm_num at h
  exact h

theorem actual_inertia_two : ramifiedPrime.inertia G = ⊤ := by
  let : IsGalois ℚ K := extension_galois
  let := IsGaloisGroup.of_isFractionRing G ℤ (𝓞 K) ℚ K
  apply Subgroup.eq_top_of_card_eq
  rw [Ideal.card_inertia_eq_ramificationIdxIn twoPrime ramifiedPrime,
    ramification_index_two, Nat.card_eq_fintype_card, galois_card]

noncomputable def inertiaRepresentation (χ : DirichletCharacter ℂ 8) :
    Representation ℂ (ramifiedPrime.inertia G) ℂ :=
  (galoisRepresentation χ).comp (ramifiedPrime.inertia G).subtype

theorem inertia_invariants_zero (χ : DirichletCharacter ℂ 8)
    (h5 : χ (5 : ZMod 8) = -1) : (inertiaRepresentation χ).invariants = ⊥ := by
  apply bot_unique
  intro z hz
  have hg : galEquiv.symm u5 ∈ ramifiedPrime.inertia G := by rw [actual_inertia_two]; trivial
  have hh := (Representation.mem_invariants _ _).mp hz ⟨galEquiv.symm u5, hg⟩
  change galoisRepresentation χ (galEquiv.symm u5) z = z at hh
  rw [galois_representation_apply] at hh
  change χ (5 : ZMod 8) * z = z at hh
  rw [h5, neg_one_mul] at hh
  have hz0 : z = 0 := by linear_combination -(1 / 2 : ℂ) * hh
  simpa using hz0

theorem inertia_fixed_det_one (χ : DirichletCharacter ℂ 8)
    (h5 : χ (5 : ZMod 8) = -1)
    (T : Module.End ℂ (inertiaRepresentation χ).invariants) : LinearMap.det T = 1 := by
  have : Subsingleton (inertiaRepresentation χ).invariants := by
    rw [inertia_invariants_zero χ h5]
    infer_instance
  exact LinearMap.det_eq_one_of_subsingleton _

theorem full_eulerFactor_two (χ : DirichletCharacter ℂ 8)
    (h5 : χ (5 : ZMod 8) = -1) (s : ℂ)
    (Frob : Module.End ℂ (inertiaRepresentation χ).invariants) :
    (LinearMap.det (1 - (2 : ℂ) ^ (-s) • Frob))⁻¹ = 1 := by
  rw [inertia_fixed_det_one χ h5]
  simp

/-- This is the actual real zero condition for a function, not a label for an
exceptional character or an assigned set of zeros. -/
def WindowZero (F : DirichletCharacter ℂ 8 → ℂ → ℂ) (c D : ℝ)
    (χ : DirichletCharacter ℂ 8) : Prop :=
  ∃ β : ℝ, β ∈ Set.Ioo (1 - c / Real.log D) 1 ∧ F χ (β : ℂ) = 0

/-- Restriction of the printed per-character iff to genuine nonprincipal
primitive conductor-eight characters of this one Galois extension. -/
def PrintedRealIff (F : DirichletCharacter ℂ 8 → ℂ → ℂ) (c D : ℝ) : Prop :=
  ∀ χ : DirichletCharacter ℂ 8, χ.IsPrimitive → χ ≠ 1 →
    (WindowZero F c D χ ↔ RealCharacter χ)

/-- Restriction of the printed pairwise exclusion to actual irreducible,
orthogonal rank-one Galois characters. Both functions use the same window. -/
def PrintedExclusion (F : DirichletCharacter ℂ 8 → ℂ → ℂ) (c D : ℝ) : Prop :=
  ∀ χ ψ : DirichletCharacter ℂ 8, χ.IsPrimitive → ψ.IsPrimitive → χ ≠ 1 → ψ ≠ 1 →
    Representation.IsIrreducible (galoisRepresentation χ) →
    Representation.IsIrreducible (galoisRepresentation ψ) →
    characterInner χ ψ = 0 →
    ¬ (WindowZero F c D χ ∧ WindowZero F c D ψ)

theorem no_function_family_satisfies_printed_conjunction
    (F : DirichletCharacter ℂ 8 → ℂ → ℂ) (c D : ℝ) :
    ¬ (PrintedRealIff F c D ∧ PrintedExclusion F c D) := by
  rintro ⟨hiff, hexc⟩
  have ha := (hiff chiA chiA_primitive chiA_nontrivial).mpr chiA_real
  have hb := (hiff chiB chiB_primitive chiB_nontrivial).mpr chiB_real
  exact hexc chiA chiB chiA_primitive chiB_primitive chiA_nontrivial chiB_nontrivial
    chiA_irreducible chiB_irreducible characters_orthogonal ⟨ha, hb⟩

noncomputable def nativeLFunctions : DirichletCharacter ℂ 8 → ℂ → ℂ :=
  fun χ s => DirichletCharacter.LFunction χ s

theorem native_zero_condition (χ : DirichletCharacter ℂ 8) (c D : ℝ) :
    WindowZero nativeLFunctions c D χ ↔
      ∃ β : ℝ, 1 - c / Real.log D < β ∧ β < 1 ∧
        DirichletCharacter.LFunction χ (β : ℂ) = 0 := by
  simp only [WindowZero, nativeLFunctions, Set.mem_Ioo, and_assoc]

theorem window_nonempty (c : ℝ) (hc : 0 < c) :
    (Set.Ioo (1 - c / Real.log absoluteDiscriminant) 1).Nonempty := by
  apply Set.nonempty_Ioo.mpr
  have hlog : 0 < Real.log absoluteDiscriminant := Real.log_pos absoluteDiscriminant_gt_one
  have hdiv := div_pos hc hlog
  linarith

theorem native_conjunction_impossible (c : ℝ) :
    ¬ (PrintedRealIff nativeLFunctions c absoluteDiscriminant ∧
      PrintedExclusion nativeLFunctions c absoluteDiscriminant) :=
  no_function_family_satisfies_printed_conjunction _ _ _

theorem complete_counterexample :
    IsGalois ℚ K ∧ Module.finrank ℚ K = 4 ∧ NumberField.discr K = 256 ∧
    Fintype.card G = 4 ∧ twoPrime.ramificationIdxIn (𝓞 K) = 4 ∧
    ramifiedPrime.inertia G = ⊤ ∧
    chiA.IsPrimitive ∧ chiB.IsPrimitive ∧ chiA ≠ 1 ∧ chiB ≠ 1 ∧ chiA ≠ chiB ∧
    Representation.IsIrreducible (galoisRepresentation chiA) ∧
    Representation.IsIrreducible (galoisRepresentation chiB) ∧
    RealCharacter chiA ∧ RealCharacter chiB ∧ characterInner chiA chiB = 0 ∧
    ∀ c : ℝ, 0 < c →
      (Set.Ioo (1 - c / Real.log absoluteDiscriminant) 1).Nonempty ∧
      ¬ (PrintedRealIff nativeLFunctions c absoluteDiscriminant ∧
        PrintedExclusion nativeLFunctions c absoluteDiscriminant) := by
  refine ⟨extension_galois, extension_degree, actual_discriminant, galois_card,
    ramification_index_two, actual_inertia_two, chiA_primitive,
    chiB_primitive, chiA_nontrivial, chiB_nontrivial, characters_distinct, chiA_irreducible,
    chiB_irreducible, chiA_real, chiB_real, characters_orthogonal, ?_⟩
  intro c hc
  exact ⟨window_nonempty c hc, native_conjunction_impossible c⟩

end TLMC25
