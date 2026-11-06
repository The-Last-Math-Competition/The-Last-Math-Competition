import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-! Infinitely many actual rank-three completely decomposable Butler groups.
The rank is genuine Module.rank over the integers, not an assigned label. -/
namespace TLMC4279
open scoped DirectSum
open Module

abbrev Prime := {p : ℕ // p.Prime}
abbrev R (p : Prime) := Localization.Away (p.1 : ℤ)
noncomputable instance rationalIntegerModule (p : Prime) : Module ℤ (R p) := Algebra.toModule

abbrev G (p : Prime) := Fin 3 → R p
noncomputable instance tripleIntegerModule (p : Prime) : Module ℤ (G p) :=
  Pi.module (Fin 3) (fun _ => R p) ℤ

abbrev D (p : Prime) := ⨁ _ : Fin 3, R p

theorem prime_cast_ne_zero (p : Prime) : (p.1 : ℤ) ≠ 0 := by
  exact_mod_cast p.2.ne_zero

theorem integer_map_injective (p : Prime) :
    Function.Injective (algebraMap ℤ (R p)) :=
  IsLocalization.injective (R p)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (prime_cast_ne_zero p))

theorem rank_one (p : Prime) : Module.rank ℤ (R p) = 1 := by
  rw [IsLocalizedModule.rank_eq (Submonoid.powers (p.1 : ℤ))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (prime_cast_ne_zero p))
    (Algebra.linearMap ℤ (R p))]
  exact rank_self ℤ

noncomputable def toRat (p : Prime) : R p →+* ℚ :=
  IsLocalization.Away.lift (p.1 : ℤ)
    (isUnit_iff_ne_zero.mpr (by change (p.1 : ℚ) ≠ 0; exact_mod_cast p.2.ne_zero) :
      IsUnit ((Int.castRingHom ℚ) (p.1 : ℤ)))

theorem toRat_injective (p : Prime) : Function.Injective (toRat p) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (p.1 : ℤ)) (toRat p)).mpr
  intro a b
  simp only [toRat, IsLocalization.Away.lift_eq]
  change (algebraMap ℤ (R p)) a = (algebraMap ℤ (R p)) b ↔ (a : ℚ) = (b : ℚ)
  simp only [(integer_map_injective p).eq_iff, Int.cast_inj]

theorem summand_torsion_free (p : Prime) (n : ℕ) (hn : n ≠ 0) (x : R p)
    (hx : n • x = 0) : x = 0 := by
  apply toRat_injective p
  rw [map_zero]
  have h := congrArg (toRat p) hx
  simpa [nsmul_eq_mul, hn] using h

noncomputable def integerTriple (p : Prime) : (Fin 3 → ℤ) →ₗ[ℤ] G p :=
  { toFun := fun v i => algebraMap ℤ (R p) (v i)
    map_add' := by intros; ext i; simp
    map_smul' := by intros; ext i; simp }

noncomputable def rationalTriple (p : Prime) : G p →ₗ[ℤ] (Fin 3 → ℚ) :=
  { toFun := fun v i => toRat p (v i)
    map_add' := by intros; ext i; simp
    map_smul' := by intros; ext i; simp }

theorem integerTriple_injective (p : Prime) : Function.Injective (integerTriple p) := by
  intro x y h
  ext i
  exact integer_map_injective p (congrFun h i)

theorem rationalTriple_injective (p : Prime) : Function.Injective (rationalTriple p) := by
  intro x y h
  ext i
  exact toRat_injective p (congrFun h i)

theorem rational_triple_integer_rank : Module.rank ℤ (Fin 3 → ℚ) = 3 := by
  rw [← IsLocalization.rank_eq ℚ (nonZeroDivisors ℤ) (le_refl _)]
  exact rank_fin_fun (R := ℚ) 3

theorem rank_three (p : Prime) : Module.rank ℤ (G p) = 3 := by
  apply le_antisymm
  · calc
      Module.rank ℤ (G p) ≤ Module.rank ℤ (Fin 3 → ℚ) :=
        (rationalTriple p).rank_le_of_injective (rationalTriple_injective p)
      _ = 3 := rational_triple_integer_rank
  · calc
      3 = Module.rank ℤ (Fin 3 → ℤ) := (rank_fin_fun (R := ℤ) 3).symm
      _ ≤ Module.rank ℤ (G p) :=
        (integerTriple p).rank_le_of_injective (integerTriple_injective p)

theorem torsion_free (p : Prime) (n : ℕ) (hn : n ≠ 0) (x : G p)
    (hx : n • x = 0) : x = 0 := by
  apply rationalTriple_injective p
  rw [map_zero]
  have h := congrArg (rationalTriple p) hx
  rw [map_nsmul, map_zero] at h
  ext i
  have hi := congrFun h i
  simpa [nsmul_eq_mul, hn] using hi

/-- Purity of an actual integer submodule: every solvable scalar equation
with right side in H has a solution in H. This is nA ∩ H = nH. -/
def Pure {A : Type*} [AddCommMonoid A] [Module ℤ A] (H : Submodule ℤ A) : Prop :=
  ∀ n : ℕ, ∀ h : H, (∃ a : A, n • a = (h : A)) → ∃ b : H, n • b = h

theorem top_pure (p : Prime) : Pure (⊤ : Submodule ℤ (D p)) := by
  rintro n h ⟨a, ha⟩
  exact ⟨⟨a, Submodule.mem_top⟩, Subtype.ext ha⟩

noncomputable def directSumEquiv (p : Prime) : G p ≃ₗ[ℤ] D p :=
  (DirectSum.linearEquivFunOnFintype ℤ (Fin 3) (fun _ => R p)).symm

theorem pure_rank_one_sum_witness (p : Prime) :
    (∀ _i : Fin 3, Module.rank ℤ (R p) = 1) ∧
    ∃ H : Submodule ℤ (D p), Pure H ∧ Nonempty (G p ≃ₗ[ℤ] H) := by
  refine ⟨fun _ => rank_one p, ⊤, top_pure p, ?_⟩
  exact ⟨(directSumEquiv p).trans (Submodule.topEquiv).symm⟩

theorem family_qualifies (p : Prime) :
    Module.rank ℤ (G p) = 3 ∧
    (∀ n : ℕ, n ≠ 0 → ∀ x : G p, n • x = 0 → x = 0) ∧
    Module.rank ℤ (R p) = 1 ∧
    (∀ n : ℕ, n ≠ 0 → ∀ x : R p, n • x = 0 → x = 0) ∧
    ∃ H : Submodule ℤ (D p), Pure H ∧ Nonempty (G p ≃ₗ[ℤ] H) := by
  exact ⟨rank_three p, fun n hn x => torsion_free p n hn x,
    rank_one p, fun n hn x => summand_torsion_free p n hn x,
    (pure_rank_one_sum_witness p).2⟩

def DivisibleBy (n : ℕ) (A : Type*) [AddCommGroup A] : Prop :=
  Function.Surjective (fun a : A => n • a)

theorem divisible_by_own_prime (p : Prime) : DivisibleBy p.1 (G p) := by
  intro x
  refine ⟨fun i => IsLocalization.Away.invSelf (p.1 : ℤ) * x i, ?_⟩
  ext i
  simp only [Pi.smul_apply, nsmul_eq_mul]
  have h : (p.1 : R p) * IsLocalization.Away.invSelf (p.1 : ℤ) = 1 :=
    by simpa using (IsLocalization.Away.mul_invSelf (S := R p) (p.1 : ℤ))
  rw [← mul_assoc, h, one_mul]

theorem other_prime_cast_ne_zero (p q : Prime) (hpq : p ≠ q) :
    (p.1 : ZMod q.1) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  apply hpq
  apply Subtype.ext
  exact (Nat.dvd_prime p.2).mp h |>.resolve_left q.2.ne_one |>.symm

noncomputable def residue (p q : Prime) (hpq : p ≠ q) : R p →+* ZMod q.1 := by
  letI : Fact q.1.Prime := ⟨q.2⟩
  have hu : IsUnit ((p.1 : ℤ) : ZMod q.1) := by
    rw [isUnit_iff_ne_zero]
    simpa only [Int.cast_natCast] using other_prime_cast_ne_zero p q hpq
  exact IsLocalization.Away.lift (S := R p) (g := Int.castRingHom (ZMod q.1))
    (p.1 : ℤ) hu

theorem not_divisible_by_other_prime (p q : Prime) (hpq : p ≠ q) :
    ¬ DivisibleBy q.1 (G p) := by
  intro h
  obtain ⟨x, hx⟩ := h (fun _ => 1)
  have hi := congrFun hx (0 : Fin 3)
  have hz := congrArg (residue p q hpq) hi
  let _ : Fact q.1.Prime := ⟨q.2⟩
  simp [nsmul_eq_mul] at hz

theorem divisible_invariant {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (n : ℕ) : DivisibleBy n A ↔ DivisibleBy n B := by
  constructor
  · intro h b
    obtain ⟨a, ha⟩ := h (e.symm b)
    refine ⟨e a, ?_⟩
    simpa only [map_nsmul, e.apply_symm_apply] using congrArg e ha
  · intro h a
    obtain ⟨b, hb⟩ := h (e a)
    refine ⟨e.symm b, ?_⟩
    simpa only [map_nsmul, e.symm_apply_apply] using congrArg e.symm hb

theorem pairwise_nonisomorphic (p q : Prime) (hpq : p ≠ q) :
    ¬ Nonempty (G p ≃+ G q) := by
  rintro ⟨e⟩
  have h := (divisible_invariant e p.1).mp (divisible_by_own_prime p)
  exact not_divisible_by_other_prime q p hpq.symm h

def groupIsoSetoid : Setoid Prime where
  r p q := Nonempty (G p ≃+ G q)
  iseqv := ⟨fun _ => ⟨AddEquiv.refl _⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

theorem prime_class_injective : Function.Injective (Quotient.mk groupIsoSetoid) := by
  intro p q h
  by_contra hpq
  exact pairwise_nonisomorphic p q hpq (Quotient.exact h)

instance infinite_primes : Infinite Prime := by
  apply Set.infinite_coe_iff.mpr
  intro h
  exact Nat.not_bddAbove_setOfPred_prime h.bddAbove

theorem infinite_actual_isomorphism_quotient : Infinite (Quotient groupIsoSetoid) :=
  Infinite.of_injective _ prime_class_injective

theorem no_finite_classification {L : Type*} [Finite L]
    (label : Prime → L)
    (hcomplete : ∀ p q, label p = label q → Nonempty (G p ≃+ G q)) : False := by
  have h : Function.Injective label := by
    intro p q hpq
    by_contra hne
    exact pairwise_nonisomorphic p q hne (hcomplete p q hpq)
  have : Finite Prime := Finite.of_injective label h
  exact not_finite Prime

end TLMC4279
