import Mathlib

noncomputable section
open Polynomial
open scoped CharTwo
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace TLMC92

abbrev k := ZMod 2
instance two_prime : Fact (Nat.Prime 2) := ⟨by decide⟩
abbrev A := Polynomial k
abbrev K := RatFunc k

section Carlitz
variable {L : Type*} [Field L] [CharP L 2] [Algebra k L]

/-- The actual Carlitz action of the coefficient-ring generator. -/
def tOperator (theta : L) : Module.End k L where
  toFun x := x ^ 2 + theta * x
  map_add' x y := by rw [add_pow_char]; ring
  map_smul' c x := by
    classical
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl <;>
      simp only [RingHom.id_apply, zero_smul, one_smul, zero_pow (by decide : 2 ≠ 0),
        mul_zero, add_zero]

@[simp] theorem tOperator_apply (theta x : L) :
    tOperator theta x = x ^ 2 + theta * x := rfl

/-- Polynomial evaluation in the true ring of linear endomorphisms. -/
def carlitzAction (theta : L) : A →ₐ[k] Module.End k L :=
  Polynomial.aeval (tOperator theta)

abbrev CarlitzModule (theta : L) := Module.AEval' (tOperator theta)

/-- The recursive polynomial for the genuine action of T^n. -/
def iterPoly (theta : L) : ℕ → L[X]
  | 0 => X
  | n + 1 => iterPoly theta n ^ 2 + C theta * iterPoly theta n

@[simp] theorem iterPoly_zero (theta : L) : iterPoly theta 0 = X := rfl
@[simp] theorem iterPoly_succ (theta : L) (n : ℕ) :
    iterPoly theta (n+1) = iterPoly theta n ^ 2 + C theta * iterPoly theta n := rfl

theorem eval_iterPoly (theta x : L) (n : ℕ) :
    (iterPoly theta n).eval x = (tOperator theta ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [iterPoly_succ, eval_add, eval_pow, eval_mul, eval_C, ih]
    rw [pow_succ' (tOperator theta) n]
    rfl

theorem iterPoly_natDegree (theta : L) (n : ℕ) :
    (iterPoly theta n).natDegree = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterPoly_succ, natDegree_add_eq_left_of_natDegree_lt]
    · rw [natDegree_pow, ih, pow_succ]
      omega
    · calc
        (C theta * iterPoly theta n).natDegree ≤ (iterPoly theta n).natDegree :=
          natDegree_C_mul_le _ _
        _ < (iterPoly theta n ^ 2).natDegree := by
          rw [natDegree_pow, ih]
          have : 0 < 2 ^ n := pow_pos (by decide) _
          omega

theorem iterPoly_ne_zero (theta : L) (n : ℕ) : iterPoly theta n ≠ 0 := by
  intro h
  have := iterPoly_natDegree theta n
  rw [h, natDegree_zero] at this
  exact (pow_ne_zero n (by decide : (2:ℕ)≠0)) this.symm

theorem iterPoly_derivative (theta : L) (n : ℕ) :
    derivative (iterPoly theta n) = C (theta ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterPoly_succ, derivative_add, derivative_pow, derivative_mul, derivative_C, ih]
    simp [pow_succ, mul_comm]

theorem iterPoly_separable (theta : L) (h : theta ≠ 0) (n : ℕ) :
    (iterPoly theta n).Separable := by
  rw [separable_def, iterPoly_derivative]
  refine ⟨0, C ((theta^n)⁻¹), ?_⟩
  rw [zero_mul, zero_add, ← C_mul, inv_mul_cancel₀ (pow_ne_zero n h), C_1]

/-- The space of actual finite linear combinations of X^(2^i). -/
def twoPolynomials (L : Type*) [Field L] : Submodule L L[X] :=
  Submodule.span L (Set.range fun n : ℕ => (X : L[X]) ^ (2 ^ n))

theorem twoPolynomials_X : (X : L[X]) ∈ twoPolynomials L := by
  exact Submodule.subset_span ⟨0, by simp⟩

theorem twoPolynomials_sq {p : L[X]} (hp : p ∈ twoPolynomials L) :
    p ^ 2 ∈ twoPolynomials L := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨n,rfl⟩ := hp
    apply Submodule.subset_span
    exact ⟨n+1, by rw [← pow_mul]; simp [pow_succ, Nat.mul_comm]⟩
  | zero => simp
  | add p q hp hq ihp ihq =>
    rw [add_pow_char]
    exact (twoPolynomials L).add_mem ihp ihq
  | smul a p hp ih =>
    rw [smul_eq_C_mul, mul_pow, ← map_pow C a 2, ← smul_eq_C_mul]
    exact (twoPolynomials L).smul_mem (a^2) ih

theorem iterPoly_twoPolynomials (theta : L) (n : ℕ) :
    iterPoly theta n ∈ twoPolynomials L := by
  induction n with
  | zero => exact twoPolynomials_X
  | succ n ih =>
    exact (twoPolynomials L).add_mem (twoPolynomials_sq ih)
      (by simpa [Algebra.smul_def] using (twoPolynomials L).smul_mem theta ih)

/-- All coefficients of the actual parameter polynomial are used. -/
def carlitzPoly (theta : L) (a : A) : L[X] :=
  ∑ n ∈ a.support, C (algebraMap k L (a.coeff n)) * iterPoly theta n

theorem carlitzPoly_eval (theta x : L) (a : A) :
    (carlitzPoly theta a).eval x = carlitzAction theta a x := by
  rw [carlitzAction, aeval_endomorphism]
  simp only [carlitzPoly, eval_finsetSum, eval_mul, eval_C, eval_iterPoly,
    Polynomial.sum, Algebra.smul_def]

theorem carlitzPoly_twoPolynomials (theta : L) (a : A) :
    carlitzPoly theta a ∈ twoPolynomials L := by
  apply Submodule.sum_mem
  intro i hi
  rw [← smul_eq_C_mul]
  exact (twoPolynomials L).smul_mem _ (iterPoly_twoPolynomials theta i)

theorem carlitzPoly_derivative (theta : L) (a : A) :
    derivative (carlitzPoly theta a) = C (Polynomial.aeval theta a) := by
  simp only [carlitzPoly, derivative_sum, derivative_mul, derivative_C,
    zero_mul, zero_add, iterPoly_derivative, ← C_mul, ← map_sum,
    aeval_def, eval₂_eq_sum, Polynomial.sum]

variable [Infinite L]

theorem carlitzPoly_zero (theta : L) : carlitzPoly theta 0 = 0 := by
  apply Polynomial.funext
  intro x
  simp [carlitzPoly_eval]

theorem carlitzPoly_one (theta : L) : carlitzPoly theta 1 = X := by
  apply Polynomial.funext
  intro x
  simp [carlitzPoly_eval]

theorem carlitzPoly_add (theta : L) (a b : A) :
    carlitzPoly theta (a+b) = carlitzPoly theta a + carlitzPoly theta b := by
  apply Polynomial.funext
  intro x
  simp [carlitzPoly_eval]

theorem carlitzPoly_mul (theta : L) (a b : A) :
    carlitzPoly theta (a*b) = (carlitzPoly theta a).comp (carlitzPoly theta b) := by
  apply Polynomial.funext
  intro x
  simp [carlitzPoly_eval, Module.End.mul_apply]

theorem carlitzPoly_scalar (theta : L) (c : k) :
    carlitzPoly theta (C c) = C (algebraMap k L c) * X := by
  apply Polynomial.funext
  intro x
  simp [carlitzPoly_eval, carlitzAction, Algebra.smul_def]

theorem carlitzPoly_X_pow (theta : L) (n : ℕ) :
    carlitzPoly theta (X^n) = iterPoly theta n := by
  apply Polynomial.funext
  intro x
  simp only [carlitzPoly_eval, carlitzAction, map_pow, aeval_X, eval_iterPoly]

theorem carlitzPoly_injective (theta : L)
    (hi : Function.Injective (Polynomial.aeval theta : A →ₐ[k] L)) :
    Function.Injective (carlitzPoly theta) := by
  intro a b h
  apply hi
  apply Polynomial.C_injective
  simpa only [carlitzPoly_derivative] using congrArg derivative h

theorem carlitzAction_injective (theta : L)
    (hi : Function.Injective (Polynomial.aeval theta : A →ₐ[k] L)) :
    Function.Injective (carlitzAction theta) := by
  intro a b hab
  apply carlitzPoly_injective theta hi
  apply Polynomial.funext
  intro x
  simp only [carlitzPoly_eval, hab]

theorem carlitzPoly_generator (theta : L) :
    carlitzPoly theta X = X^2 + C theta * X := by
  have h := carlitzPoly_X_pow theta 1
  simpa only [pow_one, iterPoly_succ, iterPoly_zero] using h

/-- The concrete algebraic definition, expressed through polynomial addition and composition. -/
structure DrinfeldModule (iota : A →+* L) where
  polynomial : A → L[X]
  map_zero : polynomial 0 = 0
  map_one : polynomial 1 = X
  map_add : ∀ a b, polynomial (a+b) = polynomial a + polynomial b
  map_mul : ∀ a b, polynomial (a*b) = (polynomial a).comp (polynomial b)
  map_scalar : ∀ c : k, polynomial (C c) = C (algebraMap k L c) * X
  frobenius_powers : ∀ a, polynomial a ∈ twoPolynomials L
  tangent_action : ∀ a, derivative (polynomial a) = C (iota a)
  faithful : Function.Injective polynomial
  non_scalar : 1 < (polynomial X).natDegree

/-- Rank is read from the actual highest Frobenius exponent of the T-action. -/
def DrinfeldModule.rank {iota : A →+* L} (phi : DrinfeldModule iota) : ℕ :=
  Nat.log 2 (phi.polynomial X).natDegree

def carlitz (theta : L)
    (hi : Function.Injective (Polynomial.aeval theta : A →ₐ[k] L)) :
    DrinfeldModule (Polynomial.aeval theta).toRingHom where
  polynomial := carlitzPoly theta
  map_zero := carlitzPoly_zero theta
  map_one := carlitzPoly_one theta
  map_add := carlitzPoly_add theta
  map_mul := carlitzPoly_mul theta
  map_scalar := carlitzPoly_scalar theta
  frobenius_powers := carlitzPoly_twoPolynomials theta
  tangent_action := carlitzPoly_derivative theta
  faithful := carlitzPoly_injective theta hi
  non_scalar := by
    have h := carlitzPoly_X_pow theta 1
    simp only [pow_one] at h
    rw [h, iterPoly_natDegree]
    decide

theorem carlitz_rank_one (theta : L)
    (hi : Function.Injective (Polynomial.aeval theta : A →ₐ[k] L)) :
    (carlitz theta hi).rank = 1 := by
  have h := carlitzPoly_X_pow theta 1
  simp only [pow_one] at h
  simp only [DrinfeldModule.rank, carlitz, h, iterPoly_natDegree]
  decide

end Carlitz

def baseTheta : K := RatFunc.X
abbrev Lext (n : ℕ) := (iterPoly baseTheta n).SplittingField

instance coefficientRingInfinite : Infinite A := by
  apply Infinite.of_injective (fun n : ℕ => (X : A)^n)
  intro n m h
  simpa only [natDegree_X_pow] using congrArg Polynomial.natDegree h

instance baseInfinite : Infinite K :=
  Infinite.of_injective (algebraMap A K) (RatFunc.algebraMap_injective k)

instance extInfinite (n : ℕ) : Infinite (Lext n) :=
  Infinite.of_injective (algebraMap K (Lext n)) (algebraMap K (Lext n)).injective

theorem extension_finite (n : ℕ) : FiniteDimensional K (Lext n) := inferInstance

def extTheta (n : ℕ) : Lext n := algebraMap K (Lext n) baseTheta

theorem baseTheta_ne_zero : baseTheta ≠ 0 := RatFunc.X_ne_zero

theorem extTheta_ne_zero (n : ℕ) : extTheta n ≠ 0 := by
  intro h
  apply baseTheta_ne_zero
  apply (algebraMap K (Lext n)).injective
  simpa only [extTheta, map_zero] using h

theorem base_aeval_eq (a : A) : Polynomial.aeval baseTheta a = algebraMap A K a := by
  have h : (Polynomial.aeval baseTheta : A →ₐ[k] K) =
      IsScalarTower.toAlgHom k A K := by
    ext
    simp [baseTheta]
  exact congrArg (fun f : A →ₐ[k] K => f a) h

theorem ext_aeval_eq (n : ℕ) (a : A) :
    Polynomial.aeval (extTheta n) a = algebraMap K (Lext n) (algebraMap A K a) := by
  calc
    Polynomial.aeval (extTheta n) a =
        (IsScalarTower.toAlgHom k K (Lext n)) (Polynomial.aeval baseTheta a) :=
      Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom k K (Lext n)) baseTheta a
    _ = _ := by rw [base_aeval_eq]; rfl

theorem ext_aeval_injective (n : ℕ) :
    Function.Injective (Polynomial.aeval (extTheta n) : A →ₐ[k] Lext n) := by
  intro a b h
  simp only [ext_aeval_eq] at h
  exact RatFunc.algebraMap_injective k ((algebraMap K (Lext n)).injective h)

def extCarlitz (n : ℕ) := carlitz (extTheta n) (ext_aeval_injective n)

theorem extCarlitz_rank (n : ℕ) : (extCarlitz n).rank = 1 :=
  carlitz_rank_one _ _

theorem coefficient_field_size : Fintype.card k = 2 := by simp [k]

theorem generic_characteristic (n : ℕ) :
    RingHom.ker (Polynomial.aeval (extTheta n) : A →ₐ[k] Lext n).toRingHom = ⊥ := by
  exact (RingHom.injective_iff_ker_eq_bot _).mp (ext_aeval_injective n)

theorem full_action_agreement (n : ℕ) (a : A) (x : Lext n) :
    a • Module.AEval'.of (tOperator (extTheta n)) x =
      Module.AEval'.of (tOperator (extTheta n)) ((extCarlitz n).polynomial a |>.eval x) := by
  change a • Module.AEval'.of (tOperator (extTheta n)) x =
    Module.AEval'.of (tOperator (extTheta n)) ((carlitzPoly (extTheta n) a).eval x)
  rw [carlitzPoly_eval]
  rfl

theorem iterPoly_map {L E : Type*} [Field L] [Field E]
    (f : L →+* E) (theta : L) (n : ℕ) :
    (iterPoly theta n).map f = iterPoly (f theta) n := by
  induction n with
  | zero => simp only [iterPoly, Polynomial.map_X]
  | succ n ih => simp only [iterPoly, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_mul, Polynomial.map_C, ih]

abbrev torsionPoints (n : ℕ) :=
  Submodule.torsion A (CarlitzModule (extTheta n))

abbrev divisionPoints (n : ℕ) := (iterPoly baseTheta n).rootSet (Lext n)

theorem torsion_membership (n : ℕ) (x : Lext n) :
    Module.AEval'.of (tOperator (extTheta n)) x ∈ torsionPoints n ↔
      ∃ a : A, a ≠ 0 ∧ ((extCarlitz n).polynomial a).eval x = 0 := by
  rw [Submodule.mem_torsion_iff]
  constructor
  · rintro ⟨⟨a,ha⟩,h⟩
    refine ⟨a, mem_nonZeroDivisors_iff_ne_zero.mp ha, ?_⟩
    change a • Module.AEval'.of (tOperator (extTheta n)) x = 0 at h
    rw [full_action_agreement] at h
    apply (Module.AEval'.of (tOperator (extTheta n))).injective
    simpa only [map_zero] using h
  · rintro ⟨a,ha,h⟩
    refine ⟨⟨a,mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩, ?_⟩
    change a • Module.AEval'.of (tOperator (extTheta n)) x = 0
    rw [full_action_agreement, h, map_zero]

theorem divisionPoints_card (n : ℕ) : Fintype.card (divisionPoints n) = 2^n := by
  rw [card_rootSet_eq_natDegree (iterPoly_separable baseTheta baseTheta_ne_zero n)
    (Polynomial.SplittingField.splits _), iterPoly_natDegree]

def rootToTorsion (n : ℕ) (x : divisionPoints n) : torsionPoints n := by
  refine ⟨Module.AEval'.of (tOperator (extTheta n)) x.1, ?_⟩
  rw [Submodule.mem_torsion_iff]
  refine ⟨⟨(X:A)^n, mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ X_ne_zero)⟩, ?_⟩
  change (X^n : A) • Module.AEval'.of (tOperator (extTheta n)) x.1 = 0
  rw [Module.AEval'.X_pow_smul_of]
  have hx : (iterPoly (extTheta n) n).eval x.1 = 0 := by
    have h := aeval_eq_zero_of_mem_rootSet x.2
    simpa only [aeval_def, eval₂_eq_eval_map, iterPoly_map, extTheta] using h
  rw [eval_iterPoly] at hx
  simp only [Module.End.smul_def, hx, map_zero]

theorem rootToTorsion_injective (n : ℕ) : Function.Injective (rootToTorsion n) := by
  intro x y h
  apply Subtype.ext
  apply (Module.AEval'.of (tOperator (extTheta n))).injective
  exact congrArg (fun z : torsionPoints n => z.1) h

theorem torsion_card_lower_bound (n : ℕ) :
    (2^n : Cardinal) ≤ Cardinal.mk (torsionPoints n) := by
  have h := Cardinal.mk_le_of_injective (rootToTorsion_injective n)
  rwa [Cardinal.mk_fintype, divisionPoints_card, Nat.cast_pow, Nat.cast_ofNat] at h

theorem no_uniform_torsion_bound :
    ¬ ∃ B : ℕ, ∀ n : ℕ, Cardinal.mk (torsionPoints n) ≤ (B : Cardinal) := by
  rintro ⟨B,hB⟩
  have h := (torsion_card_lower_bound B).trans (hB B)
  have hn : 2^B ≤ B := by exact_mod_cast h
  exact Nat.lt_two_pow_self.not_ge hn

theorem complete_counterexample :
    Fintype.card k = 2 ∧
    (∀ n : ℕ, FiniteDimensional K (Lext n) ∧ (extCarlitz n).rank = 1 ∧
      RingHom.ker (Polynomial.aeval (extTheta n) : A →ₐ[k] Lext n).toRingHom = ⊥ ∧
      Fintype.card (divisionPoints n) = 2^n) ∧
    ¬ ∃ B : ℕ, ∀ n : ℕ, Cardinal.mk (torsionPoints n) ≤ (B : Cardinal) := by
  refine ⟨coefficient_field_size, fun n => ?_, no_uniform_torsion_bound⟩
  exact ⟨extension_finite n, extCarlitz_rank n, generic_characteristic n, divisionPoints_card n⟩

end TLMC92
