import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases

noncomputable section
open Filter
open scoped BigOperators Topology

namespace Conjecture4316

/-- The integral positive-definite quadratic form x_0^2+x_1^2. -/
def Q : QuadraticForm ℤ (Fin 2 → ℤ) :=
  QuadraticMap.proj 0 0 + QuadraticMap.proj 1 1

theorem Q_apply (x : Fin 2 → ℤ) : Q x = x 0 ^ 2 + x 1 ^ 2 := by
  simp [Q, pow_two]

/-- Canonical residue representatives of actual representations of 3. -/
def Solutions (q : ℕ) :=
  {x : Fin 2 → Fin q // ((x 0).val ^ 2 + (x 1).val ^ 2) % q = 3 % q}

theorem residue_value_agrees_with_form (q : ℕ) (x : Fin 2 → Fin q) :
    Q (fun i => ((x i).val : ℤ)) =
      (((x 0).val ^ 2 + (x 1).val ^ 2 : ℕ) : ℤ) := by
  simp [Q_apply]

theorem no_sum_squares_three_mod_four (a b : ℕ) : (a ^ 2 + b ^ 2) % 4 ≠ 3 := by
  have h : ∀ x y : Fin 4, (x.val ^ 2 + y.val ^ 2) % 4 ≠ 3 := by decide
  simpa [Nat.add_mod, Nat.pow_mod] using
    h ⟨a % 4, Nat.mod_lt _ (by decide)⟩ ⟨b % 4, Nat.mod_lt _ (by decide)⟩

theorem no_solutions_of_four_dvd (q : ℕ) (hq : 4 ∣ q) : IsEmpty (Solutions q) := by
  refine ⟨fun x => ?_⟩
  have hx := congrArg (fun t : ℕ => t % 4) x.property
  change ((x.val 0).val ^ 2 + (x.val 1).val ^ 2) % q % 4 = 3 % q % 4 at hx
  rw [Nat.mod_mod_of_dvd _ hq, Nat.mod_mod_of_dvd _ hq] at hx
  norm_num at hx
  exact no_sum_squares_three_mod_four _ _ hx

theorem two_power_solution_count_zero (e : ℕ) : Nat.card (Solutions (2 ^ (e + 2))) = 0 := by
  have hd : 4 ∣ 2 ^ (e + 2) := by
    simp [pow_add]
  letI : IsEmpty (Solutions (2 ^ (e + 2))) := no_solutions_of_four_dvd _ hd
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

/-- Standard normalized representation density for a binary form.
Starting at e+2 omits only the first two terms of the prime-power sequence. -/
def density (p e : ℕ) : ℝ :=
  (Nat.card (Solutions (p ^ (e + 2))) : ℝ) / (p ^ (e + 2) : ℕ)

theorem two_density_zero (e : ℕ) : density 2 e = 0 := by
  simp [density, two_power_solution_count_zero]

theorem two_density_tends_zero : Tendsto (density 2) atTop (𝓝 0) := by
  have hz : density 2 = fun _ : ℕ => (0 : ℝ) := funext two_density_zero
  rw [hz]
  exact tendsto_const_nhds

theorem two_local_factor_zero {L : ℝ}
    (h : Tendsto (density 2) atTop (𝓝 L)) : L = 0 :=
  tendsto_nhds_unique h two_density_tends_zero

def eulerPartial (L : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime, L p

theorem euler_partial_zero {L : ℕ → ℝ} (hL : L 2 = 0) {N : ℕ} (hN : 2 ≤ N) :
    eulerPartial L N = 0 := by
  apply Finset.prod_eq_zero (i := 2)
  · simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by decide⟩
  · exact hL

theorem euler_product_tends_zero {L : ℕ → ℝ}
    (hL : Tendsto (density 2) atTop (𝓝 (L 2))) :
    Tendsto (eulerPartial L) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (euler_partial_zero (two_local_factor_zero hL) hN).symm

theorem euler_product_cannot_equal_one_half :
    ¬ ∃ L : ℕ → ℝ,
      (∀ p, p.Prime → Tendsto (density p) atTop (𝓝 (L p))) ∧
      Tendsto (eulerPartial L) atTop (𝓝 (1 / 2 : ℝ)) := by
  rintro ⟨L, hL, hhalf⟩
  have heq := tendsto_nhds_unique hhalf (euler_product_tends_zero (hL 2 (by decide)))
  norm_num at heq

end Conjecture4316

#print axioms Conjecture4316.residue_value_agrees_with_form
#print axioms Conjecture4316.two_power_solution_count_zero
#print axioms Conjecture4316.euler_product_cannot_equal_one_half

namespace Conjecture4316.ExistenceDensity

/-- A genuine integral binary quadratic form, with no positivity restriction in the source. -/
def splitForm : QuadraticForm ℤ (Fin 2 → ℤ) := QuadraticMap.proj 0 1

theorem splitForm_apply (x : Fin 2 → ℤ) : splitForm x = x 0 * x 1 := by
  simp [splitForm]

theorem polar_formula (x y : Fin 2 → ℤ) :
    splitForm.polarBilin x y = x 0 * y 1 + y 0 * x 1 := by
  change (x 0 + y 0) * (x 1 + y 1) - x 0 * x 1 - y 0 * y 1 = _
  ring

def basisVector (i : Fin 2) : Fin 2 → ℤ := fun j => if j = i then 1 else 0

/-- Matrix of the actual integral polar bilinear form in the coordinate basis. -/
def polarMatrix : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => splitForm.polarBilin (basisVector i) (basisVector j)

theorem polar_determinant : polarMatrix.det = -1 := by
  simp only [Matrix.det_fin_two, polarMatrix, polar_formula]
  norm_num [basisVector]

theorem polar_nondegenerate (x : Fin 2 → ℤ)
    (hx : ∀ y : Fin 2 → ℤ, splitForm.polarBilin x y = 0) : x = 0 := by
  have h0 := hx (basisVector 0)
  have h1 := hx (basisVector 1)
  rw [polar_formula] at h0 h1
  simp [basisVector] at h0 h1
  funext i
  fin_cases i
  · exact h1
  · exact h0

/-- A residue class belongs if there exists a pair representing it modulo q. -/
def represented (q : ℕ) : Finset (Fin q) :=
  Finset.univ.filter (fun a => ∃ x y : Fin q, (x.val * y.val) % q = a.val)

theorem representation_expression_agrees (q : ℕ) (x : Fin 2 → Fin q) :
    splitForm (fun i => ((x i).val : ℤ)) =
      (((x 0).val * (x 1).val : ℕ) : ℤ) := by
  simp [splitForm_apply]

theorem every_target_represented (q : ℕ) (a : Fin q) :
    ∃ x y : Fin q, (x.val * y.val) % q = a.val := by
  have hq : 0 < q := Nat.zero_lt_of_lt a.isLt
  refine ⟨a, ⟨1 % q, Nat.mod_lt _ hq⟩, ?_⟩
  change (a.val * (1 % q)) % q = a.val
  simp [← Nat.mul_mod, Nat.mod_eq_of_lt a.isLt]

theorem represented_eq_univ (q : ℕ) : represented q = Finset.univ := by
  ext a
  simp [represented, every_target_represented q a]

theorem represented_count (q : ℕ) : (represented q).card = q := by
  rw [represented_eq_univ]
  simp

/-- Proportion of right-hand-side residue classes with at least one representation. -/
def existenceDensity (q : ℕ) : ℝ := ((represented q).card : ℝ) / q

theorem existence_density_one (q : ℕ) (hq : 0 < q) : existenceDensity q = 1 := by
  rw [existenceDensity, represented_count]
  exact div_self (by exact_mod_cast (Nat.ne_of_gt hq))

def localDensity (p e : ℕ) : ℝ := existenceDensity (p ^ (e + 1))

theorem local_density_one {p : ℕ} (hp : p.Prime) (e : ℕ) : localDensity p e = 1 := by
  exact existence_density_one _ (pow_pos hp.pos _)

theorem local_limit_one {p : ℕ} (hp : p.Prime) :
    Tendsto (localDensity p) atTop (𝓝 1) := by
  have h : localDensity p = fun _ : ℕ => (1 : ℝ) := funext (local_density_one hp)
  rw [h]
  exact tendsto_const_nhds

theorem every_consistent_factor_one {L : ℕ → ℝ}
    (hL : ∀ p, p.Prime → Tendsto (localDensity p) atTop (𝓝 (L p)))
    {p : ℕ} (hp : p.Prime) : L p = 1 :=
  tendsto_nhds_unique (hL p hp) (local_limit_one hp)

theorem existence_euler_partial_one {L : ℕ → ℝ}
    (hL : ∀ p, p.Prime → Tendsto (localDensity p) atTop (𝓝 (L p))) (N : ℕ) :
    Conjecture4316.eulerPartial L N = 1 := by
  apply Finset.prod_eq_one
  intro p hp
  exact every_consistent_factor_one hL (Finset.mem_filter.mp hp).2

theorem existence_euler_limit_one {L : ℕ → ℝ}
    (hL : ∀ p, p.Prime → Tendsto (localDensity p) atTop (𝓝 (L p))) :
    Tendsto (Conjecture4316.eulerPartial L) atTop (𝓝 1) := by
  have h : Conjecture4316.eulerPartial L = fun _ : ℕ => (1 : ℝ) :=
    funext (existence_euler_partial_one hL)
  rw [h]
  exact tendsto_const_nhds

theorem all_local_limits_and_product_exist :
    (∀ p : ℕ, p.Prime → Tendsto (localDensity p) atTop (𝓝 1)) ∧
    Tendsto (Conjecture4316.eulerPartial (fun _ => 1)) atTop (𝓝 1) :=
  ⟨fun _ hp => local_limit_one hp, existence_euler_limit_one (fun _ hp => local_limit_one hp)⟩

theorem existence_product_cannot_equal_one_half :
    ¬ ∃ L : ℕ → ℝ,
      (∀ p, p.Prime → Tendsto (localDensity p) atTop (𝓝 (L p))) ∧
      Tendsto (Conjecture4316.eulerPartial L) atTop (𝓝 (1 / 2 : ℝ)) := by
  rintro ⟨L, hL, hhalf⟩
  have h := tendsto_nhds_unique hhalf (existence_euler_limit_one hL)
  norm_num at h

end Conjecture4316.ExistenceDensity

#print axioms Conjecture4316.ExistenceDensity.polar_determinant
#print axioms Conjecture4316.ExistenceDensity.polar_nondegenerate
#print axioms Conjecture4316.ExistenceDensity.representation_expression_agrees
#print axioms Conjecture4316.ExistenceDensity.every_target_represented
#print axioms Conjecture4316.ExistenceDensity.represented_count
#print axioms Conjecture4316.ExistenceDensity.all_local_limits_and_product_exist
#print axioms Conjecture4316.ExistenceDensity.existence_product_cannot_equal_one_half
