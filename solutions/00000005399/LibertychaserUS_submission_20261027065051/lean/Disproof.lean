import Mathlib

/-!
# Conjecture 00000005399 is false: a counterexample to the claimed mixing correction

Conjecture (see `conjectures/00000005399.md`): for a finite irreducible Markov chain, the
expected first return time to a state x equals the reciprocal of the stationary measure
of x, plus a correction term which is a nonzero multiple of the negative first power of the
mixing rate (spectral gap), and the formula is exact.

Correspondence between the objects below and the conjecture:
* `IsStochastic P`      : P is a row-stochastic transition matrix (nonnegative, rows sum to 1).
* `IsIrreducible P`     : every state reaches every state with positive probability.
* `IsStationary P π`    : π is a probability vector with π P = π (the measure).
* `IsHittingTimes P x h`: h y = E_y[T_x] for all y, where T_x = min {n >= 0 : X_n = x}; for
                          irreducible finite chains this first-step linear system has a unique
                          solution, so it determines the hitting times.
* `ExpReturn P x r`     : r = E_x[T_x^+] with T_x^+ = min {n >= 1 : X_n = x}, i.e.
                          r = 1 + sum_y P(x,y) E_y[T_x] (the first-step decomposition).
* `eigenvalues P`       : the eigenvalues of P with algebraic multiplicity, as roots of the
                          characteristic polynomial over ℂ.
* `spectralGap P`       : 1 - max{|μ| : μ eigenvalue of P, μ ≠ 1}, the mixing rate.

The claim is refuted on the three-state chain P0 below, state 0: there E_0[T_0^+] = 23/8 and
π(0) = 8/23, so E_0[T_0^+] = 1/π(0) exactly, and no nonzero correction c / gap can be added.
-/

namespace TLMC5399

open Matrix

/-- Row-stochastic: nonnegative entries and every row sums to 1. -/
def IsStochastic {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j = 1

/-- Irreducible: for all states i, j there is a number of steps k with P^k(i,j) > 0. -/
def IsIrreducible {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, ∃ k : ℕ, 0 < (P ^ k) i j

/-- The stationary measure π: a probability vector with π P = π. -/
def IsStationary {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ) : Prop :=
  (∑ i, π i = 1) ∧ ∀ j, ∑ i, π i * P i j = π j

/-- First-step equations for the expected hitting times h y = E_y[T_x] of the state x. -/
def IsHittingTimes {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (x : Fin n) (h : Fin n → ℝ) : Prop :=
  h x = 0 ∧ ∀ y, y ≠ x → h y = 1 + ∑ z, P y z * h z

/-- r is the expected first return time E_x[T_x^+] = 1 + sum_y P(x,y) E_y[T_x]. -/
def ExpReturn {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (x : Fin n) (r : ℝ) : Prop :=
  ∃ h : Fin n → ℝ, IsHittingTimes P x h ∧ r = 1 + ∑ y, P x y * h y

/-- Eigenvalues of P (with multiplicity), as roots of its characteristic polynomial over ℂ. -/
noncomputable def eigenvalues {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Multiset ℂ :=
  (P.map (fun a : ℝ => (a : ℂ))).charpoly.roots

/-- Spectral gap (mixing rate): 1 minus the largest modulus of an eigenvalue other than 1. -/
noncomputable def spectralGap {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  1 - sSup {r : ℝ | ∃ μ ∈ eigenvalues P, μ ≠ 1 ∧ r = ‖μ‖}

/-- The conjecture as a statement: for every state of every irreducible chain there is a
nonzero correction coefficient c such that E_x[T_x^+] = 1/π(x) + c / gap exactly. -/
def ClaimedFormula : Prop :=
  ∀ (n : ℕ) (P : Matrix (Fin n) (Fin n) ℝ), IsStochastic P → IsIrreducible P →
    ∀ π : Fin n → ℝ, IsStationary P π → ∀ x : Fin n, ∀ r : ℝ, ExpReturn P x r →
      ∃ c : ℝ, c ≠ 0 ∧ r = 1 / π x + c / spectralGap P

/-- Uniform reading: one nonzero constant c works for all chains, states and expectations. -/
def ClaimedUniformFormula : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧ ∀ (n : ℕ) (P : Matrix (Fin n) (Fin n) ℝ), IsStochastic P → IsIrreducible P →
    ∀ π : Fin n → ℝ, IsStationary P π → ∀ x : Fin n, ∀ r : ℝ, ExpReturn P x r →
      r = 1 / π x + c / spectralGap P

/-! ## The counterexample chain P0 on states 0, 1, 2 -/

/-- Transition matrix P0 = [[1/2,1/4,1/4],[1/3,1/3,1/3],[1/5,2/5,2/5]]. -/
noncomputable def P0 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1/2, 1/4, 1/4; 1/3, 1/3, 1/3; 1/5, 2/5, 2/5]

/-- Stationary distribution (8/23, 15/46, 15/46) of P0. -/
noncomputable def π0 : Fin 3 → ℝ := ![8/23, 15/46, 15/46]

/-- Entries of a three-vector, by rfl (simp normal form for `![a, b, c] i`). -/
lemma vec3_zero {α : Type*} (a b c : α) : ![a, b, c] 0 = a := rfl
lemma vec3_one {α : Type*} (a b c : α) : ![a, b, c] 1 = b := rfl
lemma vec3_two {α : Type*} (a b c : α) : ![a, b, c] 2 = c := rfl

lemma P0_stochastic : IsStochastic P0 := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> norm_num [P0]
  · fin_cases i <;> norm_num [P0, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_one, Matrix.head_cons]

lemma P0_irreducible : IsIrreducible P0 := by
  intro i j
  refine ⟨1, ?_⟩
  rw [pow_one]
  fin_cases i <;> fin_cases j <;> norm_num [P0]

lemma π0_stationary : IsStationary P0 π0 := by
  refine ⟨?_, fun j => ?_⟩
  · norm_num [Fin.sum_univ_three, vec3_zero, vec3_one, vec3_two, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_one, Matrix.head_cons, π0]
  · fin_cases j <;> norm_num [Fin.sum_univ_three, vec3_zero, vec3_one, vec3_two, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_one, Matrix.head_cons, π0, P0]

/-- E_0[T_0^+] = 23/8, witnessed by the hitting times h = (0, 7/2, 4). -/
lemma P0_expReturn : ExpReturn P0 0 (23/8) := by
  refine ⟨![0, 7/2, 4], ⟨by simp, ?_⟩, ?_⟩
  · intro y hy
    fin_cases y
    · exact absurd rfl hy
    · norm_num [Fin.sum_univ_three, vec3_zero, vec3_one, vec3_two, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_one, Matrix.head_cons, P0]
    · norm_num [Fin.sum_univ_three, vec3_zero, vec3_one, vec3_two, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_one, Matrix.head_cons, P0]
  · norm_num [Fin.sum_univ_three, vec3_zero, vec3_one, vec3_two, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_one, Matrix.head_cons, P0]

/-- The characteristic polynomial of P0 evaluated at t is t (t - 1) (t - 7/30). -/
lemma P0_charpoly_eval (t : ℂ) :
    (P0.map (fun a : ℝ => (a : ℂ))).charpoly.eval t = t * (t - 1) * (t - 7/30) := by
  rw [Matrix.eval_charpoly, Matrix.det_fin_three]
  simp [P0, Matrix.scalar_apply]
  ring

lemma mem_eigenvalues_P0 (μ : ℂ) : μ ∈ eigenvalues P0 ↔ μ = 0 ∨ μ = 1 ∨ μ = 7/30 := by
  unfold eigenvalues
  rw [Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero, Polynomial.IsRoot.def,
    P0_charpoly_eval]
  simp [mul_eq_zero, sub_eq_zero, or_assoc]

/-- The spectral gap of P0 is 23/30 (eigenvalues 1, 7/30, 0). -/
lemma spectralGap_P0 : spectralGap P0 = 23/30 := by
  have hS : {r : ℝ | ∃ μ ∈ eigenvalues P0, μ ≠ 1 ∧ r = ‖μ‖} = {0, 7/30} := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨μ, hμ, hne, rfl⟩
      rcases (mem_eigenvalues_P0 μ).1 hμ with rfl | rfl | rfl
      · left; simp
      · exact absurd rfl hne
      · right
        have : ((7/30 : ℂ)) = ((7/30 : ℝ) : ℂ) := by push_cast; rfl
        rw [this, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
    · rintro (rfl | rfl)
      · exact ⟨0, (mem_eigenvalues_P0 0).2 (Or.inl rfl), by norm_num, by simp⟩
      · refine ⟨7/30, (mem_eigenvalues_P0 _).2 (Or.inr (Or.inr rfl)), by norm_num, ?_⟩
        have : ((7/30 : ℂ)) = ((7/30 : ℝ) : ℂ) := by push_cast; rfl
        rw [this, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
  unfold spectralGap
  rw [hS, csSup_pair]
  norm_num

/-! ## Refutation -/

/-- The counterexample instance: for c ≠ 0 the formula fails at P0, state 0. -/
lemma P0_no_correction (c : ℝ) (hc : c ≠ 0) : ¬ (23/8 : ℝ) = 1 / π0 0 + c / spectralGap P0 := by
  intro h
  rw [spectralGap_P0] at h
  have h1 : (1 : ℝ) / π0 0 = 23/8 := by norm_num [π0]
  have h2 : c / (23/30 : ℝ) = 0 := by linarith
  rcases div_eq_zero_iff.1 h2 with h3 | h3
  · exact hc h3
  · norm_num at h3

/-- The conjectured formula is false: it fails for P0 at state 0. -/
theorem conjecture_00000005399_fails : ¬ ClaimedFormula := by
  intro H
  obtain ⟨c, hc, hEq⟩ := H 3 P0 P0_stochastic P0_irreducible π0 π0_stationary 0 (23/8)
    P0_expReturn
  exact P0_no_correction c hc hEq

/-- Even the uniform reading (a single constant c for all chains) is false. -/
theorem conjecture_00000005399_uniform_fails : ¬ ClaimedUniformFormula := by
  rintro ⟨c, hc, H⟩
  exact P0_no_correction c hc (H 3 P0 P0_stochastic P0_irreducible π0 π0_stationary 0 (23/8)
    P0_expReturn)

end TLMC5399

#print axioms TLMC5399.conjecture_00000005399_fails
#print axioms TLMC5399.conjecture_00000005399_uniform_fails
