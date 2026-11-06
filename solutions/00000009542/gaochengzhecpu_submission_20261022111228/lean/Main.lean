import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Matrix.Notation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Tactic
open Matrix
open scoped Matrix.L2OpNorm BigOperators ComplexConjugate ComplexOrder Kronecker
noncomputable section
namespace Conjecture9542
set_option maxHeartbeats 1500000
set_option maxRecDepth 2000

def entropy {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (cfc Real.negMulLog A)).re


theorem re_sum {α : Type*} (s : Finset α) (f : α → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re :=
  map_sum Complex.reAddGroupHom f s

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem entropy_eigenvalues {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    entropy A = ∑ i, Real.negMulLog (hA.eigenvalues i) := by
  unfold entropy
  rw [hA.cfc_eq]
  unfold Matrix.IsHermitian.cfc
  rw [Matrix.trace_mul_cycle]
  simp only [unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal,
    Function.comp_apply, re_sum, RCLike.ofReal_re]
  rfl

omit [DecidableEq n] in
theorem entropy_doubly_stochastic (w : n → n → ℝ) (lam mu : n → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hr : ∀ i, ∑ j, w i j = 1)
    (hc : ∀ j, ∑ i, w i j = 1) (hlam : ∀ j, 0 ≤ lam j)
    (hmu : ∀ i, mu i = ∑ j, w i j * lam j) :
    ∑ j, Real.negMulLog (lam j) ≤ ∑ i, Real.negMulLog (mu i) := by
  have hj (i : n) : ∑ j, w i j * Real.negMulLog (lam j) ≤ Real.negMulLog (mu i) := by
    rw [hmu]
    simpa only [Finset.mem_univ, Finset.sum_const_zero, Finset.sum_filter, smul_eq_mul] using
      Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
        (w := w i) (p := lam) (fun j _ => hw i j) (hr i) (fun j _ => hlam j)
  calc
    _ = ∑ j, (∑ i, w i j) * Real.negMulLog (lam j) := by simp only [hc, one_mul]
    _ = ∑ i, ∑ j, w i j * Real.negMulLog (lam j) := by
      simp only [Finset.sum_mul]
      exact Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum fun i _ => hj i

omit [DecidableEq n] in
theorem row_normSq (X : Matrix n n ℂ) (i : n) :
    ∑ j, Complex.normSq (X i j) = ((X * Xᴴ) i i).re := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, re_sum,
    Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

omit [DecidableEq n] in
theorem column_normSq (X : Matrix n n ℂ) (j : n) :
    ∑ i, Complex.normSq (X i j) = ((Xᴴ * X) j j).re := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, re_sum,
    Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

theorem diag_weighted (X : Matrix n n ℂ) (lam : n → ℝ) (i : n) :
    ((X * Matrix.diagonal (fun j => (lam j : ℂ)) * Xᴴ) i i).re =
      ∑ j, Complex.normSq (X i j) * lam j := by
  change (∑ j, (X * Matrix.diagonal (fun k => (lam k : ℂ))) i j * star (X i j)).re = _
  simp only [Matrix.mul_diagonal, re_sum, Complex.star_def]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring


theorem entropy_le_of_two_kraus_eigenbasis {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (X Y : Matrix n n ℂ)
    (hr : X * Xᴴ + Y * Yᴴ = 1) (hc : Xᴴ * X + Yᴴ * Y = 1)
    (hD : Matrix.diagonal (fun i => (hB.1.eigenvalues i : ℂ)) =
      X * Matrix.diagonal (fun j => (hA.1.eigenvalues j : ℂ)) * Xᴴ +
      Y * Matrix.diagonal (fun j => (hA.1.eigenvalues j : ℂ)) * Yᴴ) :
    entropy A ≤ entropy B := by
  rw [entropy_eigenvalues hA.1, entropy_eigenvalues hB.1]
  apply entropy_doubly_stochastic
    (fun i j => Complex.normSq (X i j) + Complex.normSq (Y i j))
    hA.1.eigenvalues hB.1.eigenvalues
  · intro i j
    exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  · intro i
    rw [Finset.sum_add_distrib, row_normSq, row_normSq]
    have hh := congrArg (fun M : Matrix n n ℂ => (M i i).re) hr
    simpa only [Matrix.add_apply, Complex.add_re, Matrix.one_apply_eq, Complex.one_re] using hh
  · intro j
    rw [Finset.sum_add_distrib, column_normSq, column_normSq]
    have hh := congrArg (fun M : Matrix n n ℂ => (M j j).re) hc
    simpa only [Matrix.add_apply, Complex.add_re, Matrix.one_apply_eq, Complex.one_re] using hh
  · exact hA.eigenvalues_nonneg
  · intro i
    have hh := congrArg (fun M : Matrix n n ℂ => (M i i).re) hD
    simp only [Matrix.diagonal_apply_eq, Complex.ofReal_re, Matrix.add_apply,
      Complex.add_re, diag_weighted] at hh
    rw [hh, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring

def pinch (P Q A : Matrix n n ℂ) : Matrix n n ℂ := P * A * Pᴴ + Q * A * Qᴴ

theorem entropy_le_pinch {A P Q : Matrix n n ℂ} (hA : A.PosSemidef)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (hP2 : P * P = P) (hQ2 : Q * Q = Q) (hPQ : P + Q = 1) :
    entropy A ≤ entropy (pinch P Q A) := by
  have hB : (pinch P Q A).PosSemidef :=
    (hA.mul_mul_conjTranspose_same P).add (hA.mul_mul_conjTranspose_same Q)
  let U : Matrix n n ℂ := hA.1.eigenvectorUnitary
  let V : Matrix n n ℂ := hB.1.eigenvectorUnitary
  have hUU : U * Uᴴ = 1 := unitary.coe_mul_star_self hA.1.eigenvectorUnitary
  have hUU' : Uᴴ * U = 1 := unitary.coe_star_mul_self hA.1.eigenvectorUnitary
  have hVV : V * Vᴴ = 1 := unitary.coe_mul_star_self hB.1.eigenvectorUnitary
  have hVV' : Vᴴ * V = 1 := unitary.coe_star_mul_self hB.1.eigenvectorUnitary
  let X := Vᴴ * P * U
  let Y := Vᴴ * Q * U
  apply entropy_le_of_two_kraus_eigenbasis hA hB X Y
  · calc
      _ = Vᴴ * (P * (U * Uᴴ) * P + Q * (U * Uᴴ) * Q) * V := by
        simp only [X, Y, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          hP.eq, hQ.eq]
        noncomm_ring
      _ = Vᴴ * (P + Q) * V := by rw [hUU]; simp only [mul_one, hP2, hQ2]
      _ = 1 := by rw [hPQ, mul_one, hVV']
  · calc
      _ = Uᴴ * (P * (V * Vᴴ) * P + Q * (V * Vᴴ) * Q) * U := by
        simp only [X, Y, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          hP.eq, hQ.eq]
        noncomm_ring
      _ = Uᴴ * (P + Q) * U := by rw [hVV]; simp only [mul_one, hP2, hQ2]
      _ = 1 := by rw [hPQ, mul_one, hUU']
  · have hspecA : A = U * Matrix.diagonal (fun j => (hA.1.eigenvalues j : ℂ)) * Uᴴ :=
      hA.1.spectral_theorem
    have hspecB : Vᴴ * pinch P Q A * V =
        Matrix.diagonal (fun j => (hB.1.eigenvalues j : ℂ)) :=
      hB.1.star_mul_self_mul_eq_diagonal
    rw [← hspecB, pinch]
    conv_lhs => rw [hspecA]
    simp only [X, Y, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hP.eq, hQ.eq]
    noncomm_ring


def diagonalHom : (n → ℂ) →⋆ₐ[ℝ] Matrix n n ℂ :=
  { Matrix.diagonalAlgHom (n := n) (α := ℂ) ℝ with
    map_star' p := by
      change Matrix.diagonal (star p) = (Matrix.diagonal p)ᴴ
      exact (Matrix.diagonal_conjTranspose p).symm }

theorem entropy_diagonal (p : n → ℝ) :
    entropy (Matrix.diagonal (fun i => (p i : ℂ))) = ∑ i, Real.negMulLog (p i) := by
  let pc : n → ℂ := fun i => p i
  have hpc : _root_.IsSelfAdjoint pc := by
    ext i
    simp [pc]
  have hdiag : _root_.IsSelfAdjoint (diagonalHom pc) := by
    change (Matrix.diagonal pc).IsHermitian
    simpa only [Matrix.IsHermitian, Matrix.diagonal_conjTranspose] using
      congrArg Matrix.diagonal hpc
  have hh := (diagonalHom (n := n)).map_cfc Real.negMulLog pc
    Real.continuous_negMulLog.continuousOn
    (show Continuous (diagonalHom (n := n)) from
      diagonalHom.toLinearMap.continuous_of_finiteDimensional) hpc hdiag
  unfold entropy
  change (Matrix.trace (cfc Real.negMulLog (diagonalHom pc))).re = _
  rw [← hh]
  change (Matrix.trace (Matrix.diagonal (cfc Real.negMulLog pc))).re = _
  rw [Matrix.trace_diagonal, re_sum]
  have hpi := cfc_map_pi (S := ℂ) Real.negMulLog pc Real.continuous_negMulLog.continuousOn hpc
    (fun i => by change star (pc i) = pc i; simp [pc])
  rw [hpi]
  apply Finset.sum_congr rfl
  intro i _
  change (cfc Real.negMulLog (algebraMap ℝ ℂ (p i))).re = _
  rw [cfc_algebraMap]
  rfl

variable {m a : Type*} [Fintype m] [DecidableEq m] [Fintype a]

def krausMap (K : a → Matrix m n ℂ) (A : Matrix n n ℂ) : Matrix m m ℂ :=
  ∑ j, K j * A * (K j)ᴴ

def amplify {k : Type*} (φ : Matrix n n ℂ → Matrix m m ℂ)
    (X : Matrix (k × n) (k × n) ℂ) : Matrix (k × m) (k × m) ℂ :=
  fun i j => φ (fun r s => X (i.1,r) (j.1,s)) i.2 j.2

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem amplify_kraus {k : Type*} [Fintype k] [DecidableEq k]
    (K : a → Matrix m n ℂ) (X : Matrix (k × n) (k × n) ℂ) :
    amplify (krausMap K) X =
      ∑ j, (1 ⊗ₖ K j) * X * (1 ⊗ₖ K j)ᴴ := by
  ext i j
  simp [amplify, krausMap, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.kronecker_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Matrix.one_apply, apply_ite]

omit [DecidableEq n] [DecidableEq m] in
theorem kraus_positive (K : a → Matrix m n ℂ) {A : Matrix n n ℂ}
    (hA : A.PosSemidef) : (krausMap K A).PosSemidef := by
  apply Finset.sum_induction
  · intro A B hA hB
    exact hA.add hB
  · exact Matrix.PosSemidef.zero
  · intro j _
    exact hA.mul_mul_conjTranspose_same (K j)

def CompletelyPositive (φ : Matrix n n ℂ → Matrix m m ℂ) : Prop :=
  ∀ k : ℕ, ∀ X : Matrix (Fin k × n) (Fin k × n) ℂ,
    X.PosSemidef → (amplify φ X).PosSemidef

omit [DecidableEq n] [DecidableEq m] in
theorem kraus_completelyPositive (K : a → Matrix m n ℂ) : CompletelyPositive (krausMap K) := by
  intro k X hX
  rw [amplify_kraus]
  exact kraus_positive (fun j => (1 : Matrix (Fin k) (Fin k) ℂ) ⊗ₖ K j) hX


abbrev Input := Fin 3
abbrev Output := Fin 2
abbrev MatIn := Matrix Input Input ℂ
abbrev MatOut := Matrix Output Output ℂ

theorem input_two : (2 : Input) = ⟨2, by decide⟩ := rfl
theorem input_ne20 : (2 : Input) ≠ 0 := by decide
theorem input_ne21 : (2 : Input) ≠ 1 := by decide
theorem input_ne02 : (0 : Input) ≠ 2 := by decide
theorem input_ne12 : (1 : Input) ≠ 2 := by decide

def bit (i j : Input) : Output := if j.val = i.val then 0 else 1

def K (i j : Input) : Matrix Output Input ℂ :=
  fun b k => if b.val = (bit i j).val ∧ k.val = j.val then 1 else 0

def phi (i : Input) (A : MatIn) : MatOut := krausMap (K i) A

theorem phi_formula (i : Input) (A : MatIn) :
    phi i A = Matrix.diagonal ![A i i, Matrix.trace A - A i i] := by
  fin_cases i <;> ext b c <;> fin_cases b <;> fin_cases c <;>
    norm_num [phi, krausMap, K, bit, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_three, Fin.sum_univ_two, Matrix.trace, Matrix.diag, input_two, Fin.isValue, input_ne20, input_ne21, input_ne02, input_ne12, Matrix.diagonal_apply, Matrix.one_apply]
  all_goals first | rfl | (simp only [input_two]; ring)

theorem phi_trace (i : Input) (A : MatIn) : Matrix.trace (phi i A) = Matrix.trace A := by
  rw [phi_formula, Matrix.trace_diagonal]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem phi_CP (i : Input) : CompletelyPositive (phi i) := kraus_completelyPositive (K i)

def channel (i : Input) : MatIn →ₗ[ℂ] MatOut where
  toFun := phi i
  map_add' A B := by simp [phi, krausMap, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c A := by simp [phi, krausMap, mul_smul_comm, smul_mul_assoc, Finset.smul_sum]

def select (i : Input) : MatIn := Matrix.diagonal (fun j => if j.val = i.val then 1 else 0)
def reject (i : Input) : MatIn := 1 - select i

theorem select_hermitian (i : Input) : (select i).IsHermitian := by
  unfold select
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  ext j
  by_cases h : j.val = i.val <;> simp [h]

theorem reject_hermitian (i : Input) : (reject i).IsHermitian :=
  Matrix.isHermitian_one.sub (select_hermitian i)

theorem select_idempotent (i : Input) : select i * select i = select i := by
  unfold select
  rw [Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext j
  by_cases h : j.val = i.val <;> simp [h]

theorem reject_idempotent (i : Input) : reject i * reject i = reject i := by
  dsimp [reject]
  calc
    _ = 1 - select i - select i + select i * select i := by noncomm_ring
    _ = 1 - select i := by rw [select_idempotent]; abel

def complement (i : Input) (A : MatIn) : MatIn := pinch (select i) (reject i) A

theorem entropy_le_complement (i : Input) {A : MatIn} (hA : A.PosSemidef) :
    entropy A ≤ entropy (complement i A) :=
  entropy_le_pinch hA (select_hermitian i) (reject_hermitian i)
    (select_idempotent i) (reject_idempotent i) (by simp [reject])

def mutualInformation (i : Input) (A : MatIn) : ℝ :=
  entropy A + entropy (phi i A) - entropy (complement i A)

theorem mutualInformation_le_outputEntropy (i : Input) {A : MatIn} (hA : A.PosSemidef) :
    mutualInformation i A ≤ entropy (phi i A) := by
  have hh := entropy_le_complement i hA
  unfold mutualInformation
  linarith


def stinespring (i : Input) : Matrix (Output × Input) Input ℂ :=
  fun bj k => if bj.2.val = k.val ∧ bj.1.val = (bit i k).val then 1 else 0

def traceEnvironment (X : Matrix (Output × Input) (Output × Input) ℂ) : MatOut :=
  fun b c => ∑ j, X (b,j) (c,j)

def traceOutput (X : Matrix (Output × Input) (Output × Input) ℂ) : MatIn :=
  fun j k => ∑ b, X (b,j) (b,k)

theorem stinespring_isometry (i : Input) : (stinespring i)ᴴ * stinespring i = 1 := by
  fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;>
    norm_num [stinespring, bit, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two, Input, Output, input_two, Fin.isValue, input_ne20, input_ne21, input_ne02, input_ne12, Matrix.diagonal_apply, Matrix.one_apply]

theorem stinespring_channel (i : Input) (A : MatIn) :
    traceEnvironment (stinespring i * A * (stinespring i)ᴴ) = phi i A := by
  rw [phi_formula]
  fin_cases i <;> ext b c <;> fin_cases b <;> fin_cases c <;>
    norm_num [traceEnvironment, stinespring, bit, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.trace, Matrix.diag,
      Input, Output, input_two, Fin.isValue, input_ne20, input_ne21, input_ne02, input_ne12, Matrix.diagonal_apply, Matrix.one_apply]
  all_goals first | rfl | (simp only [input_two]; ring)

theorem stinespring_complement (i : Input) (A : MatIn) :
    traceOutput (stinespring i * A * (stinespring i)ᴴ) = complement i A := by
  fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;>
    norm_num [traceOutput, stinespring, bit, complement, pinch, select, reject,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Fin.sum_univ_three, Fin.sum_univ_two, Input, Output, input_two, Fin.isValue, input_ne20, input_ne21, input_ne02, input_ne12, Matrix.diagonal_apply, Matrix.one_apply]

  all_goals rfl

structure State where
  val : MatIn
  positive : val.PosSemidef
  trace_one : Matrix.trace val = 1

def probability (ρ : State) (i : Input) : ℝ := (ρ.val i i).re

theorem probability_nonneg (ρ : State) (i : Input) : 0 ≤ probability ρ i := by
  have hh := ρ.positive.re_dotProduct_nonneg (Pi.single i 1)
  simpa [probability, ← Pi.single_star] using hh

theorem probability_sum (ρ : State) : ∑ i, probability ρ i = 1 := by
  have hh := congrArg Complex.re ρ.trace_one
  simpa only [Matrix.trace, Matrix.diag, re_sum, probability, Complex.one_re] using hh

theorem probability_le_one (ρ : State) (i : Input) : probability ρ i ≤ 1 := by
  rw [← probability_sum ρ]
  exact Finset.single_le_sum (fun j _ => probability_nonneg ρ j) (Finset.mem_univ i)

theorem phi_state_formula (ρ : State) (i : Input) :
    phi i ρ.val = Matrix.diagonal (fun b => ((![probability ρ i, 1-probability ρ i] b) : ℂ)) := by
  rw [phi_formula, ρ.trace_one, ← ρ.positive.1.coe_re_apply_self i]
  ext b c
  fin_cases b <;> fin_cases c <;> simp [probability]

theorem outputEntropy (ρ : State) (i : Input) :
    entropy (phi i ρ.val) = Real.binEntropy (probability ρ i) := by
  rw [phi_state_formula, entropy_diagonal]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

theorem mutualInformation_le_binEntropy (ρ : State) (i : Input) :
    mutualInformation i ρ.val ≤ Real.binEntropy (probability ρ i) := by
  rw [← outputEntropy]
  exact mutualInformation_le_outputEntropy i ρ.positive

theorem mutualInformation_le_log_two (ρ : State) (i : Input) :
    mutualInformation i ρ.val ≤ Real.log 2 :=
  (mutualInformation_le_binEntropy ρ i).trans Real.binEntropy_le_log_two

theorem small_probability (ρ : State) : ∃ i : Input, probability ρ i ≤ 1/3 := by
  by_contra! h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have hh := probability_sum ρ
  simp only [Fin.sum_univ_three] at hh
  linarith

theorem exists_small_information (ρ : State) :
    ∃ i : Input, mutualInformation i ρ.val ≤ Real.binEntropy (1/3) := by
  obtain ⟨i, hi⟩ := small_probability ρ
  refine ⟨i, (mutualInformation_le_binEntropy ρ i).trans ?_⟩
  apply Real.binEntropy_strictMonoOn.monotoneOn
    ⟨probability_nonneg ρ i, hi.trans (by norm_num)⟩ (by norm_num) hi

theorem entropy_gap : Real.binEntropy (1/3) < Real.log 2 :=
  Real.binEntropy_lt_log_two.mpr (by norm_num)


def diagonalState (p : Input → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) : State where
  val := Matrix.diagonal (fun i => (p i : ℂ))
  positive := Matrix.PosSemidef.diagonal fun i => by
    exact RCLike.ofReal_nonneg.mpr (hp i)
  trace_one := by rw [Matrix.trace_diagonal]; exact_mod_cast hsum

theorem probability_diagonalState (p : Input → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (i : Input) : probability (diagonalState p hp hsum) i = p i := by
  simp [probability, diagonalState]

theorem reject_diagonal (i : Input) :
    reject i = Matrix.diagonal (fun j => if j.val = i.val then 0 else 1) := by
  unfold reject select
  rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  apply congrArg Matrix.diagonal
  funext j
  by_cases h : j.val = i.val <;> simp [h]

theorem complement_diagonal (i : Input) (p : Input → ℂ) :
    complement i (Matrix.diagonal p) = Matrix.diagonal p := by
  unfold complement pinch
  rw [(select_hermitian i).eq, (reject_hermitian i).eq, select, reject_diagonal]
  simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_add]
  apply congrArg Matrix.diagonal
  funext j
  by_cases h : j.val = i.val <;> simp [h]

theorem mutualInformation_diagonalState (p : Input → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (i : Input) :
    mutualInformation i (diagonalState p hp hsum).val = Real.binEntropy (p i) := by
  unfold mutualInformation
  change entropy (Matrix.diagonal _) + entropy (phi i (diagonalState p hp hsum).val) -
    entropy (complement i (Matrix.diagonal _)) = _
  rw [complement_diagonal]
  have hh := outputEntropy (diagonalState p hp hsum) i
  rw [probability_diagonalState] at hh
  linarith

def uniformState : State := diagonalState (fun _ => 1/3) (by intro; norm_num)
  (by norm_num [Fin.sum_univ_three])

theorem uniformInformation (i : Input) :
    mutualInformation i uniformState.val = Real.binEntropy (1/3) :=
  mutualInformation_diagonalState _ _ _ i

def optimalState (i : Input) : State :=
  diagonalState (fun j => if j.val = i.val then 1/2 else 1/4)
    (by intro j; dsimp; split_ifs <;> norm_num)
    (by fin_cases i <;> norm_num [Fin.sum_univ_three, input_two, input_ne20, input_ne21])

theorem optimalInformation (i : Input) : mutualInformation i (optimalState i).val = Real.log 2 := by
  unfold optimalState
  rw [mutualInformation_diagonalState]
  simp only [ite_true]
  exact Real.binEntropy_eq_log_two.mpr (by norm_num)

def worstInformation (ρ : State) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i : Input => mutualInformation i ρ.val)

def compoundSingleLetter : ℝ := sSup (Set.range worstInformation)
def individualSingleLetter (i : Input) : ℝ := sSup (Set.range (fun ρ : State => mutualInformation i ρ.val))

theorem worstInformation_le (ρ : State) : worstInformation ρ ≤ Real.binEntropy (1/3) := by
  obtain ⟨i, hi⟩ := exists_small_information ρ
  exact (Finset.inf'_le _ (Finset.mem_univ i)).trans hi

theorem worst_uniform : worstInformation uniformState = Real.binEntropy (1/3) := by
  simp [worstInformation, uniformInformation]

theorem compound_value : compoundSingleLetter = Real.binEntropy (1/3) := by
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · exact ⟨worstInformation uniformState, ⟨uniformState, rfl⟩⟩
  · rintro x ⟨ρ, rfl⟩
    exact worstInformation_le ρ
  · intro b hb
    exact ⟨worstInformation uniformState, ⟨uniformState, rfl⟩, by rwa [worst_uniform]⟩

theorem individual_value (i : Input) : individualSingleLetter i = Real.log 2 := by
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · exact ⟨mutualInformation i (optimalState i).val, ⟨optimalState i, rfl⟩⟩
  · rintro x ⟨ρ, rfl⟩
    exact mutualInformation_le_log_two ρ i
  · intro b hb
    exact ⟨mutualInformation i (optimalState i).val, ⟨optimalState i, rfl⟩,
      by rwa [optimalInformation]⟩

theorem strict_minimax_gap :
    compoundSingleLetter < Finset.univ.inf' Finset.univ_nonempty individualSingleLetter := by
  rw [compound_value]
  simpa [individual_value] using entropy_gap


theorem channel_CPTP (i : Input) :
    CompletelyPositive (channel i) ∧ ∀ A : MatIn, Matrix.trace (channel i A) = Matrix.trace A :=
  ⟨phi_CP i, phi_trace i⟩

theorem complement_CP (i : Input) : CompletelyPositive (complement i) := by
  have hh : complement i = krausMap ![select i, reject i] := by
    funext A
    simp [complement, pinch, krausMap, Fin.sum_univ_two]
  rw [hh]
  exact kraus_completelyPositive _

theorem complement_trace (i : Input) (A : MatIn) :
    Matrix.trace (complement i A) = Matrix.trace A := by
  unfold complement pinch
  rw [(select_hermitian i).eq, (reject_hermitian i).eq, Matrix.trace_add,
    Matrix.trace_mul_cycle (select i) A (select i),
    Matrix.trace_mul_cycle (reject i) A (reject i), select_idempotent, reject_idempotent,
    ← Matrix.trace_add, ← Matrix.add_mul]
  simp [reject]

theorem phi_state (i : Input) (ρ : State) :
    (phi i ρ.val).PosSemidef ∧ Matrix.trace (phi i ρ.val) = 1 :=
  ⟨kraus_positive (K i) ρ.positive, by rw [phi_trace, ρ.trace_one]⟩

theorem complement_state (i : Input) (ρ : State) :
    (complement i ρ.val).PosSemidef ∧ Matrix.trace (complement i ρ.val) = 1 :=
  ⟨(ρ.positive.mul_mul_conjTranspose_same (select i)).add
    (ρ.positive.mul_mul_conjTranspose_same (reject i)), by rw [complement_trace, ρ.trace_one]⟩

#print axioms entropy_eigenvalues
#print axioms entropy_le_pinch
#print axioms entropy_diagonal
#print axioms channel_CPTP
#print axioms stinespring_isometry
#print axioms stinespring_channel
#print axioms stinespring_complement
#print axioms mutualInformation_le_binEntropy
#print axioms compound_value
#print axioms individual_value
#print axioms strict_minimax_gap

end Conjecture9542








