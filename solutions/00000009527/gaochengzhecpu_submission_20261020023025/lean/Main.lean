import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Complex.Module
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped Matrix BigOperators ComplexOrder
namespace Conjecture9527
noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
abbrev Q := Matrix (Fin 2) (Fin 2) ℂ

def diagonal (p q : ℝ) : Q := Matrix.diagonal ![(p : ℂ), (q : ℂ)]

def Density (A : Q) : Prop := A.PosSemidef ∧ Matrix.trace A = 1

/-- Spectral von Neumann entropy, in nats; only its Hermitian branch is used. -/
noncomputable def entropy (A : Q) : ℝ :=
  if h : A.IsHermitian then ∑ i, Real.negMulLog (h.eigenvalues i) else 0

lemma diagonal_hermitian (p q : ℝ) : (diagonal p q).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal, Matrix.conjTranspose_apply]

lemma eigenvalue_diagonal (p q : ℝ) (i : Fin 2) :
    (diagonal_hermitian p q).eigenvalues i = p ∨
    (diagonal_hermitian p q).eigenvalues i = q := by
  have hs := (diagonal_hermitian p q).eigenvalues_mem_spectrum_real i
  have hc : ((diagonal_hermitian p q).eigenvalues i : ℂ) ∈ spectrum ℂ (diagonal p q) :=
    (spectrum.algebraMap_mem_iff ℂ).mpr hs
  change ((diagonal_hermitian p q).eigenvalues i : ℂ) ∈ spectrum ℂ (Matrix.diagonal ![(p : ℂ), (q : ℂ)]) at hc
  rw [spectrum_diagonal] at hc
  obtain ⟨j, hj⟩ := hc
  fin_cases j
  · exact Or.inl (Complex.ofReal_injective hj.symm)
  · exact Or.inr (Complex.ofReal_injective hj.symm)

lemma eigenvalue_sum (p q : ℝ) :
    (diagonal_hermitian p q).eigenvalues 0 +
    (diagonal_hermitian p q).eigenvalues 1 = p + q := by
  have ht := congrArg Matrix.trace (diagonal_hermitian p q).star_mul_self_mul_eq_diagonal
  rw [Matrix.trace_mul_cycle] at ht
  simp only [← mul_assoc, ← unitary.coe_star, unitary.coe_mul_star_self, one_mul] at ht
  have hr := congrArg Complex.re ht
  simpa [Matrix.trace, diagonal, Fin.sum_univ_two] using hr.symm

lemma entropy_diagonal (p q : ℝ) :
    entropy (diagonal p q) = Real.negMulLog p + Real.negMulLog q := by
  simp only [entropy, dif_pos (diagonal_hermitian p q), Fin.sum_univ_two]
  have h := eigenvalue_sum p q
  rcases eigenvalue_diagonal p q 0 with h0 | h0 <;>
    rcases eigenvalue_diagonal p q 1 with h1 | h1
  · rw [h0, h1] at h ⊢
    have : p = q := by linarith
    rw [this]
  · rw [h0, h1]
  · rw [h0, h1, add_comm]
  · rw [h0, h1] at h ⊢
    have : q = p := by linarith
    rw [this]


/-- A finite ensemble of actual density matrices; zero-probability labels are allowed. -/
structure Ensemble (n : ℕ) where
  weight : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  total : ∑ i, weight i = 1
  state : Fin n → Q
  density : ∀ i, Density (state i)

/-- The channel's Holevo information on a finite input ensemble. -/
noncomputable def holevo {n : ℕ} (E : Ensemble n) (Φ : Q → Q) : ℝ :=
  entropy (∑ i, E.weight i • Φ (E.state i)) -
    ∑ i, E.weight i * entropy (Φ (E.state i))

def LessNoisy (Φ Ψ : Q → Q) : Prop :=
  ∀ (n : ℕ) (E : Ensemble n), holevo E Φ ≤ holevo E Ψ

/-- Matrix units used as genuine Kraus operators below. -/
def unit (a b : Fin 2) : Q := fun i j => if i = a ∧ j = b then 1 else 0

def dephase (A : Q) : Q := Matrix.diagonal (fun i => A i i)
def reset (a : Fin 2) (A : Q) : Q := Matrix.trace A • unit a a

def depolarize (A : Q) : Q := (Matrix.trace A / 2) • (1 : Q)

/-- A finite Kraus certificate for a completely positive trace-preserving map. -/
def KrausCPTP (Φ : Q → Q) : Prop :=
  ∃ (m : ℕ) (K : Fin m → Q),
    (∑ i, (K i)ᴴ * K i) = 1 ∧
    ∀ A, Φ A = ∑ i, K i * A * (K i)ᴴ

lemma dephase_kraus : KrausCPTP dephase := by
  refine ⟨2, fun i => unit i i, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Fin.sum_univ_two, unit, Matrix.mul_apply, Matrix.conjTranspose_apply]
  · intro A
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dephase, Fin.sum_univ_two, unit, Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma reset_kraus (a : Fin 2) : KrausCPTP (reset a) := by
  refine ⟨2, fun i => unit a i, ?_, ?_⟩
  · ext i j
    fin_cases a <;> fin_cases i <;> fin_cases j <;>
      norm_num [Fin.sum_univ_two, unit, Matrix.mul_apply, Matrix.conjTranspose_apply]
  · intro A
    ext i j
    fin_cases a <;> fin_cases i <;> fin_cases j <;>
      simp [reset, Matrix.trace, Fin.sum_univ_two, unit,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply]

lemma depolarize_kraus : KrausCPTP depolarize := by
  refine ⟨8, fun i => (1 / 2 : ℂ) • unit (if i.val < 4 then 0 else 1)
    (if i.val % 4 < 2 then 0 else 1), ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Fin.sum_univ_succ, unit, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.smul_apply]
  · intro A
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [depolarize, Matrix.trace, Fin.sum_univ_succ, unit, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.smul_apply] <;> ring

lemma density_diag_real {A : Q} (h : Density A) (i : Fin 2) :
    A i i = ((A i i).re : ℂ) := by
  have ht := congrFun (congrFun h.1.1 i) i
  apply Complex.ext
  · rfl
  · have hi := congrArg Complex.im ht
    simp [Matrix.conjTranspose_apply] at hi
    simp only [Complex.ofReal_im]
    linarith

lemma density_diag_nonneg {A : Q} (h : Density A) (i : Fin 2) :
    0 ≤ (A i i).re := by
  fin_cases i <;> simpa [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Pi.single_apply] using
    h.1.re_dotProduct_nonneg (Pi.single _ 1)

lemma dephase_density {A : Q} (h : Density A) :
    dephase A = diagonal (A 0 0).re (A 1 1).re := by
  unfold dephase diagonal
  apply congrArg Matrix.diagonal
  funext i
  fin_cases i <;> exact density_diag_real h _

lemma depolarize_density {A : Q} (h : Density A) :
    depolarize A = diagonal (1/2) (1/2) := by
  rw [depolarize, h.2]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [diagonal]

lemma reset_density {A : Q} (h : Density A) (a : Fin 2) :
    reset a A = unit a a := by simp [reset, h.2]

lemma weighted_constant {n : ℕ} (E : Ensemble n) (A : Q) :
    (∑ i, E.weight i • A) = A := by rw [← Finset.sum_smul, E.total, one_smul]

lemma constant_holevo {n : ℕ} (E : Ensemble n) (Φ : Q → Q) (A : Q)
    (h : ∀ i, Φ (E.state i) = A) : holevo E Φ = 0 := by
  simp_rw [holevo, h]
  rw [weighted_constant, ← Finset.sum_mul, E.total, one_mul, sub_self]

lemma holevo_depolarize {n : ℕ} (E : Ensemble n) : holevo E depolarize = 0 :=
  constant_holevo E _ _ (fun i => depolarize_density (E.density i))

lemma holevo_reset {n : ℕ} (E : Ensemble n) (a : Fin 2) : holevo E (reset a) = 0 :=
  constant_holevo E _ _ (fun i => reset_density (E.density i) a)


lemma weighted_diagonal {n : ℕ} (E : Ensemble n) (p q : Fin n → ℝ) :
    (∑ i, E.weight i • diagonal (p i) (q i)) =
      diagonal (∑ i, E.weight i * p i) (∑ i, E.weight i * q i) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [diagonal, Matrix.sum_apply, Matrix.smul_apply, Complex.ofReal_sum,
      Complex.ofReal_mul, Complex.real_smul]

lemma holevo_dephase_nonneg {n : ℕ} (E : Ensemble n) : 0 ≤ holevo E dephase := by
  let p : Fin n → ℝ := fun i => (E.state i 0 0).re
  let q : Fin n → ℝ := fun i => (E.state i 1 1).re
  have hp : ∀ i, 0 ≤ p i := fun i => density_diag_nonneg (E.density i) 0
  have hq : ∀ i, 0 ≤ q i := fun i => density_diag_nonneg (E.density i) 1
  have jp := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
    (w := E.weight) (p := p) (fun i _ => E.nonneg i) (by simpa using E.total)
    (fun i _ => hp i)
  have jq := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
    (w := E.weight) (p := q) (fun i _ => E.nonneg i) (by simpa using E.total)
    (fun i _ => hq i)
  simp only [smul_eq_mul] at jp jq
  unfold holevo
  simp_rw [dephase_density (E.density _)]
  change 0 ≤ entropy (∑ i, E.weight i • diagonal (p i) (q i)) -
    ∑ i, E.weight i * entropy (diagonal (p i) (q i))
  rw [weighted_diagonal]
  simp_rw [entropy_diagonal, mul_add, Finset.sum_add_distrib]
  linarith

/-- All finite ensembles, with arbitrary (including noncommuting) input density states. -/
lemma depolarize_lessNoisy_dephase : LessNoisy depolarize dephase := by
  intro n E
  rw [holevo_depolarize]
  exact holevo_dephase_nonneg E

lemma unit_density (a : Fin 2) : Density (unit a a) := by
  have hd : unit a a = Matrix.diagonal (fun i => if i = a then (1 : ℂ) else 0) := by
    ext i j
    fin_cases a <;> fin_cases i <;> fin_cases j <;> simp [unit]
  constructor
  · rw [hd]
    exact Matrix.PosSemidef.diagonal (fun i => by split_ifs <;> norm_num)
  · fin_cases a <;> norm_num [unit, Matrix.trace, Fin.sum_univ_two]

noncomputable def orthogonalEnsemble : Ensemble 2 where
  weight := fun _ => 1/2
  nonneg := fun _ => by norm_num
  total := by norm_num [Fin.sum_univ_two]
  state := fun i => unit i i
  density := unit_density

lemma unit_entropy (a : Fin 2) : entropy (unit a a) = 0 := by
  fin_cases a
  · change entropy (unit 0 0) = 0
    have : unit 0 0 = diagonal 1 0 := by ext i j; fin_cases i <;> fin_cases j <;> simp [unit, diagonal]
    rw [this, entropy_diagonal]
    norm_num [Real.negMulLog]
  · change entropy (unit 1 1) = 0
    have : unit 1 1 = diagonal 0 1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [unit, diagonal]
    rw [this, entropy_diagonal]
    norm_num [Real.negMulLog]

lemma dephase_unit (a : Fin 2) : dephase (unit a a) = unit a a := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;> simp [dephase, unit]

lemma orthogonal_average :
    (∑ i, orthogonalEnsemble.weight i • unit i i) = diagonal (1/2) (1/2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [orthogonalEnsemble, Fin.sum_univ_two, unit, diagonal, Complex.real_smul]

lemma orthogonal_holevo_dephase : holevo orthogonalEnsemble dephase = Real.log 2 := by
  unfold holevo
  change entropy (∑ i, orthogonalEnsemble.weight i • dephase (unit i i)) -
    ∑ i, orthogonalEnsemble.weight i * entropy (dephase (unit i i)) = _
  simp_rw [dephase_unit, unit_entropy, mul_zero]
  rw [Finset.sum_const_zero, sub_zero, orthogonal_average, entropy_diagonal]
  norm_num [Real.negMulLog, Real.log_div]
  ring

lemma dephase_not_lessNoisy_depolarize : ¬ LessNoisy dephase depolarize := by
  intro h
  have hh := h 2 orthogonalEnsemble
  rw [orthogonal_holevo_dephase, holevo_depolarize] at hh
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).not_le hh

/-- A strict successor in the source's actual order direction, refuting maximality. -/
theorem depolarize_not_maximal :
    KrausCPTP depolarize ∧ KrausCPTP dephase ∧
    LessNoisy depolarize dephase ∧ ¬ LessNoisy dephase depolarize :=
  ⟨depolarize_kraus, dephase_kraus, depolarize_lessNoisy_dephase,
    dephase_not_lessNoisy_depolarize⟩

lemma reset_lessNoisy (a b : Fin 2) : LessNoisy (reset a) (reset b) := by
  intro n E
  rw [holevo_reset, holevo_reset]

lemma resets_ne : reset 0 ≠ reset 1 := by
  intro h
  have hh := congrFun (congrFun (congrFun h (unit 0 0)) 0) 0
  norm_num [reset, unit, Matrix.trace, Fin.sum_univ_two] at hh

/-- On literal channels (as stated), the relation is not antisymmetric either. -/
theorem not_antisymmetric :
    ∃ Φ Ψ : Q → Q, KrausCPTP Φ ∧ KrausCPTP Ψ ∧
      LessNoisy Φ Ψ ∧ LessNoisy Ψ Φ ∧ Φ ≠ Ψ :=
  ⟨reset 0, reset 1, reset_kraus 0, reset_kraus 1,
    reset_lessNoisy 0 1, reset_lessNoisy 1 0, resets_ne⟩

#print axioms depolarize_not_maximal
#print axioms not_antisymmetric
end
end Conjecture9527




