import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

open Polynomial Finset Set Matrix

namespace TLMC1470

noncomputable section

def node (d : ℕ) (i : Fin (d+1)) : ℝ := (i.val + 1 : ℝ) / (d + 2 : ℝ)

theorem node_pos (d : ℕ) (i : Fin (d+1)) : 0 < node d i := by
  unfold node
  positivity

theorem node_le_one (d : ℕ) (i : Fin (d+1)) : node d i ≤ 1 := by
  unfold node
  apply (div_le_one (by positivity : (0:ℝ) < d+2)).2
  have hi : i.val + 1 ≤ d+1 := i.isLt
  exact_mod_cast (by omega : i.val+1 ≤ d+2)

theorem node_injective (d : ℕ) : Function.Injective (node d) := by
  intro i j h
  unfold node at h
  have hd : (d+2:ℝ) ≠ 0 := by positivity
  have hh := (div_left_inj' hd).mp h
  apply Fin.ext
  exact_mod_cast (add_right_cancel hh)

theorem eval_interpolation (d : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ d) (t : ℝ) :
    p.eval t = ∑ i : Fin (d+1), p.eval (node d i) *
      (Lagrange.basis univ (node d) i).eval t := by
  have hdeg : p.degree < (univ : Finset (Fin (d+1))).card := by
    simp only [card_univ, Fintype.card_fin]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast (show p.natDegree < d+1 by omega))
  have h := Lagrange.eq_interpolate (node_injective d).injOn hdeg
  have hh := congrArg (fun f : ℝ[X] => f.eval t) h
  simpa [Lagrange.interpolate_apply, eval_finsetSum] using hh

theorem uniform_eval_bound (d : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ t ∈ Icc (-1 : ℝ) 0, ∀ p : ℝ[X], p.natDegree ≤ d →
      (p.eval t)^2 ≤ C * ∑ i : Fin (d+1), (p.eval (node d i))^2 := by
  let f : ℝ → ℝ := fun t => ∑ i : Fin (d+1),
    ((Lagrange.basis univ (node d) i).eval t)^2
  have hf : Continuous f := by
    unfold f
    fun_prop
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (-1:ℝ) 0)).bddAbove_image hf.continuousOn
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro t ht p hp
  rw [eval_interpolation d p hp t]
  have hs := sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin (d+1)))
    (fun i => (Lagrange.basis univ (node d) i).eval t)
    (fun i => p.eval (node d i))
  have hbound : f t ≤ max B 1 := (hB (mem_image_of_mem f ht)).trans (le_max_left _ _)
  have hnonneg : 0 ≤ ∑ i : Fin (d+1), (p.eval (node d i))^2 := by positivity
  calc
    (∑ i : Fin (d+1), p.eval (node d i) * (Lagrange.basis univ (node d) i).eval t)^2
      = (∑ i : Fin (d+1), (Lagrange.basis univ (node d) i).eval t * p.eval (node d i))^2 := by
          simp_rw [mul_comm]
    _ ≤ f t * ∑ i : Fin (d+1), (p.eval (node d i))^2 := hs
    _ ≤ max B 1 * ∑ i : Fin (d+1), (p.eval (node d i))^2 := mul_le_mul_of_nonneg_right hbound hnonneg

theorem atomic_parameters (d : ℕ) : ∃ (ε : ℝ) (w : Fin (d+1) → ℝ),
    0 < ε ∧ ε ≤ 1 ∧ (∀ i, 0 < w i) ∧
    -ε + ε^3 * (∑ i, w i * node d i) < 0 ∧
    ∀ p : ℝ[X], p.natDegree ≤ d →
      0 ≤ (-ε)^3 * (p.eval (-ε))^2 +
        ε^3 * ∑ i, w i * (node d i)^3 * (p.eval (node d i))^2 := by
  obtain ⟨C,hC,hbound⟩ := uniform_eval_bound d
  let w : Fin (d+1) → ℝ := fun i => C / (node d i)^3
  have hw : ∀ i, 0 < w i := fun i => div_pos hC (pow_pos (node_pos d i) _)
  let A : ℝ := ∑ i, w i * node d i
  have hA : 0 ≤ A := sum_nonneg fun i _ => le_of_lt (mul_pos (hw i) (node_pos d i))
  let ε : ℝ := 1 / (A+1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by positivity : 0 < A+1)).2 (by linarith)
  have hsmall : ε^2 * A < 1 := by
    have hsq : A < (A+1)^2 := by nlinarith [sq_nonneg A]
    have hden : 0 < (A+1)^2 := by positivity
    calc
      ε^2 * A = A / (A+1)^2 := by
        dsimp [ε]
        rw [div_pow]
        simp only [one_pow]
        ring
      _ < 1 := (div_lt_one hden).2 hsq
  have hneg : -ε + ε^3 * A < 0 := by
    have hmul := mul_lt_mul_of_pos_left hsmall hε
    nlinarith
  refine ⟨ε,w,hε,hε1,hw,hneg,?_⟩
  intro p hp
  have hb := hbound (-ε) (by constructor <;> linarith) p hp
  have hc : ∀ i, w i * (node d i)^3 = C := by
    intro i
    exact div_mul_cancel₀ C (ne_of_gt (pow_pos (node_pos d i) 3))
  simp_rw [hc]
  rw [← mul_sum]
  have hm := mul_nonneg (le_of_lt (pow_pos hε 3)) (sub_nonneg.mpr hb)
  nlinarith

def atomicMass {d : ℕ} (ε : ℝ) (w : Fin (d+1) → ℝ) : ℝ :=
  1 + ε^3 * ∑ i, w i

def atomicFunctional {d : ℕ} (ε : ℝ) (w : Fin (d+1) → ℝ) : ℝ[X] →ₗ[ℝ] ℝ :=
  (atomicMass ε w)⁻¹ • (Polynomial.leval (-ε) +
    ε^3 • ∑ i, w i • Polynomial.leval (node d i))

theorem atomicFunctional_apply {d : ℕ} (ε : ℝ) (w : Fin (d+1) → ℝ) (p : ℝ[X]) :
    atomicFunctional ε w p =
      (p.eval (-ε) + ε^3 * ∑ i, w i * p.eval (node d i)) / atomicMass ε w := by
  simp [atomicFunctional, div_eq_mul_inv, mul_comm]
  ring

theorem atomicMass_pos {d : ℕ} {ε : ℝ} {w : Fin (d+1) → ℝ}
    (hε : 0 < ε) (hw : ∀ i, 0 < w i) : 0 < atomicMass ε w := by
  unfold atomicMass
  exact add_pos_of_pos_of_nonneg zero_lt_one
    (mul_nonneg (le_of_lt (pow_pos hε 3)) (sum_nonneg fun i _ => le_of_lt (hw i)))

theorem atomicFunctional_one {d : ℕ} {ε : ℝ} {w : Fin (d+1) → ℝ}
    (hε : 0 < ε) (hw : ∀ i, 0 < w i) : atomicFunctional ε w 1 = 1 := by
  rw [atomicFunctional_apply]
  simp only [eval_one, mul_one]
  exact div_self (ne_of_gt (atomicMass_pos hε hw))

theorem atomicFunctional_square_nonneg {d : ℕ} {ε : ℝ} {w : Fin (d+1) → ℝ}
    (hε : 0 < ε) (hw : ∀ i, 0 < w i) (p : ℝ[X]) :
    0 ≤ atomicFunctional ε w (p^2) := by
  rw [atomicFunctional_apply]
  simp only [eval_pow]
  apply div_nonneg _ (le_of_lt (atomicMass_pos hε hw))
  exact add_nonneg (sq_nonneg _) (mul_nonneg (le_of_lt (pow_pos hε 3))
    (sum_nonneg fun i _ => mul_nonneg (le_of_lt (hw i)) (sq_nonneg _)))

theorem atomicFunctional_ball_nonneg {d : ℕ} {ε : ℝ} {w : Fin (d+1) → ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hw : ∀ i, 0 < w i) (p : ℝ[X]) :
    0 ≤ atomicFunctional ε w ((1-X^2)*p^2) := by
  rw [atomicFunctional_apply]
  simp only [eval_mul, eval_sub, eval_one, eval_pow, eval_X]
  have he : 0 ≤ 1-(-ε)^2 := by nlinarith
  have hn : ∀ i, 0 ≤ 1-(node d i)^2 := by
    intro i
    have h0 := node_pos d i
    have h1 := node_le_one d i
    nlinarith
  apply div_nonneg _ (le_of_lt (atomicMass_pos hε hw))
  exact add_nonneg (mul_nonneg he (sq_nonneg _))
    (mul_nonneg (le_of_lt (pow_pos hε 3))
      (sum_nonneg fun i _ => mul_nonneg (le_of_lt (hw i)) (mul_nonneg (hn i) (sq_nonneg _))))

theorem exists_atomic_functional (d : ℕ) : ∃ L : ℝ[X] →ₗ[ℝ] ℝ,
    L 1 = 1 ∧ L X < 0 ∧
    (∀ p : ℝ[X], 0 ≤ L (p^2)) ∧
    (∀ p : ℝ[X], 0 ≤ L ((1-X^2)*p^2)) ∧
    (∀ p : ℝ[X], p.natDegree ≤ d → 0 ≤ L (X^3*p^2)) := by
  obtain ⟨ε,w,hε,hε1,hw,hneg,hcubic⟩ := atomic_parameters d
  refine ⟨atomicFunctional ε w, atomicFunctional_one hε hw, ?_,
    atomicFunctional_square_nonneg hε hw,
    atomicFunctional_ball_nonneg hε hε1 hw, ?_⟩
  · rw [atomicFunctional_apply]
    simp only [eval_X]
    exact div_neg_of_neg_of_pos hneg (atomicMass_pos hε hw)
  · intro p hp
    rw [atomicFunctional_apply]
    simp only [eval_mul, eval_pow, eval_X]
    apply div_nonneg _ (le_of_lt (atomicMass_pos hε hw))
    convert hcubic p hp using 1 <;> congr 1
    apply congrArg (fun a => ε^3*a)
    apply sum_congr rfl
    intro i _
    ring


/-- Coefficients in the full monomial basis through degree k. -/
def coefficientPolynomial (k : ℕ) (a : Fin (k+1) → ℝ) : ℝ[X] :=
  ∑ i, C (a i) * X^i.val

theorem coefficientPolynomial_degree (k : ℕ) (a : Fin (k+1) → ℝ) :
    (coefficientPolynomial k a).natDegree ≤ k := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

theorem coefficientPolynomial_coeff (k : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ k) :
    coefficientPolynomial k (fun i => p.coeff i.val) = p := by
  unfold coefficientPolynomial
  change (∑ i : Fin (k+1), C (p.coeff i.val) * X^i.val) = p
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => C (p.coeff i) * X^i) (k+1)).trans
    (p.as_sum_range_C_mul_X_pow' (by omega)).symm

/-- The actual truncated localizing matrix; g=1 is the moment matrix. -/
def localizingMatrix (L : ℝ[X] →ₗ[ℝ] ℝ) (g : ℝ[X]) (k : ℕ) :
    Matrix (Fin (k+1)) (Fin (k+1)) ℝ :=
  fun i j => L (g * X^(i.val+j.val))

def momentMatrix (L : ℝ[X] →ₗ[ℝ] ℝ) (k : ℕ) := localizingMatrix L 1 k

theorem localizingMatrix_hermitian (L : ℝ[X] →ₗ[ℝ] ℝ) (g : ℝ[X]) (k : ℕ) :
    (localizingMatrix L g k).IsHermitian := by
  ext i j
  simp [localizingMatrix, Matrix.conjTranspose_apply, add_comm]

theorem localizingMatrix_quadratic (L : ℝ[X] →ₗ[ℝ] ℝ) (g : ℝ[X])
    (k : ℕ) (a : Fin (k+1) → ℝ) :
    star a ⬝ᵥ (localizingMatrix L g k *ᵥ a) =
      L (g * (coefficientPolynomial k a)^2) := by
  simp only [Matrix.mulVec, dotProduct, localizingMatrix, Pi.star_apply,
    star_trivial, coefficientPolynomial, pow_two, sum_mul, mul_sum, map_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  have hpoly : g * (C (a j) * X^j.val * (C (a i) * X^i.val)) =
      (a j * a i) • (g * X^(j.val+i.val)) := by
    simp only [pow_add, Algebra.smul_def, algebraMap_eq, map_mul]
    ring
  rw [hpoly, map_smul]
  simp only [smul_eq_mul]
  ring

theorem localizingMatrix_psd_iff (L : ℝ[X] →ₗ[ℝ] ℝ) (g : ℝ[X]) (k : ℕ) :
    (localizingMatrix L g k).PosSemidef ↔
      ∀ p : ℝ[X], p.natDegree ≤ k → 0 ≤ L (g*p^2) := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨_, h⟩ p hp
    have hh := h (fun i => p.coeff i.val)
    rwa [localizingMatrix_quadratic, coefficientPolynomial_coeff k p hp] at hh
  · intro h
    refine ⟨localizingMatrix_hermitian L g k, fun a => ?_⟩
    rw [localizingMatrix_quadratic]
    exact h _ (coefficientPolynomial_degree k a)

/-- The prescribed Lasserre moment relaxation, with its true PSD constraints. -/
def MomentFeasible (r : ℕ) (L : ℝ[X] →ₗ[ℝ] ℝ) : Prop :=
  L 1 = 1 ∧ (momentMatrix L r).PosSemidef ∧
    (localizingMatrix L (X^3) (r-2)).PosSemidef ∧
    (localizingMatrix L (1-X^2) (r-1)).PosSemidef

theorem momentFeasible_iff (r : ℕ) (L : ℝ[X] →ₗ[ℝ] ℝ) :
    MomentFeasible r L ↔ L 1=1 ∧
      (∀ p : ℝ[X], p.natDegree ≤ r → 0 ≤ L (p^2)) ∧
      (∀ p : ℝ[X], p.natDegree ≤ r-2 → 0 ≤ L (X^3*p^2)) ∧
      (∀ p : ℝ[X], p.natDegree ≤ r-1 → 0 ≤ L ((1-X^2)*p^2)) := by
  simp [MomentFeasible, momentMatrix, localizingMatrix_psd_iff]

theorem negative_moment_feasible (r : ℕ) :
    ∃ L : ℝ[X] →ₗ[ℝ] ℝ, MomentFeasible r L ∧ L X < 0 := by
  obtain ⟨L,h1,hx,hs,hb,hc⟩ := exists_atomic_functional (r-2)
  exact ⟨L, (momentFeasible_iff r L).2 ⟨h1,fun p _ => hs p,hc,fun p _ => hb p⟩,hx⟩


/-- The actual compact semialgebraic input, with the given defining tuple. -/
def K : Set ℝ := {x | 0 ≤ x^3 ∧ 0 ≤ 1-x^2}

theorem K_eq : K = Set.Icc 0 1 := by
  ext x
  constructor
  · rintro ⟨h3,h2⟩
    have h0 : 0 ≤ x := by
      by_contra h
      have hn : x < 0 := lt_of_not_ge h
      have hm := mul_neg_of_neg_of_pos hn (sq_pos_of_neg hn)
      nlinarith
    exact ⟨h0,by nlinarith⟩
  · rintro ⟨h0,h1⟩
    exact ⟨by positivity,by nlinarith⟩

theorem K_compact : IsCompact K := by rw [K_eq]; exact isCompact_Icc

theorem actual_minimum : IsLeast ((fun x : ℝ => x) '' K) 0 := by
  refine ⟨⟨0,by rw [K_eq]; exact ⟨le_rfl,zero_le_one⟩,rfl⟩,?_⟩
  rintro x ⟨y,hy,rfl⟩
  rw [K_eq] at hy
  exact hy.1

/-- A genuine finite sum of polynomial squares with the indicated degree bound. -/
def SumSquares (k : ℕ) (σ : ℝ[X]) : Prop :=
  ∃ n : ℕ, ∃ p : Fin n → ℝ[X], (∀ i, (p i).natDegree ≤ k) ∧ σ = ∑ i, (p i)^2

def SOSFeasible (r : ℕ) (γ : ℝ) : Prop :=
  ∃ σ0 σ1 σ2 : ℝ[X], SumSquares r σ0 ∧ SumSquares (r-2) σ1 ∧
    SumSquares (r-1) σ2 ∧ X-C γ = σ0 + X^3*σ1 + (1-X^2)*σ2

theorem sumSquares_zero (k : ℕ) : SumSquares k 0 := by
  exact ⟨0,fun i => Fin.elim0 i,fun i => Fin.elim0 i,by simp⟩

theorem linear_sumSquares (k : ℕ) (hk : 1 ≤ k) :
    SumSquares k (C (1/2:ℝ)*(X+1)^2) := by
  refine ⟨2,fun _ => C (1/2:ℝ)*(X+1),?_,?_⟩
  · intro i
    calc
      (C (1/2:ℝ)*(X+1)).natDegree ≤ (X+1 : ℝ[X]).natDegree := natDegree_C_mul_le _ _
      _ ≤ 1 := by compute_degree!
      _ ≤ k := hk
  · simp only [Fin.sum_univ_two]
    have hhalf : 2 * C (1/2:ℝ) = (1:ℝ[X]) := by
      rw [show (2:ℝ[X])=C (2:ℝ) by exact (map_ofNat C 2).symm, ← map_mul]
      norm_num
    linear_combination - C (1/2:ℝ) * (X+1)^2 * hhalf

theorem constant_sumSquares (k : ℕ) : SumSquares k (C (1/2:ℝ)) := by
  refine ⟨2,fun _ => C (1/2:ℝ),?_,?_⟩
  · intro i
    simp
  · simp only [Fin.sum_univ_two]
    rw [← map_pow, ← map_add]
    norm_num

theorem sos_minus_one (r : ℕ) (hr : 2 ≤ r) : SOSFeasible r (-1) := by
  refine ⟨C (1/2:ℝ)*(X+1)^2,0,C (1/2:ℝ),
    linear_sumSquares r (by omega),sumSquares_zero _,constant_sumSquares _,?_⟩
  have hhalf : 2 * C (1/2:ℝ) = (1:ℝ[X]) := by
    rw [show (2:ℝ[X])=C (2:ℝ) by exact (map_ofNat C 2).symm, ← map_mul]
    norm_num
  norm_num only [map_neg, map_one, mul_zero, add_zero]
  linear_combination -(X+1) * hhalf

theorem sumSquares_nonneg (L : ℝ[X] →ₗ[ℝ] ℝ) (g : ℝ[X]) (k : ℕ)
    (h : ∀ p : ℝ[X], p.natDegree ≤ k → 0 ≤ L (g*p^2))
    {σ : ℝ[X]} (hσ : SumSquares k σ) : 0 ≤ L (g*σ) := by
  obtain ⟨n,p,hp,rfl⟩ := hσ
  simp only [mul_sum,map_sum]
  exact sum_nonneg fun i _ => h (p i) (hp i)

theorem weak_duality (r : ℕ) (L : ℝ[X] →ₗ[ℝ] ℝ) (γ : ℝ)
    (hL : MomentFeasible r L) (hγ : SOSFeasible r γ) : γ ≤ L X := by
  obtain ⟨h1,hs,hc,hb⟩ := (momentFeasible_iff r L).1 hL
  obtain ⟨σ0,σ1,σ2,h0,h1s,h2,heq⟩ := hγ
  have hn0 := sumSquares_nonneg L 1 r (by simpa using hs) h0
  have hn1 := sumSquares_nonneg L (X^3) (r-2) hc h1s
  have hn2 := sumSquares_nonneg L (1-X^2) (r-1) hb h2
  have hC : L (C γ) = γ := by
    have ht := L.map_smul γ (1:ℝ[X])
    simpa [Algebra.smul_def,h1] using ht
  have he := congrArg L heq
  simp only [map_sub,map_add,hC,one_mul] at he hn0
  linarith

def momentValues (r : ℕ) : Set ℝ := {v | ∃ L, MomentFeasible r L ∧ L X = v}
def sosValues (r : ℕ) : Set ℝ := {γ | SOSFeasible r γ}
def momentValue (r : ℕ) : ℝ := sInf (momentValues r)
def sosValue (r : ℕ) : ℝ := sSup (sosValues r)

theorem momentValues_nonempty (r : ℕ) : (momentValues r).Nonempty := by
  obtain ⟨L,hL,_⟩ := negative_moment_feasible r
  exact ⟨L X,L,hL,rfl⟩

theorem sosValues_nonempty (r : ℕ) (hr : 2 ≤ r) : (sosValues r).Nonempty :=
  ⟨-1,sos_minus_one r hr⟩

theorem momentValues_bddBelow (r : ℕ) (hr : 2 ≤ r) : BddBelow (momentValues r) := by
  refine ⟨-1,?_⟩
  rintro v ⟨L,hL,rfl⟩
  exact weak_duality r L (-1) hL (sos_minus_one r hr)

theorem sosValues_bddAbove (r : ℕ) : BddAbove (sosValues r) := by
  obtain ⟨L,hL,_⟩ := negative_moment_feasible r
  exact ⟨L X,fun γ hγ => weak_duality r L γ hL hγ⟩

theorem momentValue_bounds (r : ℕ) (hr : 2 ≤ r) :
    -1 ≤ momentValue r ∧ momentValue r < 0 := by
  constructor
  · exact le_csInf (momentValues_nonempty r) (by
      rintro v ⟨L,hL,rfl⟩
      exact weak_duality r L (-1) hL (sos_minus_one r hr))
  · obtain ⟨L,hL,hx⟩ := negative_moment_feasible r
    exact lt_of_le_of_lt (csInf_le (momentValues_bddBelow r hr) ⟨L,hL,rfl⟩) hx

theorem sosValue_bounds (r : ℕ) (hr : 2 ≤ r) : -1 ≤ sosValue r ∧ sosValue r < 0 := by
  constructor
  · exact le_csSup (sosValues_bddAbove r) (sos_minus_one r hr)
  · obtain ⟨L,hL,hx⟩ := negative_moment_feasible r
    exact lt_of_le_of_lt (csSup_le (sosValues_nonempty r hr)
      (fun γ hγ => weak_duality r L γ hL hγ)) hx

/-- Both real optimization values are well-defined and strictly below the true minimum. -/
theorem every_finite_level_has_gap (r : ℕ) (hr : 2 ≤ r) :
    IsCompact K ∧ IsLeast ((fun x : ℝ => x) '' K) 0 ∧
    (momentValues r).Nonempty ∧ BddBelow (momentValues r) ∧
    (sosValues r).Nonempty ∧ BddAbove (sosValues r) ∧
    momentValue r < 0 ∧ sosValue r < 0 :=
  ⟨K_compact,actual_minimum,momentValues_nonempty r,momentValues_bddBelow r hr,
    sosValues_nonempty r hr,sosValues_bddAbove r,(momentValue_bounds r hr).2,
    (sosValue_bounds r hr).2⟩

theorem no_finite_exact_level : ¬ ∃ r : ℕ, 2 ≤ r ∧ (momentValue r = 0 ∨ sosValue r = 0) := by
  rintro ⟨r,hr,h⟩
  have hm := (momentValue_bounds r hr).2
  have hs := (sosValue_bounds r hr).2
  rcases h with h | h <;> linarith


/-- Actual monomial moments, not separately assigned matrix entries. -/
def momentSequence (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ) : ℝ := L (X^n)

theorem momentMatrix_entry (L : ℝ[X] →ₗ[ℝ] ℝ) (r : ℕ) (i j : Fin (r+1)) :
    momentMatrix L r i j = momentSequence L (i.val+j.val) := by
  simp [momentMatrix,localizingMatrix,momentSequence]

theorem cubicMatrix_entry (L : ℝ[X] →ₗ[ℝ] ℝ) (k : ℕ) (i j : Fin (k+1)) :
    localizingMatrix L (X^3) k i j = momentSequence L (i.val+j.val+3) := by
  simp [localizingMatrix,momentSequence,←pow_add,Nat.add_comm]

theorem ballMatrix_entry (L : ℝ[X] →ₗ[ℝ] ℝ) (k : ℕ) (i j : Fin (k+1)) :
    localizingMatrix L (1-X^2) k i j =
      momentSequence L (i.val+j.val) - momentSequence L (i.val+j.val+2) := by
  simp [localizingMatrix,momentSequence,sub_mul,←pow_add,Nat.add_comm]

theorem evaluation_moment_feasible (r : ℕ) (x : ℝ) (hx : x ∈ K) :
    MomentFeasible r (Polynomial.leval x) := by
  rw [momentFeasible_iff]
  refine ⟨by simp,?_,?_,?_⟩
  · intro p _
    simpa using sq_nonneg (p.eval x)
  · intro p _
    simpa using mul_nonneg hx.1 (sq_nonneg (p.eval x))
  · intro p _
    simpa using mul_nonneg hx.2 (sq_nonneg (p.eval x))

theorem K_subset_momentValues (r : ℕ) : K ⊆ momentValues r := by
  intro x hx
  exact ⟨Polynomial.leval x,evaluation_moment_feasible r x hx,by simp⟩

theorem moment_projection_strict (r : ℕ) : K ⊂ momentValues r := by
  refine lt_of_le_of_ne (K_subset_momentValues r) ?_
  intro heq
  obtain ⟨L,hL,hx⟩ := negative_moment_feasible r
  have hm : L X ∈ momentValues r := ⟨L,hL,rfl⟩
  rw [←heq,K_eq] at hm
  linarith [hm.1]

theorem no_finite_exact_projection : ¬ ∃ r : ℕ, 2 ≤ r ∧ momentValues r = K := by
  rintro ⟨r,_,heq⟩
  exact (ne_of_lt (moment_projection_strict r)) heq.symm

end
end TLMC1470
