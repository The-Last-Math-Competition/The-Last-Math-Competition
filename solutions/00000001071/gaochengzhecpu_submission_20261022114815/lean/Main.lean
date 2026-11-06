import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Tactic.FieldSimp

open SimpleGraph Matrix Finset

namespace Conjecture1071

/-- A real adjacency eigenvalue, with a genuine nonzero eigenvector. -/
def AdjacencyEigenvalue {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : ℝ) : Prop :=
  ∃ x : V → ℝ, x ≠ 0 ∧ G.adjMatrix ℝ *ᵥ x = a • x

/-- Every adjacency eigenvalue of a graph of maximum degree two has modulus at most two. -/
theorem eigenvalue_abs_le_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 2) {a : ℝ} (ha : AdjacencyEigenvalue G a) :
    |a| ≤ 2 := by
  classical
  obtain ⟨x, hx, he⟩ := ha
  have hex : ∃ v, x v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  obtain ⟨v₀, hv₀⟩ := hex
  obtain ⟨v, _, hv⟩ := Finset.exists_max_image Finset.univ (fun i => |x i|)
    ⟨v₀, Finset.mem_univ _⟩
  have hm : ∀ i, |x i| ≤ |x v| := fun i => hv i (Finset.mem_univ _)
  have hp : 0 < |x v| := lt_of_lt_of_le (abs_pos.mpr hv₀) (hm v₀)
  have he' := congrFun he v
  rw [SimpleGraph.adjMatrix_mulVec_apply] at he'
  have hmul : |a| * |x v| ≤ 2 * |x v| := calc
    |a| * |x v| = |∑ i ∈ G.neighborFinset v, x i| := by
      rw [he']; simp [abs_mul]
    _ ≤ ∑ i ∈ G.neighborFinset v, |x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ G.neighborFinset v, |x v| := Finset.sum_le_sum (fun i _ => hm i)
    _ = (G.degree v : ℝ) * |x v| := by
      simp only [Finset.sum_const, nsmul_eq_mul, G.card_neighborFinset_eq_degree]
    _ ≤ 2 * |x v| := mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg v) (abs_nonneg _)
  exact (mul_le_mul_right hp).mp hmul

theorem cycle_eigenvalue_lower_bound (n : ℕ) {a : ℝ}
    (ha : AdjacencyEigenvalue (cycleGraph (n + 3)) a) : -2 ≤ a := by
  have hb := eigenvalue_abs_le_two (cycleGraph (n + 3))
    (fun v => le_of_eq (cycleGraph_degree_three_le)) ha
  exact (abs_le.mp hb).1

def cycleHermitian (n : ℕ) : ((cycleGraph (n + 3)).adjMatrix ℝ).IsHermitian := by
  rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]
  exact (cycleGraph (n + 3)).isSymm_adjMatrix

/-- The least value in Mathlib's complete real adjacency eigenvalue list. -/
noncomputable def leastEigenvalue (n : ℕ) : ℝ :=
  (Finset.univ.image (cycleHermitian n).eigenvalues).min'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

theorem leastEigenvalue_is_eigenvalue (n : ℕ) :
    AdjacencyEigenvalue (cycleGraph (n + 3)) (leastEigenvalue n) := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp
    (Finset.min'_mem (Finset.univ.image (cycleHermitian n).eigenvalues)
      (Finset.image_nonempty.mpr Finset.univ_nonempty))
  change (cycleHermitian n).eigenvalues i = leastEigenvalue n at hi
  refine ⟨⇑((cycleHermitian n).eigenvectorBasis i), ?_, ?_⟩
  · intro hz
    apply (cycleHermitian n).eigenvectorBasis.orthonormal.ne_zero i
    ext j
    exact congrFun hz j
  · rw [← hi]
    exact (cycleHermitian n).mulVec_eigenvectorBasis i

theorem leastEigenvalue_le_list (n : ℕ) (i : Fin (n + 3)) :
    leastEigenvalue n ≤ (cycleHermitian n).eigenvalues i := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

theorem deviation_lower_bound (n : ℕ) :
    2 * Real.sqrt (n + 3 : ℕ) - 2 ≤
      |leastEigenvalue n + 2 * Real.sqrt (n + 3 : ℕ)| := by
  have hl := cycle_eigenvalue_lower_bound n (leastEigenvalue_is_eigenvalue n)
  have ha := le_abs_self (leastEigenvalue n + 2 * Real.sqrt (n + 3 : ℕ))
  linarith

/-- The discrepancy is unbounded even after discarding any finite set of prime orders. -/
theorem deviation_unbounded_on_primes (C : ℝ) (N : ℕ) :
    ∃ n : ℕ, (n + 3).Prime ∧ N ≤ n + 3 ∧
      C < |leastEigenvalue n + 2 * Real.sqrt (n + 3 : ℕ)| := by
  obtain ⟨m, hm⟩ := exists_nat_gt ((|C| + 2) ^ 2)
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max N (max m 3))
  have hpN : N ≤ p := le_trans (le_max_left _ _) hp
  have hpm : m ≤ p := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hp
  have hp3 : 3 ≤ p := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hp
  let n := p - 3
  have hn : n + 3 = p := Nat.sub_add_cancel hp3
  refine ⟨n, hn ▸ hprime, hn ▸ hpN, ?_⟩
  have hsq : (|C| + 2) ^ 2 < (n + 3 : ℕ) := by
    rw [hn]
    exact lt_of_lt_of_le hm (by exact_mod_cast hpm)
  have hs : |C| + 2 < Real.sqrt (n + 3 : ℕ) :=
    (Real.lt_sqrt (by positivity)).mpr hsq
  have hlow := deviation_lower_bound n
  have habs := le_abs_self C
  have hpos := abs_nonneg C
  linarith

/-- The claimed spectral error, allowing arbitrary Big-O constants and a prime-order cutoff. -/
def SpectralClaim : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
    ∀ n : ℕ, (n + 3).Prime → N ≤ n + 3 →
      |leastEigenvalue n + 2 * Real.sqrt (n + 3 : ℕ)| ≤
        C * (n + 3 : ℕ) ^ (-(1 : ℝ) / 4 + ε)

theorem not_spectralClaim : ¬ SpectralClaim := by
  intro h
  obtain ⟨C, hC, N, hN⟩ := h (1 / 8) (by norm_num)
  obtain ⟨n, hp, hn, hgt⟩ := deviation_unbounded_on_primes C N
  have hb := hN n hp hn
  have hpow : ((n + 3 : ℕ) : ℝ) ^ (-(1 : ℝ) / 4 + 1 / 8) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (show 1 ≤ n + 3 by omega))
      (by norm_num)
  have hb' : |leastEigenvalue n + 2 * Real.sqrt (n + 3 : ℕ)| ≤ C :=
    hb.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hC)
  exact (not_lt_of_ge hb') hgt

#print axioms eigenvalue_abs_le_two
#print axioms leastEigenvalue_is_eigenvalue
#print axioms deviation_unbounded_on_primes
#print axioms not_spectralClaim

end Conjecture1071

open Matrix Finset

namespace Conjecture1071

/-- Spectral lower bound from the quadratic-character (conference-matrix) identity. -/
theorem eigenvalue_lower_of_conference {V : Type*} [Fintype V] [DecidableEq V]
    (A Q : Matrix V V ℝ) (p : ℝ) (hp : 1 ≤ p)
    (hlink : Q = 2 • A + 1 - Matrix.of (fun _ _ => (1 : ℝ)))
    (hcol : ∀ j, ∑ i, A i j = (p - 1) / 2)
    (hquad : Q * Q = p • (1 : Matrix V V ℝ) - Matrix.of (fun _ _ => (1 : ℝ)))
    {a : ℝ} {x : V → ℝ} (hx : x ≠ 0) (he : A *ᵥ x = a • x) :
    -(1 + Real.sqrt p) / 2 ≤ a := by
  classical
  by_cases ha : a = (p - 1) / 2
  · have hs := Real.sqrt_nonneg p
    rw [ha]
    linarith
  have hsum : ((p - 1) / 2) * (∑ i, x i) = a * (∑ i, x i) := by
    calc
      ((p - 1) / 2) * (∑ i, x i) = ∑ i, ∑ j, A i j * x j := by
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_mul, hcol]
        rw [Finset.mul_sum]
      _ = ∑ i, (A *ᵥ x) i := rfl
      _ = a * (∑ i, x i) := by rw [he]; simp [Finset.mul_sum]
  have hs0 : ∑ i, x i = 0 := by
    have hh : (((p - 1) / 2) - a) * (∑ i, x i) = 0 := by nlinarith [hsum]
    rcases mul_eq_zero.mp hh with h | h
    · exact (ha (sub_eq_zero.mp h).symm).elim
    · exact h
  have hJ : (Matrix.of (fun _ _ => (1 : ℝ)) : Matrix V V ℝ) *ᵥ x = 0 := by
    ext i
    simpa [Matrix.mulVec, dotProduct] using hs0
  have hqx : Q *ᵥ x = (2 * a + 1) • x := by
    rw [hlink, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec_assoc,
      Matrix.one_mulVec, he, hJ, sub_zero]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hq2 := congrArg (fun M : Matrix V V ℝ => M *ᵥ x) hquad
  dsimp only at hq2
  rw [← Matrix.mulVec_mulVec, hqx, Matrix.mulVec_smul, hqx,
    Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec, hJ, sub_zero] at hq2
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  have heq := congrFun hq2 i
  simp only [Pi.smul_apply, smul_eq_mul] at heq
  have hpq : (2 * a + 1) ^ 2 = p := by
    have hh : ((2 * a + 1) ^ 2 - p) * x i = 0 := by nlinarith [heq]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hi)
  have habs : |2 * a + 1| = Real.sqrt p := by
    simpa only [Real.sqrt_sq_eq_abs] using congrArg Real.sqrt hpq
  have hlow := (abs_le.mp (le_of_eq habs)).1
  linarith

end Conjecture1071

open Finset Matrix SimpleGraph

namespace Conjecture1071.Paley

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem char_neg (hneg : quadraticChar F (-1) = 1) (x : F) :
    quadraticChar F (-x) = quadraticChar F x := by
  rw [neg_eq_neg_one_mul, map_mul, hneg, one_mul]

theorem char_jacobi (hodd : ringChar F ≠ 2) (hneg : quadraticChar F (-1) = 1) :
    ∑ x : F, quadraticChar F x * quadraticChar F (1 - x) = -1 := by
  have h := jacobiSum_nontrivial_inv (quadraticChar_ne_one hodd)
  rw [(quadraticChar_isQuadratic F).inv, hneg] at h
  exact h

theorem char_correlation_offdiag (hodd : ringChar F ≠ 2)
    (hneg : quadraticChar F (-1) = 1) (a b : F) (hab : a ≠ b) :
    ∑ x : F, quadraticChar F (a - x) * quadraticChar F (x - b) = -1 := by
  classical
  let d := a - b
  have hd : d ≠ 0 := sub_ne_zero.mpr hab
  let e := (Equiv.mulLeft₀ d hd).trans (Equiv.addLeft b)
  calc
    ∑ x : F, quadraticChar F (a - x) * quadraticChar F (x - b)
      = ∑ t : F, quadraticChar F (a - (b + d * t)) *
          quadraticChar F (b + d * t - b) := by
        exact (Equiv.sum_comp e _).symm
    _ = ∑ t : F, quadraticChar F (d * (1 - t)) * quadraticChar F (d * t) := by
      apply Finset.sum_congr rfl
      intro t _
      congr 2 <;> dsimp [d] <;> ring
    _ = ∑ t : F, quadraticChar F t * quadraticChar F (1 - t) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [map_mul, map_mul]
      calc
        quadraticChar F d * quadraticChar F (1 - t) *
            (quadraticChar F d * quadraticChar F t)
          = (quadraticChar F d ^ 2) *
              (quadraticChar F t * quadraticChar F (1 - t)) := by ring
        _ = _ := by rw [quadraticChar_sq_one hd, one_mul]
    _ = -1 := char_jacobi hodd hneg

theorem char_correlation_diag (hneg : quadraticChar F (-1) = 1) (a : F) :
    ∑ x : F, quadraticChar F (a - x) * quadraticChar F (x - a) =
      (Fintype.card F : ℤ) - 1 := by
  classical
  have hi (x : F) : quadraticChar F (a - x) * quadraticChar F (x - a) =
      1 - if x = a then 1 else 0 := by
    rw [show x - a = -(a - x) by ring, char_neg hneg]
    by_cases hxa : x = a
    · simp [hxa, quadraticChar_zero]
    · rw [if_neg hxa, sub_zero, ← pow_two]
      exact quadraticChar_sq_one (sub_ne_zero.mpr (Ne.symm hxa))
  simp_rw [hi]
  rw [Finset.sum_sub_distrib]
  simp

def charMatrix : Matrix F F ℝ := fun a b => quadraticChar F (a - b)

theorem charMatrix_sq (hodd : ringChar F ≠ 2) (hneg : quadraticChar F (-1) = 1) :
    (charMatrix : Matrix F F ℝ) * charMatrix =
      (Fintype.card F : ℝ) • (1 : Matrix F F ℝ) - Matrix.of (fun _ _ => (1 : ℝ)) := by
  classical
  ext a b
  simp only [Matrix.mul_apply, charMatrix, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul, Matrix.one_apply]
  by_cases hab : a = b
  · subst b
    simp only [if_true, mul_one]
    exact_mod_cast char_correlation_diag hneg a
  · simp only [if_neg hab, mul_zero, zero_sub]
    exact_mod_cast char_correlation_offdiag hodd hneg a b hab

/-- The standard undirected Paley graph: adjacency means a nonzero square difference. -/
def graph (hneg : quadraticChar F (-1) = 1) : SimpleGraph F where
  Adj a b := quadraticChar F (a - b) = 1
  symm := by
    intro a b h
    rw [show b - a = -(a - b) by ring, char_neg hneg]
    exact h
  loopless := by intro a; simp [quadraticChar_zero]

instance (hneg : quadraticChar F (-1) = 1) : DecidableRel (graph hneg).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ = (1 : ℤ)))

theorem graph_adj_iff (hneg : quadraticChar F (-1) = 1) (a b : F) :
    (graph hneg).Adj a b ↔ a ≠ b ∧ IsSquare (a - b) := by
  change quadraticChar F (a - b) = 1 ↔ _
  by_cases hab : a = b
  · simp [hab, quadraticChar_zero]
  · exact ⟨fun h => ⟨hab, (quadraticChar_one_iff_isSquare (sub_ne_zero.mpr hab)).mp h⟩,
      fun h => (quadraticChar_one_iff_isSquare (sub_ne_zero.mpr hab)).mpr h.2⟩

theorem charMatrix_graph (hneg : quadraticChar F (-1) = 1) :
    (charMatrix : Matrix F F ℝ) =
      2 • (graph hneg).adjMatrix ℝ + 1 - Matrix.of (fun _ _ => (1 : ℝ)) := by
  classical
  ext a b
  simp only [charMatrix, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul, Matrix.one_apply, SimpleGraph.adjMatrix, graph]
  by_cases hab : a = b
  · subst b
    simp [quadraticChar_zero]
  · simp only [if_neg hab]
    rcases quadraticChar_dichotomy (sub_ne_zero.mpr hab) with h | h
    · norm_num [h]
    · norm_num [h]

theorem charMatrix_colsum (hodd : ringChar F ≠ 2) (j : F) :
    ∑ i, (charMatrix : Matrix F F ℝ) i j = 0 := by
  have hs : ∑ i : F, quadraticChar F (i - j) = 0 := by
    simpa only [sub_eq_add_neg] using
      (Equiv.sum_comp (Equiv.addRight (-j)) (fun x => quadraticChar F x)).trans
        (quadraticChar_sum_zero hodd)
  simp only [charMatrix]
  exact_mod_cast hs

theorem graph_colsum (hodd : ringChar F ≠ 2) (hneg : quadraticChar F (-1) = 1) (j : F) :
    ∑ i, (graph hneg).adjMatrix ℝ i j = ((Fintype.card F : ℝ) - 1) / 2 := by
  classical
  have he := congrArg (fun M : Matrix F F ℝ => ∑ i, M i j) (charMatrix_graph hneg)
  dsimp only at he
  rw [charMatrix_colsum hodd] at he
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
    smul_eq_mul, Matrix.one_apply] at he
  simp only [nsmul_eq_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, mul_one] at he
  norm_num only [Nat.cast_ofNat] at he
  linarith

theorem graph_eigenvalue_lower (hodd : ringChar F ≠ 2)
    (hneg : quadraticChar F (-1) = 1) {a : ℝ} {x : F → ℝ}
    (hx : x ≠ 0) (he : (graph hneg).adjMatrix ℝ *ᵥ x = a • x) :
    -(1 + Real.sqrt (Fintype.card F)) / 2 ≤ a := by
  apply eigenvalue_lower_of_conference ((graph hneg).adjMatrix ℝ) charMatrix
    (Fintype.card F) _ (charMatrix_graph hneg) (graph_colsum hodd hneg)
    (charMatrix_sq hodd hneg) hx he
  exact_mod_cast (show 1 ≤ Fintype.card F from Nat.one_le_iff_ne_zero.mpr
    (ne_of_gt Fintype.card_pos))

def graphHermitian (hneg : quadraticChar F (-1) = 1) :
    ((graph hneg).adjMatrix ℝ).IsHermitian := by
  rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]
  exact (graph hneg).isSymm_adjMatrix

noncomputable def leastEigenvalue (hneg : quadraticChar F (-1) = 1) : ℝ :=
  (Finset.univ.image (graphHermitian hneg).eigenvalues).min'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

theorem leastEigenvalue_lower (hodd : ringChar F ≠ 2)
    (hneg : quadraticChar F (-1) = 1) :
    -(1 + Real.sqrt (Fintype.card F)) / 2 ≤ leastEigenvalue hneg := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp
    (Finset.min'_mem (Finset.univ.image (graphHermitian hneg).eigenvalues)
      (Finset.image_nonempty.mpr Finset.univ_nonempty))
  change (graphHermitian hneg).eigenvalues i = leastEigenvalue hneg at hi
  apply graph_eigenvalue_lower hodd hneg
    (x := ⇑((graphHermitian hneg).eigenvectorBasis i))
  · intro hz
    apply (graphHermitian hneg).eigenvectorBasis.orthonormal.ne_zero i
    ext j
    exact congrFun hz j
  · rw [← hi]
    exact (graphHermitian hneg).mulVec_eigenvectorBasis i

/-- Primes for which the ordinary Paley graph is undirected. -/
def GoodPrime := {p : ℕ // p.Prime ∧ p % 4 = 1}

instance (p : GoodPrime) : Fact p.val.Prime := ⟨p.property.1⟩

theorem prime_odd (p : GoodPrime) : ringChar (ZMod p.val) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  have h := p.property.2
  omega

def primeNegOne (p : GoodPrime) : quadraticChar (ZMod p.val) (-1) = 1 := by
  apply (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr
  apply FiniteField.isSquare_neg_one_iff.mpr
  simpa only [ZMod.card, p.property.2] using (show (1 : ℕ) ≠ 3 by decide)

noncomputable def primeLeast (p : GoodPrime) : ℝ := leastEigenvalue (primeNegOne p)

theorem prime_deviation_lower (p : GoodPrime) :
    (3 * Real.sqrt p.val - 1) / 2 ≤ |primeLeast p + 2 * Real.sqrt p.val| := by
  have hl := leastEigenvalue_lower (prime_odd p) (primeNegOne p)
  simp only [ZMod.card] at hl
  have ha := le_abs_self (primeLeast p + 2 * Real.sqrt p.val)
  change -(1 + Real.sqrt p.val) / 2 ≤ primeLeast p at hl
  linarith

theorem prime_deviation_unbounded (C : ℝ) (N : ℕ) :
    ∃ p : GoodPrime, N ≤ p.val ∧ C < |primeLeast p + 2 * Real.sqrt p.val| := by
  obtain ⟨m, hm⟩ := exists_nat_gt ((|C| + 2) ^ 2)
  obtain ⟨p, hp, hlarge, hmod⟩ := Nat.exists_prime_gt_modEq_one (max N m)
    (show 4 ≠ 0 by decide)
  have hm4 : p % 4 = 1 := by simpa only [Nat.ModEq, Nat.mod_eq_of_lt (show 1 < 4 by decide)] using hmod
  let P : GoodPrime := ⟨p, hp, hm4⟩
  refine ⟨P, le_trans (le_max_left _ _) (le_of_lt hlarge), ?_⟩
  have hmp : m ≤ p := le_trans (le_max_right _ _) (le_of_lt hlarge)
  have hsq : (|C| + 2) ^ 2 < (p : ℝ) := lt_of_lt_of_le hm (by exact_mod_cast hmp)
  have hs : |C| + 2 < Real.sqrt p := (Real.lt_sqrt (by positivity)).mpr hsq
  have hl := prime_deviation_lower P
  have hc := le_abs_self C
  have hp0 := abs_nonneg C
  change (3 * Real.sqrt p - 1) / 2 ≤ |primeLeast P + 2 * Real.sqrt p| at hl
  change C < |primeLeast P + 2 * Real.sqrt p|
  linarith

/-- The source's error estimate for the standard Paley graph, with arbitrary constants. -/
def SpectralClaim : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
    ∀ p : GoodPrime, N ≤ p.val →
      |primeLeast p + 2 * Real.sqrt p.val| ≤
        C * (p.val : ℝ) ^ (-(1 : ℝ) / 4 + ε)

theorem not_spectralClaim : ¬ SpectralClaim := by
  intro h
  obtain ⟨C, hC, N, hN⟩ := h (1 / 8) (by norm_num)
  obtain ⟨p, hn, hgt⟩ := prime_deviation_unbounded C N
  have hb := hN p hn
  have hpow : (p.val : ℝ) ^ (-(1 : ℝ) / 4 + 1 / 8) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast p.property.1.one_lt.le)
      (by norm_num)
  have hb' : |primeLeast p + 2 * Real.sqrt p.val| ≤ C :=
    hb.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hC)
  exact (not_lt_of_ge hb') hgt

#print axioms char_correlation_offdiag
#print axioms charMatrix_sq
#print axioms graph_eigenvalue_lower
#print axioms prime_deviation_unbounded
#print axioms not_spectralClaim

end Conjecture1071.Paley
