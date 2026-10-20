import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Finset Matrix
namespace Conjecture7717
set_option autoImplicit false
abbrev V := ZMod 64 × ZMod 4
def a : V := (1, 0)
def b : V := (0, 1)
def jumps : Finset V := {a, -a, b, -b}
def graph : SimpleGraph V where
  Adj v w := w - v ∈ jumps
  symm := by
    intro v w h
    have he : v - w = -(w - v) := by abel
    rw [he]
    change -(w - v) ∈ jumps
    simp only [jumps, mem_insert, mem_singleton] at h ⊢
    rcases h with h | h | h | h <;> rw [h] <;> simp
  loopless := by
    intro v
    norm_num [jumps, a, b, Prod.ext_iff]; decide
instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ jumps))

theorem neighbors (v : V) : graph.neighborFinset v = jumps.image (v + ·) := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset, graph, mem_image]
  constructor
  · intro h
    exact ⟨w - v, h, by abel⟩
  · rintro ⟨s, hs, rfl⟩
    simpa using hs

theorem degree_four (v : V) : graph.degree v = 4 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighbors,
    card_image_of_injective _ (add_right_injective v)]
  decide +kernel

theorem sum_jumps (g : V → ℂ) : ∑ s ∈ jumps, g s = g a + g (-a) + g b + g (-b) := by
  simp only [jumps, sum_insert (by decide : a ∉ ({-a, b, -b} : Finset V)),
    sum_insert (by decide : -a ∉ ({b, -b} : Finset V)),
    sum_insert (by decide : b ∉ ({-b} : Finset V)), sum_singleton]
  ring

theorem step_a (v : V) : graph.Adj v (v + a) := by
  change (v + a) - v ∈ jumps
  simp [jumps]

theorem step_b (v : V) : graph.Adj v (v + b) := by
  change (v + b) - v ∈ jumps
  simp [jumps]

theorem reachable_a (v : V) (n : ℕ) : graph.Reachable v (v + n • a) := by
  induction n with
  | zero => simpa using SimpleGraph.Reachable.refl (G := graph) v
  | succ n ih =>
    simpa only [add_nsmul, one_nsmul, add_assoc] using ih.trans (step_a (v + n • a)).reachable

theorem reachable_b (v : V) (n : ℕ) : graph.Reachable v (v + n • b) := by
  induction n with
  | zero => simpa using SimpleGraph.Reachable.refl (G := graph) v
  | succ n ih =>
    simpa only [add_nsmul, one_nsmul, add_assoc] using ih.trans (step_b (v + n • b)).reachable

theorem connected : graph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, fun v => ?_⟩
  have h := (reachable_a 0 v.1.val).trans (reachable_b (0 + v.1.val • a) v.2.val)
  simpa [a, b, nsmul_eq_mul] using h

def cell (v : V) (i : Fin 4) : V := v + ![0, a, a + b, b] i

theorem cell_injective (v : V) : Function.Injective (cell v) := by
  intro i j h
  have he := add_left_cancel h
  have hi : Function.Injective (fun k : Fin 4 => (![0, a, a + b, b] : Fin 4 → V) k) := by decide +kernel
  exact hi he

theorem cell_edges (v : V) (i : Fin 4) : graph.Adj (cell v i) (cell v (i + 1)) := by
  have htrans (x y : V) : graph.Adj (v + x) (v + y) ↔ graph.Adj x y := by
    change (v + y) - (v + x) ∈ jumps ↔ y - x ∈ jumps
    rw [add_sub_add_left_eq_sub]
  change graph.Adj (v + _) (v + _)
  rw [htrans]
  fin_cases i <;> decide +kernel

noncomputable def f (v : V) : ℂ := ZMod.stdAddChar v.1
noncomputable def mu : ℂ := 2 - ZMod.stdAddChar (1 : ZMod 64) - ZMod.stdAddChar (-1 : ZMod 64)
noncomputable def lam : ℝ := 2 - 2 * Real.cos (Real.pi / 32)

theorem eigen_equation : graph.lapMatrix ℂ *ᵥ f = mu • f := by
  funext v
  rw [SimpleGraph.lapMatrix_mulVec_apply, degree_four, neighbors,
    Finset.sum_image (fun s _ t _ h => add_left_cancel h)]
  rw [sum_jumps]
  simp only [a, b, Prod.fst_neg, f, AddChar.map_add_eq_mul,
    AddChar.map_zero_eq_one, mu, Pi.smul_apply, smul_eq_mul, mul_one]
  norm_num
  simp only [AddChar.map_add_eq_mul]
  ring

theorem f_ne_zero : f ≠ 0 := by
  intro h
  have := congrFun h (0, 0)
  norm_num [f] at this

theorem mu_real : mu = (lam : ℂ) := by
  have h1 := ZMod.stdAddChar_coe (N := 64) (1 : ℤ)
  have hn := ZMod.stdAddChar_coe (N := 64) (-1 : ℤ)
  norm_num at h1 hn
  have e1 : 2 * (Real.pi : ℂ) * Complex.I / 64 = ((Real.pi / 32 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have en : -(2 * (Real.pi : ℂ) * Complex.I) / 64 = -((Real.pi / 32 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [mu, h1, hn, e1, en, Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  dsimp [lam]
  push_cast
  ring

theorem lam_pos : 0 < lam := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := Real.pi / 32)
    (by norm_num) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  simp only [Real.cos_zero] at h
  dsimp [lam]
  linarith

theorem lam_lt_claimed_bound : lam < (3 / 16 : ℝ) / 4 ^ 2 := by
  have h := Real.one_sub_sq_div_two_le_cos (x := Real.pi / 32)
  have hp := Real.pi_lt_d2
  have hpp := Real.pi_pos
  have hp2 : Real.pi ^ 2 < 12 := by nlinarith
  dsimp [lam]
  norm_num only [show (4 : ℝ) ^ 2 = 16 by norm_num]
  nlinarith

noncomputable def realF (v : V) : ℝ := (f v).re

theorem real_eigen_equation : graph.lapMatrix ℝ *ᵥ realF = lam • realF := by
  funext v
  have h := congrArg Complex.re (congrFun eigen_equation v)
  rw [mu_real] at h
  rw [SimpleGraph.lapMatrix_mulVec_apply] at h ⊢
  simpa [realF, Complex.sub_re, Complex.mul_re, Complex.re_sum] using h

theorem realF_ne_zero : realF ≠ 0 := by
  intro h
  have := congrFun h (0, 0)
  norm_num [realF, f] at this

theorem has_small_positive_eigenvalue :
    ∃ t : ℝ, 0 < t ∧ t < (3 / 16 : ℝ) / 4 ^ 2 ∧
      Module.End.HasEigenvalue (Matrix.toLin' (graph.lapMatrix ℝ)) t := by
  refine ⟨lam, lam_pos, lam_lt_claimed_bound, ?_⟩
  apply Module.End.hasEigenvalue_of_hasEigenvector
  refine ⟨?_, realF_ne_zero⟩
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  exact real_eigen_equation

def positiveEigenvalues : Set ℝ := {t | 0 < t ∧
  Module.End.HasEigenvalue (Matrix.toLin' (graph.lapMatrix ℝ)) t}

theorem positiveEigenvalues_finite : positiveEigenvalues.Finite := by
  exact (Module.End.finite_hasEigenvalue (Matrix.toLin' (graph.lapMatrix ℝ))).subset (fun _ ht => ht.2)

theorem spectral_gap_exists_and_small : ∃ gap : ℝ,
    IsLeast positiveEigenvalues gap ∧ 0 < gap ∧ gap < (3 / 16 : ℝ) / 4 ^ 2 := by
  rcases has_small_positive_eigenvalue with ⟨t, ht0, htb, ht⟩
  have hmem : t ∈ positiveEigenvalues := ⟨ht0, ht⟩
  obtain ⟨g, hg, hgmin⟩ := Set.exists_min_image positiveEigenvalues id
    positiveEigenvalues_finite ⟨t, hmem⟩
  exact ⟨g, ⟨hg, hgmin⟩, hg.1, lt_of_le_of_lt (hgmin t hmem) htb⟩

abbrev GridV := ℤ × ℤ
def gridJumps : Finset GridV := {(1,0),(-1,0),(0,1),(0,-1)}
def gridAdj (v w : GridV) : Prop := w - v ∈ gridJumps
def project (p : GridV) : V := (p.1, p.2)

theorem project_add (p q : GridV) : project (p + q) = project p + project q := by
  ext <;> simp [project]
theorem project_sub (p q : GridV) : project (p - q) = project p - project q := by
  ext <;> simp [project]
theorem project_surjective : Function.Surjective project := by
  intro v
  exact ⟨(v.1.val, v.2.val), by simp [project]⟩
theorem project_kernel (p : GridV) : project p = 0 ↔ 64 ∣ p.1 ∧ 4 ∣ p.2 := by
  simp [project, Prod.ext_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
theorem project_jumps : gridJumps.image project = jumps := by decide +kernel

theorem quotient_adjacency (v w : V) : graph.Adj v w ↔
    ∃ p q : GridV, project p = v ∧ project q = w ∧ gridAdj p q := by
  constructor
  · intro h
    change w - v ∈ jumps at h
    rw [← project_jumps, mem_image] at h
    rcases h with ⟨s, hs, he⟩
    obtain ⟨p, hp⟩ := project_surjective v
    refine ⟨p, p + s, hp, ?_, ?_⟩
    · rw [project_add, hp, he]
      abel
    · simpa [gridAdj] using hs
  · rintro ⟨p, q, rfl, rfl, h⟩
    change project q - project p ∈ jumps
    rw [← project_sub, ← project_jumps]
    exact mem_image.mpr ⟨q - p, h, rfl⟩

theorem laplacian_posSemidef : (graph.lapMatrix ℝ).PosSemidef :=
  SimpleGraph.posSemidef_lapMatrix ℝ graph

theorem counterexample : graph.Connected ∧ (∀ v, graph.degree v = 4) ∧
    (∀ v, Function.Injective (cell v)) ∧ (∀ v i, graph.Adj (cell v i) (cell v (i + 1))) ∧
    ∃ gap : ℝ, IsLeast positiveEigenvalues gap ∧ 0 < gap ∧
      gap < (3 / 16 : ℝ) / 4 ^ 2 := by
  exact ⟨connected, degree_four, cell_injective, cell_edges, spectral_gap_exists_and_small⟩

#print axioms counterexample
#print axioms spectral_gap_exists_and_small
#print axioms quotient_adjacency
#print axioms connected
#print axioms cell_edges

end Conjecture7717
