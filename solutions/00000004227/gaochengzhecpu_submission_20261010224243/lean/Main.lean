import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
set_option autoImplicit false

namespace Conjecture4227

open Matrix Polynomial
open scoped BigOperators

abbrev Vertex := Fin 3
abbrev Edge := Fin 3
abbrev Face := Fin 1
abbrev C₀ := Vertex → ℚ
abbrev C₁ := Edge → ℚ
abbrev C₂ := Face → ℚ
abbrev Mask := Face → Bool

def triangle : SimpleGraph Vertex := ⊤

instance : DecidableRel triangle.Adj :=
  inferInstanceAs (DecidableRel (⊤ : SimpleGraph Vertex).Adj)

theorem every_set_is_clique (s : Set Vertex) : triangle.IsClique s := by
  intro u _ v _ huv
  exact huv

/-- The actual clique complex, defined from the graph's adjacency relation. -/
def flagComplex : Finset (Finset Vertex) :=
  Finset.univ.filter (fun s => triangle.IsClique (s : Set Vertex))

theorem flag_complex_eq : flagComplex = Finset.univ := by
  ext s
  simp [flagComplex, every_set_is_clique]

theorem flag_downward_closed (s t : Finset Vertex)
    (_hs : s ∈ flagComplex) (_ht : t ⊆ s) : t ∈ flagComplex := by
  simp [flag_complex_eq]

theorem dimension_exactly_two :
    (∀ s ∈ flagComplex, s.card ≤ 3) ∧
      ∃ s ∈ flagComplex, s.card = 3 := by
  constructor
  · intro s _
    simpa using Finset.card_le_univ s
  · exact ⟨Finset.univ, by simp [flag_complex_eq], by simp⟩

theorem clique_number : triangle.cliqueNum = 3 := by
  have hc : triangle.IsMaximumClique (Finset.univ : Finset Vertex) := by
    refine ⟨every_set_is_clique _, ?_⟩
    intro t _
    exact Finset.card_le_card (Finset.subset_univ t)
  have h := triangle.maximumClique_card_eq_cliqueNum Finset.univ hc
  simpa using h.symm

/-- Proper colorings of K3 are precisely injections of its three vertices. -/
def coloringEquiv (n : ℕ) : triangle.Coloring (Fin n) ≃ (Vertex ↪ Fin n) where
  toFun c := ⟨c, fun u v huv => by
    by_contra h
    exact c.valid h huv⟩
  invFun e := SimpleGraph.Coloring.mk e (fun {_ _} h => e.injective.ne h)
  left_inv c := by ext v; rfl
  right_inv e := by ext v; rfl

theorem proper_coloring_count (n : ℕ) :
    Fintype.card (triangle.Coloring (Fin n)) = n.descFactorial 3 := by
  rw [Fintype.card_congr (coloringEquiv n), Fintype.card_embedding_eq]
  simp

def chromatic : ℚ[X] := X * (X - 1) * (X - 2)

/-- The defining counting property of the chromatic polynomial, for every color count. -/
def CountsColorings (p : ℚ[X]) : Prop :=
  ∀ n : ℕ, p.eval (n : ℚ) = (Fintype.card (triangle.Coloring (Fin n)) : ℚ)

theorem chromatic_counts : CountsColorings chromatic := by
  intro n
  rw [proper_coloring_count]
  by_cases h : 2 ≤ n
  · have h1 : 1 ≤ n := by omega
    simp [chromatic, Nat.descFactorial, Nat.cast_sub h, Nat.cast_sub h1]
    ring
  · have hn : n = 0 ∨ n = 1 := by omega
    rcases hn with rfl | rfl <;> norm_num [chromatic, Nat.descFactorial]

theorem chromatic_unique (p : ℚ[X]) (hp : CountsColorings p) : p = chromatic := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hi : Set.Infinite (Set.range (fun n : ℕ => (n : ℚ))) :=
    Set.infinite_range_of_injective Nat.cast_injective
  apply hi.mono
  rintro x ⟨n, rfl⟩
  exact (hp n).trans (chromatic_counts n).symm

/-- Increasing orientations of the three actual graph edges. -/
def tail : Edge → Vertex := ![0, 0, 1]
def head : Edge → Vertex := ![1, 2, 2]
def vertices (_ : Face) : Fin 3 → Vertex := ![0, 1, 2]
def faceSet (f : Face) : Finset Vertex :=
  {vertices f 0, vertices f 1, vertices f 2}

theorem edges_enumerate : ∀ u v : Vertex,
    (u < v ∧ triangle.Adj u v) ↔ ∃ e : Edge, tail e = u ∧ head e = v := by decide

theorem edges_unique : Function.Injective (fun e : Edge => (tail e, head e)) := by decide

theorem face_sets_unique : Function.Injective faceSet := by decide

theorem actual_two_faces : ∀ s : Finset Vertex,
    s ∈ flagComplex ∧ s.card = 3 ↔ ∃ f : Face, faceSet f = s := by
  rw [flag_complex_eq]
  decide

/-- Simplicial boundaries [u,v] -> [v]-[u] and [a,b,c] -> [b,c]-[a,c]+[a,b]. -/
def B₁ : Matrix Vertex Edge ℚ := fun v e =>
  (if head e = v then 1 else 0) - (if tail e = v then 1 else 0)

def edgeCoefficient (u v : Vertex) (e : Edge) : ℚ :=
  if tail e = u ∧ head e = v then 1 else 0

def B₂ : Matrix Edge Face ℚ := fun e f =>
  edgeCoefficient (vertices f 1) (vertices f 2) e -
    edgeCoefficient (vertices f 0) (vertices f 2) e +
    edgeCoefficient (vertices f 0) (vertices f 1) e

def boundary₁ : C₁ →ₗ[ℚ] C₀ := Matrix.mulVecLin B₁
def boundary₂ : C₂ →ₗ[ℚ] C₁ := Matrix.mulVecLin B₂

theorem B₁_matrix : B₁ = !![-1, -1, 0; 1, 0, -1; 0, 1, 1] := by decide +kernel
theorem B₂_matrix : B₂ = !![1; -1; 1] := by decide +kernel

theorem boundary₁_formula (z : C₁) :
    boundary₁ z = ![-z 0 - z 1, z 0 - z 2, z 1 + z 2] := by
  change B₁ *ᵥ z = _
  rw [B₁_matrix]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem boundary₂_formula (x : C₂) :
    boundary₂ x = ![x 0, -x 0, x 0] := by
  change B₂ *ᵥ x = _
  rw [B₂_matrix]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem boundary_boundary (x : C₂) : boundary₁ (boundary₂ x) = 0 := by
  rw [boundary₁_formula, boundary₂_formula]
  ext i
  fin_cases i <;> simp

theorem top_boundary_injective : Function.Injective boundary₂ := by
  intro x y h
  have h0 := congrFun h 0
  rw [boundary₂_formula, boundary₂_formula] at h0
  ext i
  fin_cases i
  exact h0

theorem every_cycle_filled (z : C₁) (hz : boundary₁ z = 0) :
    boundary₂ (fun _ => z 0) = z := by
  have h0 := congrFun hz 0
  have h1 := congrFun hz 1
  rw [boundary₁_formula] at h0 h1
  change -z 0 - z 1 = 0 at h0
  change z 0 - z 2 = 0 at h1
  rw [boundary₂_formula]
  ext i
  fin_cases i <;> simp <;> linarith

/-- Every selected subcomplex retains the full graph as its one-skeleton. -/
def Supported (m : Mask) (x : C₂) : Prop := ∀ f, m f = false → x f = 0

/-- Standard rational spanning 2-tree conditions, expressed in actual chains. -/
def IsSpanningTwoTree (m : Mask) : Prop :=
  (∀ x, Supported m x → boundary₂ x = 0 → x = 0) ∧
  (∀ z, boundary₁ z = 0 → ∃ x, Supported m x ∧ boundary₂ x = z)

def fullMask : Mask := fun _ => true

theorem full_is_tree : IsSpanningTwoTree fullMask := by
  constructor
  · intro x _ hx
    exact top_boundary_injective (hx.trans (map_zero boundary₂).symm)
  · intro z hz
    refine ⟨fun _ => z 0, ?_, every_cycle_filled z hz⟩
    intro f hf
    simp [fullMask] at hf

theorem tree_iff_full (m : Mask) : IsSpanningTwoTree m ↔ m = fullMask := by
  constructor
  · intro hm
    have hz : boundary₁ (boundary₂ (fun _ => 1)) = 0 := boundary_boundary _
    obtain ⟨x, hx, hbd⟩ := hm.2 _ hz
    have heq : x = (fun _ => 1) := top_boundary_injective hbd
    ext f
    cases hmf : m f with
    | false =>
      have hzero := hx f hmf
      rw [heq] at hzero
      norm_num at hzero
    | true => rfl
  · rintro rfl
    exact full_is_tree

def treeCount : ℕ := by
  classical
  exact (Finset.univ.filter (fun m : Mask => IsSpanningTwoTree m)).card

theorem tree_count : treeCount = 1 := by
  classical
  have h : Finset.univ.filter (fun m : Mask => IsSpanningTwoTree m) = {fullMask} := by
    ext m
    simp [tree_iff_full]
  rw [treeCount, h]
  exact Finset.card_singleton _

def evaluationPoint : ℚ := -((triangle.cliqueNum : ℚ) - 2)

theorem prescribed_point : evaluationPoint = -1 := by
  norm_num [evaluationPoint, clique_number]

theorem prescribed_value : chromatic.eval evaluationPoint = -6 := by
  norm_num [prescribed_point, chromatic]

theorem tree_count_ne_evaluation : (treeCount : ℚ) ≠ chromatic.eval evaluationPoint := by
  rw [tree_count, prescribed_value]
  norm_num

theorem absolute_value_also_fails : (treeCount : ℚ) ≠ |chromatic.eval evaluationPoint| := by
  rw [tree_count, prescribed_value]
  norm_num

theorem positive_point_also_fails :
    (treeCount : ℚ) ≠ chromatic.eval ((triangle.cliqueNum : ℚ) - 2) := by
  norm_num [tree_count, clique_number, chromatic]

/-- Even changing the negative integer cannot make a unit conversion work. -/
theorem any_negative_value (m : ℕ) :
    chromatic.eval (-(m : ℚ)) = -(m : ℚ) * ((m : ℚ) + 1) * ((m : ℚ) + 2) := by
  simp [chromatic]
  ring

theorem any_negative_value_bound (m : ℕ) (hm : 1 ≤ m) :
    chromatic.eval (-(m : ℚ)) ≤ -6 := by
  have h1 : (1 : ℚ) ≤ m := by exact_mod_cast hm
  have h0 : (0 : ℚ) ≤ m := le_trans (by norm_num) h1
  have h2 : (2 : ℚ) ≤ (m : ℚ) * ((m : ℚ) + 1) := by
    have h := mul_le_mul h1 (show (2 : ℚ) ≤ (m : ℚ) + 1 by linarith)
      (by norm_num : (0 : ℚ) ≤ 2) h0
    norm_num at h ⊢
    exact h
  have h3 := mul_le_mul h2 (show (3 : ℚ) ≤ (m : ℚ) + 2 by linarith)
    (by norm_num : (0 : ℚ) ≤ 3) (le_trans (by norm_num) h2)
  rw [any_negative_value]
  nlinarith

theorem no_negative_integer_unit_conversion (m : ℕ) (hm : 1 ≤ m) :
    (treeCount : ℚ) ≠ chromatic.eval (-(m : ℚ)) ∧
    (treeCount : ℚ) ≠ |chromatic.eval (-(m : ℚ))| := by
  have h := any_negative_value_bound m hm
  rw [tree_count, abs_of_nonpos (le_trans h (by norm_num))]
  norm_num only [Nat.cast_one]
  constructor <;> linarith

theorem counterexample :
    triangle.cliqueNum = 3 ∧ CountsColorings chromatic ∧ treeCount = 1 ∧
      chromatic.eval evaluationPoint = -6 ∧
      (treeCount : ℚ) ≠ chromatic.eval evaluationPoint :=
  ⟨clique_number, chromatic_counts, tree_count, prescribed_value, tree_count_ne_evaluation⟩

end Conjecture4227

#print axioms Conjecture4227.dimension_exactly_two
#print axioms Conjecture4227.clique_number
#print axioms Conjecture4227.chromatic_counts
#print axioms Conjecture4227.chromatic_unique
#print axioms Conjecture4227.actual_two_faces
#print axioms Conjecture4227.tree_iff_full
#print axioms Conjecture4227.counterexample
#print axioms Conjecture4227.absolute_value_also_fails
#print axioms Conjecture4227.positive_point_also_fails
#print axioms Conjecture4227.no_negative_integer_unit_conversion
