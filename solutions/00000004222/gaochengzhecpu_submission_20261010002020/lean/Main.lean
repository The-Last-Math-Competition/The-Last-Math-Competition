import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Conjecture4222

open Matrix Polynomial
open scoped BigOperators

abbrev Vertex := Fin 4
abbrev Edge := Fin 6
abbrev Face := Fin 4
abbrev Mask := Face → Bool
abbrev C₀ := Vertex → ℚ
abbrev C₁ := Edge → ℚ
abbrev C₂ := Face → ℚ

/-- All proper subsets of four vertices, the boundary complex of a tetrahedron. -/
def tetrahedron : Finset (Finset Vertex) := Finset.univ.filter (fun s => s.card ≤ 3)

theorem tetrahedron_empty : (∅ : Finset Vertex) ∈ tetrahedron := by decide

theorem tetrahedron_downward_closed {s t : Finset Vertex}
    (hs : s ∈ tetrahedron) (ht : t ⊆ s) : t ∈ tetrahedron := by
  simp only [tetrahedron, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  exact (Finset.card_le_card ht).trans hs

/-- The six increasing oriented edges of the tetrahedron. -/
def tail : Edge → Vertex := ![0, 0, 0, 1, 1, 2]
def head : Edge → Vertex := ![1, 2, 3, 2, 3, 3]

/-- The four increasing faces, in the order 123, 023, 013, 012. -/
def vertices : Face → Fin 3 → Vertex := ![![1, 2, 3], ![0, 2, 3], ![0, 1, 3], ![0, 1, 2]]

theorem edges_enumerate_pairs :
    ∀ u v : Vertex, u < v ↔ ∃ e : Edge, tail e = u ∧ head e = v := by decide

theorem faces_enumerate_triples :
    ∀ a b c : Vertex, a < b ∧ b < c ↔
      ∃ f : Face, vertices f 0 = a ∧ vertices f 1 = b ∧ vertices f 2 = c := by decide

theorem edges_unique : Function.Injective (fun e : Edge => (tail e, head e)) := by decide

theorem faces_unique : Function.Injective vertices := by decide

def faceSet (f : Face) : Finset Vertex := {vertices f 0, vertices f 1, vertices f 2}

theorem face_sets_unique : Function.Injective faceSet := by decide

theorem actual_two_faces : ∀ s : Finset Vertex,
    s ∈ tetrahedron ∧ s.card = 3 ↔ ∃ f : Face, faceSet f = s := by decide

/-- The simplicial boundary of an oriented edge: [u,v] ↦ [v]-[u]. -/
def B₁ : Matrix Vertex Edge ℚ := fun v e =>
  (if head e = v then 1 else 0) - (if tail e = v then 1 else 0)

def edgeCoefficient (u v : Vertex) (e : Edge) : ℚ :=
  if tail e = u ∧ head e = v then 1 else 0

/-- The simplicial boundary [a,b,c] ↦ [b,c]-[a,c]+[a,b]. -/
def B₂ : Matrix Edge Face ℚ := fun e f =>
  edgeCoefficient (vertices f 1) (vertices f 2) e -
    edgeCoefficient (vertices f 0) (vertices f 2) e +
    edgeCoefficient (vertices f 0) (vertices f 1) e

def boundary₁ : C₁ →ₗ[ℚ] C₀ := Matrix.mulVecLin B₁
def boundary₂ : C₂ →ₗ[ℚ] C₁ := Matrix.mulVecLin B₂

theorem B₁_matrix : B₁ =
    !![-1, -1, -1, 0, 0, 0; 1, 0, 0, -1, -1, 0;
       0, 1, 0, 1, 0, -1; 0, 0, 1, 0, 1, 1] := by
  decide +kernel

theorem B₂_matrix : B₂ =
    !![0, 0, 1, 1; 0, 1, 0, -1; 0, -1, -1, 0;
       1, 0, 0, 1; -1, 0, 1, 0; 1, 1, 0, 0] := by
  decide +kernel

theorem boundary₁_formula (z : C₁) : boundary₁ z =
    ![-z 0 - z 1 - z 2, z 0 - z 3 - z 4, z 1 + z 3 - z 5, z 2 + z 4 + z 5] := by
  change B₁ *ᵥ z = _
  rw [B₁_matrix]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem boundary₂_formula (x : C₂) : boundary₂ x =
    ![x 2 + x 3, x 1 - x 3, -x 1 - x 2, x 0 + x 3, -x 0 + x 2, x 0 + x 1] := by
  change B₂ *ᵥ x = _
  rw [B₂_matrix]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem boundary_boundary (x : C₂) : boundary₁ (boundary₂ x) = 0 := by
  rw [boundary₁_formula, boundary₂_formula]
  ext i
  fin_cases i <;> simp <;> ring

/-- The oriented fundamental 2-cycle of the tetrahedral sphere. -/
def sigma : C₂ := ![1, -1, 1, -1]

theorem sigma_nonzero (i : Face) : sigma i ≠ 0 := by fin_cases i <;> norm_num [sigma]
theorem sigma_square (i : Face) : sigma i * sigma i = 1 := by fin_cases i <;> norm_num [sigma]

theorem sigma_cycle : boundary₂ sigma = 0 := by
  rw [boundary₂_formula]
  change ![(1 : ℚ) + (-1), -1 - (-1), -(-1) - 1, 1 + (-1), -1 + 1, 1 + (-1)] = 0
  ext i
  fin_cases i <;> norm_num

theorem kernel_representation (x : C₂) (h : boundary₂ x = 0) : x = (x 0) • sigma := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h3 := congrFun h 3
  rw [boundary₂_formula] at h0 h1 h3
  change x 2 + x 3 = 0 at h0
  change x 1 - x 3 = 0 at h1
  change x 0 + x 3 = 0 at h3
  ext i
  fin_cases i <;> simp [sigma] <;> linarith

/-- An integral formula for a preimage of every 1-cycle. -/
def filling (z : C₁) : C₂ := ![z 3, z 1, z 0, 0]

theorem filling_boundary (z : C₁) (hz : boundary₁ z = 0) : boundary₂ (filling z) = z := by
  have h0 := congrFun hz 0
  have h1 := congrFun hz 1
  have h2 := congrFun hz 2
  rw [boundary₁_formula] at h0 h1 h2
  change -z 0 - z 1 - z 2 = 0 at h0
  change z 0 - z 3 - z 4 = 0 at h1
  change z 1 + z 3 - z 5 = 0 at h2
  rw [boundary₂_formula]
  ext i
  fin_cases i <;> simp [filling] <;> linarith

/-- Chains of the subcomplex selected by the face mask; its full 1-skeleton is retained. -/
def Supported (m : Mask) (x : C₂) : Prop := ∀ i, m i = false → x i = 0

/-- Rational spanning 2-trees: no 2-cycles, and every 1-cycle is a selected-face boundary. -/
def IsSpanningTwoTree (m : Mask) : Prop :=
  (∀ x, Supported m x → boundary₂ x = 0 → x = 0) ∧
  (∀ z, boundary₁ z = 0 → ∃ x, Supported m x ∧ boundary₂ x = z)

def ExactlyOneMissing (m : Mask) : Prop := ∃ v, ∀ i, m i = false ↔ i = v

instance (m : Mask) : Decidable (ExactlyOneMissing m) :=
  inferInstanceAs (Decidable (∃ v, ∀ i, m i = false ↔ i = v))

def goodMasks : Finset Mask := Finset.univ.filter ExactlyOneMissing

theorem good_mask_count : goodMasks.card = 4 := by decide

theorem one_missing_is_tree (m : Mask) (hm : ExactlyOneMissing m) : IsSpanningTwoTree m := by
  rcases hm with ⟨v, hv⟩
  constructor
  · intro x hx hcycle
    have hrep := kernel_representation x hcycle
    have hz := hx v ((hv v).2 rfl)
    have hcoord := congrFun hrep v
    simp only [Pi.smul_apply, smul_eq_mul] at hcoord
    have hx0 : x 0 = 0 := (mul_eq_zero.mp (hcoord.symm.trans hz)).resolve_right (sigma_nonzero v)
    simpa [hx0] using hrep
  · intro z hz
    let a := filling z
    let x := a - (a v * sigma v) • sigma
    refine ⟨x, ?_, ?_⟩
    · intro i hi
      have hiv := (hv i).1 hi
      subst i
      change a v - (a v * sigma v) * sigma v = 0
      rw [mul_assoc, sigma_square, mul_one, sub_self]
    · dsimp [x]
      rw [map_sub, map_smul, sigma_cycle, smul_zero, sub_zero]
      exact filling_boundary z hz

theorem tree_has_missing_face (m : Mask) (ht : IsSpanningTwoTree m) : ∃ v, m v = false := by
  by_contra h
  have hs : Supported m sigma := by
    intro i hi
    exact (h ⟨i, hi⟩).elim
  have hzero := ht.1 sigma hs sigma_cycle
  exact sigma_nonzero 0 (congrFun hzero 0)

theorem tree_has_only_one_missing_face (m : Mask) (ht : IsSpanningTwoTree m)
    (v w : Face) (hv : m v = false) (hw : m w = false) : v = w := by
  by_contra hvw
  let e : C₂ := Pi.single v 1
  obtain ⟨x, hx, hbd⟩ := ht.2 (boundary₂ e) (boundary_boundary e)
  have hcycle : boundary₂ (x - e) = 0 := by rw [map_sub, hbd, sub_self]
  have hrep := kernel_representation (x - e) hcycle
  have hcw := congrFun hrep w
  have hcv := congrFun hrep v
  have hxw := hx w hw
  have hxv := hx v hv
  have hwv : w ≠ v := Ne.symm hvw
  have hwcoord : (x - e) w = 0 := by simp [e, hxw, hwv, hvw]
  rw [hwcoord] at hcw
  simp only [Pi.smul_apply, smul_eq_mul] at hcw
  have hscalar : (x - e) 0 = 0 := by
    apply (mul_eq_zero.mp hcw.symm).resolve_right (sigma_nonzero w)
  have hvcoord : (x - e) v = -1 := by simp [e, hxv]
  rw [hvcoord] at hcv
  simp [hscalar] at hcv

theorem tree_iff_one_missing (m : Mask) : IsSpanningTwoTree m ↔ ExactlyOneMissing m := by
  constructor
  · intro ht
    obtain ⟨v, hv⟩ := tree_has_missing_face m ht
    refine ⟨v, fun i => ⟨fun hi => tree_has_only_one_missing_face m ht i v hi hv, ?_⟩⟩
    intro hiv
    simpa [hiv] using hv
  · exact one_missing_is_tree m

noncomputable def treeCount : ℕ := by
  classical
  exact (Finset.univ.filter (fun m : Mask => IsSpanningTwoTree m)).card

theorem spanning_two_tree_count : treeCount = 4 := by
  classical
  unfold treeCount
  have hfilter : (Finset.univ.filter (fun m : Mask => IsSpanningTwoTree m)) = goodMasks := by
    ext m
    simp [goodMasks, tree_iff_one_missing]
  rw [hfilter, good_mask_count]

/-- The actual unweighted top-dimensional combinatorial Laplacian. -/
def L₂ : Matrix Face Face ℚ := B₂.transpose * B₂

noncomputable def characteristic : ℚ[X] := L₂.charpoly

theorem characteristic_degree : characteristic.natDegree = 4 := by
  simp [characteristic]

theorem characteristic_monic : characteristic.Monic := Matrix.charpoly_monic L₂

theorem fourth_derivative : Polynomial.derivative^[4] characteristic = Polynomial.C 24 := by
  have hdeg : (Polynomial.derivative^[4] characteristic).natDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa [characteristic_degree] using Polynomial.natDegree_iterate_derivative characteristic 4
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg]
  congr 1
  rw [Polynomial.coeff_iterate_derivative]
  have hlead : characteristic.coeff 4 = 1 := by
    simpa [characteristic_degree] using characteristic_monic.coeff_natDegree
  norm_num [hlead, Nat.descFactorial]

theorem fourth_derivative_at_one : (Polynomial.derivative^[4] characteristic).eval 1 = 24 := by
  rw [fourth_derivative]
  simp

theorem tree_count_ne_prescribed_derivative :
    (treeCount : ℚ) ≠ (Polynomial.derivative^[Fintype.card Face] characteristic).eval 1 := by
  change (treeCount : ℚ) ≠ (Polynomial.derivative^[4] characteristic).eval 1
  rw [spanning_two_tree_count, fourth_derivative_at_one]
  norm_num

#print axioms tree_iff_one_missing
#print axioms spanning_two_tree_count
#print axioms fourth_derivative_at_one
#print axioms tree_count_ne_prescribed_derivative

end Conjecture4222
