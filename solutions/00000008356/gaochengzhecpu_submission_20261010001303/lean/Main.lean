import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Conjecture8356
open SimpleGraph Matrix
open scoped BigOperators
abbrev V := Fin 3
abbrev Mask := Fin 3 → Bool

def graphOf (m : Mask) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v =>
    (u = 0 ∧ v = 1 ∧ m 0 = true) ∨
    (u = 0 ∧ v = 2 ∧ m 1 = true) ∨
    (u = 1 ∧ v = 2 ∧ m 2 = true))

instance (m : Mask) : DecidableRel (graphOf m).Adj := by
  intro u v
  dsimp only [graphOf, SimpleGraph.fromRel]
  infer_instance

def edgeCount (m : Mask) : ℕ := (Finset.univ.filter (fun i => m i = true)).card

theorem tree_iff (m : Mask) : (graphOf m).IsTree ↔ edgeCount m = 2 := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
  exact (show ∀ m : Mask, (graphOf m).Connected ∧
    (graphOf m).edgeFinset.card + 1 = Fintype.card V ↔ edgeCount m = 2 by decide) m

noncomputable def maskOf (G : SimpleGraph V) : Mask := by
  classical
  exact ![decide (G.Adj 0 1), decide (G.Adj 0 2), decide (G.Adj 1 2)]

theorem graphOf_maskOf (G : SimpleGraph V) : graphOf (maskOf G) = G := by
  classical
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [graphOf, SimpleGraph.fromRel, maskOf, SimpleGraph.adj_comm] <;>
      exact G.adj_comm _ _

theorem maskOf_graphOf (m : Mask) : maskOf (graphOf m) = m := by
  classical
  funext i
  fin_cases i <;> simp [graphOf, SimpleGraph.fromRel, maskOf]

def K3 : SimpleGraph V := ⊤
instance : DecidableRel K3.Adj := inferInstanceAs (DecidableRel (⊤ : SimpleGraph V).Adj)

abbrev SpanningTree := {T : SimpleGraph V // T ≤ K3 ∧ T.IsTree}

noncomputable def treeEquiv : {m : Mask // edgeCount m = 2} ≃ SpanningTree where
  toFun m := ⟨graphOf m.1, le_top, (tree_iff m.1).2 m.2⟩
  invFun T := ⟨maskOf T.1, (tree_iff _).1 (by rw [graphOf_maskOf]; exact T.2.2)⟩
  left_inv m := Subtype.ext (maskOf_graphOf m.1)
  right_inv T := Subtype.ext (graphOf_maskOf T.1)

theorem spanning_tree_count : Nat.card SpanningTree = 3 := by
  rw [← Nat.card_congr treeEquiv, Nat.card_eq_fintype_card]
  decide


/-- The three chosen orientations of the three actual edges of K3. -/
def tail : V → V := ![0,1,2]
def head : V → V := ![1,2,0]

theorem oriented_edges_are_actual :
    ∀ u v : V, K3.Adj u v ↔
      ∃ e : V, (tail e = u ∧ head e = v) ∨ (tail e = v ∧ head e = u) := by
  decide

def incidence : Matrix V V ℤ := fun v e =>
  (if head e = v then 1 else 0) - (if tail e = v then 1 else 0)

def boundary : (V → ℤ) →ₗ[ℤ] (V → ℤ) := Matrix.mulVecLin incidence

theorem incidence_matrix : incidence = !![-1,0,1; 1,-1,0; 0,1,-1] := by
  decide

theorem boundary_formula (z : V → ℤ) :
    boundary z = ![z 2 - z 0, z 0 - z 1, z 1 - z 2] := by
  change incidence *ᵥ z = ![z 2 - z 0, z 0 - z 1, z 1 - z 2]
  rw [incidence_matrix]
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- Integral first homology of this graph is the kernel of its edge boundary. -/
abbrev CycleLattice := LinearMap.ker boundary

theorem cycle_coordinates (z : CycleLattice) (i : V) : z.1 i = z.1 0 := by
  have hz : boundary z.1 = 0 := z.2
  rw [boundary_formula] at hz
  have h0 := congrFun hz 0
  have h1 := congrFun hz 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
  fin_cases i
  · rfl
  · change z.1 (1 : V) = z.1 0
    linarith
  · change z.1 (2 : V) = z.1 0
    linarith

def cycleEquiv : CycleLattice ≃ₗ[ℤ] (Fin 1 → ℤ) where
  toFun z := fun _ => z.1 0
  invFun a := ⟨fun _ => a 0, by
    change boundary (fun _ => a 0) = 0
    rw [boundary_formula]
    ext i
    fin_cases i <;> simp⟩
  left_inv z := by
    apply Subtype.ext
    funext i
    exact (cycle_coordinates z i).symm
  right_inv a := by
    funext i
    fin_cases i
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def cycleBasis : Basis (Fin 1) ℤ CycleLattice :=
  Basis.ofEquivFun cycleEquiv

theorem cycle_basis_value (i : Fin 1) (e : V) : (cycleBasis i).1 e = 1 := by
  rw [cycleBasis, Basis.coe_ofEquivFun]
  fin_cases i
  simp [cycleEquiv]

noncomputable def edgeLength (_ : V) : ℝ := 1 / 2

theorem positive_edge_lengths (e : V) : 0 < edgeLength e := by
  norm_num [edgeLength]

/-- The length pairing restricted to integral cycles. -/
noncomputable def lengthPairing (z w : CycleLattice) : ℝ :=
  ∑ e : V, edgeLength e * (z.1 e : ℝ) * (w.1 e : ℝ)

/-- The Gram matrix of an actual integral cycle basis. -/
noncomputable def gram : Matrix (Fin 1) (Fin 1) ℝ :=
  fun i j => lengthPairing (cycleBasis i) (cycleBasis j)

theorem gram_entry (i j : Fin 1) : gram i j = 3 / 2 := by
  norm_num [gram, lengthPairing, cycle_basis_value, edgeLength, Fin.sum_univ_succ]

theorem jacobian_lattice_determinant : Matrix.det gram = (3 : ℝ) / 2 := by
  rw [Matrix.det_fin_one]
  exact gram_entry 0 0

theorem determinant_ne_spanning_tree_count :
    Matrix.det gram ≠ (Nat.card SpanningTree : ℝ) := by
  rw [jacobian_lattice_determinant, spanning_tree_count]
  norm_num

/-- The alternative convention using the Euclidean covolume also fails. -/
theorem covolume_ne_spanning_tree_count :
    Real.sqrt (Matrix.det gram) ≠ (Nat.card SpanningTree : ℝ) := by
  rw [jacobian_lattice_determinant, spanning_tree_count]
  intro h
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 / 2 by norm_num)
  rw [h] at hs
  norm_num at hs

#print axioms spanning_tree_count
#print axioms oriented_edges_are_actual
#print axioms cycle_coordinates
#print axioms cycle_basis_value
#print axioms jacobian_lattice_determinant
#print axioms determinant_ne_spanning_tree_count
#print axioms covolume_ne_spanning_tree_count
end Conjecture8356
