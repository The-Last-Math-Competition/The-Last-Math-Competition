import Mathlib.Data.Real.StarOrdered
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option maxRecDepth 4096
open scoped BigOperators Matrix
open Matrix
namespace Conjecture8908

abbrev V := Fin 5
abbrev M := Matrix V V ℝ

def graph : SimpleGraph V := SimpleGraph.cycleGraph 5
instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel (SimpleGraph.cycleGraph 5).Adj)

noncomputable def objective (X : M) : ℝ := ∑ i, ∑ j, X i j

def Feasible (G : SimpleGraph V) (X : M) : Prop :=
  X.PosSemidef ∧ X.trace = 1 ∧ ∀ i j, G.Adj i j → X i j = 0

noncomputable def feasibleValues (G : SimpleGraph V) : Set ℝ :=
  {x | ∃ X : M, Feasible G X ∧ objective X = x}

/-- The full standard Lovasz theta SDP, not a chosen witness objective. -/
noncomputable def theta (G : SimpleGraph V) : ℝ := sSup (feasibleValues G)

noncomputable def b : V → ℝ := ![-9,32,8,8,32]
noncomputable def B : M := fun i j => b (j-i)
noncomputable def witness : M := (1/11285 : ℝ) • (Bᴴ * B)

lemma gram_entry (i j : V) : (Bᴴ * B) i j =
    if i = j then 2257 else if graph.Adj i j then 0 else 1392 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [B, b, graph, SimpleGraph.cycleGraph_adj, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, Fin.sub_def, Fin.neg_def, Fin.add_def, Fin.ext_iff]

lemma gram_psd : (Bᴴ * B).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self B

lemma entry_bound (X : M) (hx : X.PosSemidef) (i j : V) :
    2 * X i j ≤ X i i + X j j := by
  have hsym : X j i = X i j := by
    have h := congrArg (fun A : M => A i j) hx.1
    simpa using h
  have h := hx.2 (Pi.single i 1 - Pi.single j 1)
  simp only [star_trivial, mulVec_sub, mulVec_single_one,
    sub_dotProduct, dotProduct_sub, single_dotProduct, one_mul, sub_apply, Matrix.transpose_apply, hsym] at h

  linarith

end Conjecture8908


namespace Conjecture8908

lemma witness_psd : witness.PosSemidef := by
  constructor
  · have hh := gram_psd.1
    change (((1/11285 : ℝ) • (Bᴴ * B))ᴴ) = (1/11285 : ℝ) • (Bᴴ * B)
    rw [Matrix.conjTranspose_smul, hh]
    simp
  · intro x
    have hh := gram_psd.2 x
    change 0 ≤ dotProduct (star x) (((1/11285 : ℝ) • (Bᴴ * B)) *ᵥ x)
    rw [Matrix.smul_mulVec_assoc, dotProduct_smul]
    exact mul_nonneg (by norm_num) hh

lemma witness_entry (i j : V) : witness i j =
    if i = j then (1/5 : ℝ) else if graph.Adj i j then 0 else 1392/11285 := by
  simp only [witness, Matrix.smul_apply, smul_eq_mul, gram_entry]
  split_ifs <;> norm_num

lemma witness_feasible : Feasible graph witness := by
  refine ⟨witness_psd, ?_, ?_⟩
  · norm_num [Matrix.trace, witness_entry, Fin.sum_univ_succ]
  · intro i j hij
    have hn := graph.ne_of_adj hij
    simp [witness_entry, hn, hij]

lemma witness_matrix : witness =
    !![(1/5 : ℝ),0,1392/11285,1392/11285,0;
       0,1/5,0,1392/11285,1392/11285;
       1392/11285,0,1/5,0,1392/11285;
       1392/11285,1392/11285,0,1/5,0;
       0,1392/11285,1392/11285,0,1/5] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witness_entry, graph, SimpleGraph.cycleGraph_adj,
      Fin.sub_def, Fin.neg_def, Fin.add_def, Fin.ext_iff]
lemma witness_row_sum (i : V) : (∑ j : V, witness i j) = 5041/11285 := by
  rw [witness_matrix]
  fin_cases i <;> norm_num [Fin.sum_univ_succ]

lemma witness_objective : objective witness = 5041/2257 := by
  unfold objective
  simp only [witness_row_sum]
  norm_num

lemma objective_bounded (X : M) (hx : Feasible graph X) : objective X ≤ 5 := by
  have hh : 2 * objective X ≤ ∑ i : V, ∑ j : V, (X i i + X j j) := by
    calc
      _ = ∑ i : V, ∑ j : V, 2 * X i j := by simp only [objective, Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => entry_bound X hx.1 i j))
  have hs : (∑ i : V, ∑ j : V, (X i i + X j j)) = 10 * X.trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
    ring
  rw [hs, hx.2.1] at hh
  linarith

lemma feasible_nonempty : (feasibleValues graph).Nonempty :=
  ⟨objective witness, witness, witness_feasible, rfl⟩

lemma feasible_bounded : BddAbove (feasibleValues graph) := by
  refine ⟨5, ?_⟩
  rintro y ⟨X,hx,rfl⟩
  exact objective_bounded X hx

lemma theta_lower_bound : 5041/2257 ≤ theta graph := by
  change 5041/2257 ≤ sSup (feasibleValues graph)
  exact le_csSup feasible_bounded ⟨witness,witness_feasible,witness_objective⟩

lemma theta_greater_two : (2 : ℝ) < theta graph := by
  have hh := theta_lower_bound
  norm_num at hh ⊢
  linarith

end Conjecture8908

namespace Conjecture8908

lemma complement_clique_upper : ∀ s : Finset V, graphᶜ.IsClique s → s.card ≤ 2 := by
  decide

lemma complement_maximum_pair : graphᶜ.IsMaximumClique ({0,2} : Finset V) := by
  refine ⟨?_, ?_⟩
  · decide
  · intro t ht
    have hh := complement_clique_upper t ht
    norm_num at hh ⊢
    exact hh

lemma complement_clique_number : graphᶜ.cliqueNum = 2 := by
  have h := SimpleGraph.maximumClique_card_eq_cliqueNum ({0,2} : Finset V) complement_maximum_pair
  have hc : ({0,2} : Finset V).card = 2 := by decide
  rw [hc] at h
  exact h.symm

lemma independence_number : graph.indepNum = 2 := by
  rw [← SimpleGraph.cliqueNum_compl, complement_clique_number]

/-- Both alleged endpoints equal two, while the full standard theta SDP is
strictly larger.  Thus it cannot lie in any monotone chain between them. -/
theorem counterexample :
    graph.indepNum = 2 ∧ graphᶜ.cliqueNum = 2 ∧
    (graphᶜ.cliqueNum : ℝ) < theta graph := by
  refine ⟨independence_number, complement_clique_number, ?_⟩
  rw [complement_clique_number]
  exact theta_greater_two

theorem no_claimed_chain :
    ¬ ((graph.indepNum : ℝ) ≤ theta graph ∧ theta graph ≤ (graphᶜ.cliqueNum : ℝ)) := by
  intro h
  exact not_le_of_gt counterexample.2.2 h.2

#print axioms witness_feasible
#print axioms feasible_nonempty
#print axioms feasible_bounded
#print axioms theta_lower_bound
#print axioms complement_clique_number
#print axioms counterexample
#print axioms no_claimed_chain
end Conjecture8908






