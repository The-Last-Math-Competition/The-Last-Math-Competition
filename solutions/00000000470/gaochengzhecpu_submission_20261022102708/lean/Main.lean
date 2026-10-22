import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped BigOperators Matrix
namespace Conjecture470
abbrev Vertex (n : ℕ) := ZMod n
/-- The actual number of original cycle edges crossing a Boolean vertex cut. -/
def cut (n : ℕ) [NeZero n] (A : Vertex n → Bool) : ℤ :=
  ∑ i : Vertex n, if A i ≠ A (i + 1) then 1 else 0

def Proper {n : ℕ} (A : Vertex n → Bool) : Prop :=
  (∃ i, A i = true) ∧ (∃ i, A i = false)

lemma shift_sum {n : ℕ} [NeZero n] (f : Vertex n → ℤ) :
    (∑ i, f (i + 1)) = ∑ i, f i := by
  exact Equiv.sum_comp (Equiv.addRight (1 : Vertex n)) f

lemma cut_even {n : ℕ} [NeZero n] (A : Vertex n → Bool) :
    ∃ r : ℕ, cut n A = 2 * r := by
  let r : ℕ := ∑ i : Vertex n, if A i = false ∧ A (i+1) = true then 1 else 0
  refine ⟨r, ?_⟩
  have point (i : Vertex n) :
      (if A i ≠ A (i + 1) then (1 : ℤ) else 0) =
      2 * (if A i = false ∧ A (i+1) = true then 1 else 0) +
      (if A i = true then 1 else 0) - (if A (i+1) = true then 1 else 0) := by
    cases h : A i <;> cases h' : A (i+1) <;> simp [h, h']
  unfold cut
  simp_rw [point]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    shift_sum (fun i => if A i = true then 1 else 0)]
  simp only [add_sub_cancel_right]
  congr 1
  simp [r, Nat.cast_sum]

lemma constant_of_no_crossing {n : ℕ} [NeZero n] (A : Vertex n → Bool)
    (h : ∀ i, A i = A (i+1)) : ∀ i, A i = A 0 := by
  have allnat (k : ℕ) : A (k : Vertex n) = A 0 := by
    induction k with
    | zero => simp
    | succ k ih => simpa only [Nat.cast_add, Nat.cast_one] using (h (k : Vertex n)).symm.trans ih
  intro i
  simpa using allnat i.val

lemma cut_pos {n : ℕ} [NeZero n] (A : Vertex n → Bool) (ha : Proper A) :
    0 < cut n A := by
  have hn : 0 ≤ cut n A := Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
  by_contra hp
  have hz : cut n A = 0 := le_antisymm (by omega) hn
  have hall : ∀ i, A i = A (i+1) := by
    intro i
    by_contra hi
    have bound : (if A i ≠ A (i+1) then (1 : ℤ) else 0) ≤ cut n A := by
      unfold cut
      exact Finset.single_le_sum (f := fun j => if A j ≠ A (j+1) then (1 : ℤ) else 0) (fun j _ => by dsimp; split_ifs <;> norm_num) (Finset.mem_univ i)
    simp [hi, hz] at bound
  rcases ha with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  have hc := (constant_of_no_crossing A hall i).trans (constant_of_no_crossing A hall j).symm
  simp [hi, hj] at hc

lemma minimum_cut_lower_bound {n : ℕ} [NeZero n] (A : Vertex n → Bool) (ha : Proper A) :
    2 ≤ cut n A := by
  obtain ⟨r, hr⟩ := cut_even A
  have hp := cut_pos A ha
  omega


def inputGraph (n : ℕ) : SimpleGraph (Vertex (n+3)) := SimpleGraph.cycleGraph (n+3)

instance (n : ℕ) : DecidableRel (inputGraph n).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.cycleGraph (n+3)).Adj)

lemma input_connected (n : ℕ) : (inputGraph n).Connected := SimpleGraph.cycleGraph_connected

lemma input_adj (n : ℕ) (u v : Vertex (n+3)) :
    (inputGraph n).Adj u v ↔ v = u+1 ∨ u = v+1 := by
  change (SimpleGraph.cycleGraph (n+3)).Adj u v ↔ _
  rw [SimpleGraph.cycleGraph_adj]
  constructor
  · intro h
    rcases h with h|h
    · have hh : u = 1+v := sub_eq_iff_eq_add.mp h
      exact Or.inr (by simpa only [add_comm] using hh)
    · have hh : v = 1+u := sub_eq_iff_eq_add.mp h
      exact Or.inl (by simpa only [add_comm] using hh)
  · intro h
    rcases h with h|h
    · apply Or.inr
      apply sub_eq_iff_eq_add.mpr
      simpa only [add_comm] using h
    · apply Or.inl
      apply sub_eq_iff_eq_add.mpr
      simpa only [add_comm] using h

def edgeLabel (n : ℕ) (i : Vertex (n+3)) : Sym2 (Vertex (n+3)) := s(i, i+1)

lemma edgeLabel_injective (n : ℕ) : Function.Injective (edgeLabel n) := by
  intro i j hij
  rcases Sym2.eq_iff.mp hij with ⟨h, _⟩|⟨h, h'⟩
  · exact h
  · have hh : i + (1+1) = i+0 := by
      rw [← add_assoc, h', ← h, add_zero]
    have hzero : (1+1 : Vertex (n+3)) = 0 := add_left_cancel hh
    have hv := congrArg ZMod.val hzero
    rw [show (1+1 : Vertex (n+3)) = 2 by norm_num] at hv
    rw [ZMod.val_two_eq_two_mod, ZMod.val_zero, Nat.mod_eq_of_lt (by omega)] at hv
    omega

lemma input_edges (n : ℕ) :
    (inputGraph n).edgeFinset = Finset.univ.image (edgeLabel n) := by
  ext e
  induction e using Sym2.inductionOn with
  | hf u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, input_adj,
      Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro h
      rcases h with h|h
      · exact ⟨u, by simp [edgeLabel, h]⟩
      · exact ⟨v, Sym2.eq_iff.mpr (Or.inr ⟨rfl, h.symm⟩)⟩
    · rintro ⟨i, hi⟩
      rcases Sym2.eq_iff.mp hi with ⟨hu, hv⟩|⟨hu, hv⟩
      · exact Or.inl (by rw [← hu, ← hv])
      · exact Or.inr (by rw [← hu, ← hv])

lemma input_vertex_count (n : ℕ) : Fintype.card (Vertex (n+3)) = n+3 := ZMod.card (n+3)

lemma input_edge_count (n : ℕ) : (inputGraph n).edgeFinset.card = n+3 := by
  rw [input_edges, Finset.card_image_of_injective _ (edgeLabel_injective n), Finset.card_univ,
    input_vertex_count]


end Conjecture470

namespace Conjecture470

noncomputable def deleted (n : ℕ) (e : Vertex (n+3)) : SimpleGraph (Vertex (n+3)) :=
  (inputGraph n).deleteEdges {edgeLabel n e}

noncomputable instance (n : ℕ) (e : Vertex (n+3)) : Fintype (deleted n e).edgeSet := Fintype.ofFinite _

lemma edge_mem (n : ℕ) (e : Vertex (n+3)) : edgeLabel n e ∈ (inputGraph n).edgeFinset := by
  rw [input_edges]
  exact Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩

lemma no_bridge (n : ℕ) (e : Vertex (n+3)) : ¬ (inputGraph n).IsBridge (edgeLabel n e) := by
  classical
  intro hb
  have hnr : ¬ (deleted n e).Reachable e (e+1) := (SimpleGraph.isBridge_iff.mp hb).2
  let A : Vertex (n+3) → Bool := fun x => decide ((deleted n e).Reachable e x)
  have ha : Proper A := by
    refine ⟨⟨e, ?_⟩, ⟨e+1, ?_⟩⟩
    · have he : (deleted n e).Reachable e e := (SimpleGraph.Walk.nil : (deleted n e).Walk e e).reachable
      simp [A,he]
    · simp [A, hnr]
  have hc (i : Vertex (n+3)) (hi : i ≠ e) : A i = A (i+1) := by
    have hlabel : edgeLabel n i ≠ edgeLabel n e := fun h => hi (edgeLabel_injective n h)
    have hadj : (deleted n e).Adj i (i+1) := by
      rw [deleted, SimpleGraph.deleteEdges_adj]
      refine ⟨(input_adj n i (i+1)).mpr (Or.inl rfl), ?_⟩
      simpa only [Set.mem_singleton_iff, edgeLabel] using hlabel
    have hiff : (deleted n e).Reachable e i ↔ (deleted n e).Reachable e (i+1) :=
      ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩
    simp only [A, hiff]
  have hcut : cut (n+3) A ≤ 1 := by
    unfold cut
    have heq : (∑ i : Vertex (n+3), if A i ≠ A (i+1) then (1 : ℤ) else 0) =
        (if A e ≠ A (e+1) then 1 else 0) := by
      apply Finset.sum_eq_single e
      · intro i _ hi
        simp only [hc i hi, ne_eq, not_true_eq_false, ↓reduceIte]
      · simp
    rw [heq]
    split_ifs <;> norm_num
  have hl := minimum_cut_lower_bound A ha
  omega

lemma deleted_connected (n : ℕ) (e : Vertex (n+3)) : (deleted n e).Connected :=
  (input_connected n).connected_delete_edge_of_not_isBridge (no_bridge n e)

lemma deleted_edges (n : ℕ) (e : Vertex (n+3)) :
    (deleted n e).edgeFinset = (inputGraph n).edgeFinset.erase (edgeLabel n e) := by
  classical
  ext f
  simp [SimpleGraph.mem_edgeFinset, deleted, SimpleGraph.edgeSet_deleteEdges, and_comm]

lemma deleted_isTree (n : ℕ) (e : Vertex (n+3)) : (deleted n e).IsTree := by
  classical
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨deleted_connected n e, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, deleted_edges,
    Finset.card_erase_of_mem (edge_mem n e), input_edge_count, Nat.card_eq_fintype_card,
    input_vertex_count]
  omega

/-- All spanning trees as actual simple subgraphs on the full vertex set. -/
def SpanningTree (n : ℕ) :=
  {T : SimpleGraph (Vertex (n+3)) // T ≤ inputGraph n ∧ T.IsTree}

noncomputable instance (n : ℕ) : Fintype (SpanningTree n) := by
  classical
  unfold SpanningTree
  infer_instance

noncomputable def deletionTree (n : ℕ) (e : Vertex (n+3)) : SpanningTree n :=
  ⟨deleted n e, (inputGraph n).deleteEdges_le _, deleted_isTree n e⟩

lemma deletion_injective (n : ℕ) : Function.Injective (deletionTree n) := by
  classical
  intro i j hij
  have hgraph : deleted n i = deleted n j := congrArg Subtype.val hij
  have hg := congrArg SimpleGraph.edgeSet hgraph
  have hi : edgeLabel n i ∈ (inputGraph n).edgeSet := SimpleGraph.mem_edgeFinset.mp (edge_mem n i)
  by_contra hh
  have hl : edgeLabel n i ≠ edgeLabel n j := fun h => hh (edgeLabel_injective n h)
  have hm : edgeLabel n i ∈ (deleted n j).edgeSet := by
    simp only [deleted, SimpleGraph.edgeSet_deleteEdges, Set.mem_diff, Set.mem_singleton_iff]
    exact ⟨hi,hl⟩
  rw [← hg] at hm
  simp [deleted, SimpleGraph.edgeSet_deleteEdges] at hm
end Conjecture470




namespace Conjecture470

lemma every_tree_is_deletion (n : ℕ) (T : SpanningTree n) :
    ∃ e : Vertex (n+3), deletionTree n e = T := by
  classical
  letI : Fintype T.val.edgeSet := Fintype.ofFinite _
  have hsub : T.val.edgeFinset ⊆ (inputGraph n).edgeFinset := by
    intro e he
    exact SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.edgeSet_mono T.property.1) (SimpleGraph.mem_edgeFinset.mp he))
  have hcard : T.val.edgeFinset.card + 1 = n+3 := by
    simpa only [input_vertex_count] using T.property.2.card_edgeFinset
  have hdiff : ((inputGraph n).edgeFinset \ T.val.edgeFinset).card = 1 := by
    rw [Finset.card_sdiff hsub, input_edge_count]
    omega
  obtain ⟨f,hf⟩ := Finset.card_eq_one.mp hdiff
  have hfm : f ∈ (inputGraph n).edgeFinset :=
    (Finset.mem_sdiff.mp (by rw [hf]; exact Finset.mem_singleton_self f)).1
  rw [input_edges] at hfm
  obtain ⟨e,_,he⟩ := Finset.mem_image.mp hfm
  refine ⟨e, ?_⟩
  apply Subtype.ext
  apply SimpleGraph.edgeSet_injective
  ext g
  have hset : (inputGraph n).edgeSet \ T.val.edgeSet = {f} := by
    ext q
    have hh : q ∈ (inputGraph n).edgeFinset \ T.val.edgeFinset ↔ q = f := by rw [hf]; simp
    simpa only [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, Set.mem_diff, Set.mem_singleton_iff] using hh
  have hdel := (inputGraph n).deleteEdges_sdiff_eq_of_le T.property.1
  rw [hset, ← he] at hdel
  exact Iff.of_eq (congrArg (fun G : SimpleGraph (Vertex (n+3)) => g ∈ G.edgeSet) hdel)

noncomputable def treeEquiv (n : ℕ) : Vertex (n+3) ≃ SpanningTree n :=
  Equiv.ofBijective (deletionTree n) ⟨deletion_injective n, every_tree_is_deletion n⟩

/-- Explicit rotations show that the actual input graph is vertex-transitive. -/
def translateIso (n : ℕ) (d : Vertex (n+3)) : inputGraph n ≃g inputGraph n where
  toEquiv := Equiv.addRight d
  map_rel_iff' := by
    intro u v
    simp only [input_adj, Equiv.coe_addRight]
    constructor
    · intro h
      rcases h with h|h
      · apply Or.inl
        have hh : v+d=(u+1)+d := by simpa only [add_assoc,add_comm,add_left_comm] using h
        exact add_right_cancel hh
      · apply Or.inr
        have hh : u+d=(v+1)+d := by simpa only [add_assoc,add_comm,add_left_comm] using h
        exact add_right_cancel hh
    · intro h
      rcases h with h|h
      · exact Or.inl (by rw [h]; abel)
      · exact Or.inr (by rw [h]; abel)

lemma vertex_transitive (n : ℕ) (u v : Vertex (n+3)) :
    ∃ f : inputGraph n ≃g inputGraph n, f u = v := by
  exact ⟨translateIso n (v-u), by simp [translateIso]⟩

end Conjecture470



namespace Conjecture470
open Polynomial

/-- Nondegenerate iid samples: each coordinate is chosen uniformly from false/true,
which assign actual positive integer edge weights one/two, respectively. -/
abbrev Sample (n : ℕ) := Vertex (n+3) → Bool
noncomputable instance sampleFintype (n : ℕ) : Fintype (Sample n) := Fintype.ofFinite _

def indexWeight {n : ℕ} (σ : Sample n) (i : Vertex (n+3)) : ℕ := if σ i then 2 else 1

noncomputable def edgeWeight (n : ℕ) (σ : Sample n) (f : Sym2 (Vertex (n+3))) : ℕ := by
  classical
  exact if ∃ i, edgeLabel n i = f ∧ σ i = true then 2 else 1

lemma edgeWeight_label (n : ℕ) (σ : Sample n) (i : Vertex (n+3)) :
    edgeWeight n σ (edgeLabel n i) = indexWeight σ i := by
  classical
  have hi : (∃ j, edgeLabel n j = edgeLabel n i ∧ σ j = true) ↔ σ i = true := by
    constructor
    · rintro ⟨j,hj,hσ⟩
      rw [edgeLabel_injective n hj] at hσ
      exact hσ
    · exact fun h => ⟨i,rfl,h⟩
  simp [edgeWeight,indexWeight,hi]

def totalWeight {n : ℕ} (σ : Sample n) : ℕ := ∑ i, indexWeight σ i

noncomputable instance (n : ℕ) (T : SpanningTree n) : Fintype T.val.edgeSet := Fintype.ofFinite _

/-- The weight of a genuine spanning tree is the sum over its actual undirected edges. -/
noncomputable def treeWeight (n : ℕ) (σ : Sample n) (T : SpanningTree n) : ℕ :=
  ∑ f ∈ T.val.edgeFinset, edgeWeight n σ f

/-- Sum over ALL genuine spanning trees of the actual input graph. -/
noncomputable def treePolynomial (n : ℕ) (σ : Sample n) : Polynomial ℂ :=
  ∑ T : SpanningTree n, Polynomial.X ^ treeWeight n σ T

lemma sum_all_weights (n : ℕ) (σ : Sample n) :
    (∑ f ∈ (inputGraph n).edgeFinset, edgeWeight n σ f) = totalWeight σ := by
  classical
  rw [input_edges,Finset.sum_image]
  · simp only [edgeWeight_label,totalWeight]
  · exact fun i _ j _ h => edgeLabel_injective n h

lemma tree_weight_delete (n : ℕ) (σ : Sample n) (e : Vertex (n+3)) :
    treeWeight n σ (deletionTree n e) + indexWeight σ e = totalWeight σ := by
  classical
  have hh := Finset.sum_erase_add (inputGraph n).edgeFinset (edgeWeight n σ) (edge_mem n e)
  rw [sum_all_weights,edgeWeight_label] at hh
  unfold treeWeight
  change (∑ f ∈ (deleted n e).edgeFinset, edgeWeight n σ f) + indexWeight σ e = _
  rw [deleted_edges]
  exact hh

lemma polynomial_sum_omitted (n : ℕ) (σ : Sample n) :
    treePolynomial n σ = ∑ i : Vertex (n+3), Polynomial.X ^ (totalWeight σ - indexWeight σ i) := by
  classical
  rw [treePolynomial, ← Equiv.sum_comp (treeEquiv n)]
  apply Finset.sum_congr rfl
  intro i _
  have hh := tree_weight_delete n σ i
  change Polynomial.X ^ treeWeight n σ (deletionTree n i) = _
  congr 1
  omega

lemma totalWeight_lower (n : ℕ) (σ : Sample n) : n+3 ≤ totalWeight σ := by
  have hh : (∑ _i : Vertex (n+3), (1 : ℕ)) ≤ ∑ i, indexWeight σ i :=
    Finset.sum_le_sum (fun i _ => by unfold indexWeight; split_ifs <;> omega)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,input_vertex_count] using hh

def ones {n : ℕ} (σ : Sample n) : ℕ := (Finset.univ.filter fun i => σ i = false).card
def twos {n : ℕ} (σ : Sample n) : ℕ := (Finset.univ.filter fun i => σ i = true).card

lemma count_partition (n : ℕ) (σ : Sample n) : ones σ + twos σ = n+3 := by
  have hh := Finset.filter_card_add_filter_neg_card_eq_card (s := (Finset.univ : Finset (Vertex (n+3)))) (fun i => σ i = false)
  simpa [ones,twos] using hh

/-- The actual spanning-tree polynomial has at most one nonzero root under every
sample, including every mixed, genuinely random one/two assignment. -/
theorem tree_polynomial_factor (n : ℕ) (σ : Sample n) :
    treePolynomial n σ = Polynomial.X ^ (totalWeight σ - 2) *
      (Polynomial.C (ones σ : ℂ) * Polynomial.X + Polynomial.C (twos σ : ℂ)) := by
  classical
  rw [polynomial_sum_omitted]
  have hw := totalWeight_lower n σ
  have he (i : Vertex (n+3)) :
      (Polynomial.X : Polynomial ℂ) ^ (totalWeight σ - indexWeight σ i) =
      Polynomial.X ^ (totalWeight σ - 2) *
        (if σ i = false then Polynomial.X else 1) := by
    cases h : σ i
    · simp only [indexWeight,h,Bool.false_eq_true,↓reduceIte]
      have hh : totalWeight σ - 1 = totalWeight σ - 2 + 1 := by omega
      rw [hh,pow_succ]
    · simp [indexWeight,h]
  simp_rw [he]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have ht : (Finset.univ.filter fun i : Vertex (n+3) => ¬ σ i = false) =
      Finset.univ.filter (fun i => σ i = true) := by ext i; simp
  rw [ht]
  change ((ones σ : ℕ) : Polynomial ℂ) * Polynomial.X + ((twos σ : ℕ) : Polynomial ℂ) = _
  simp

end Conjecture470


namespace Conjecture470
open Polynomial

def Mixed {n : ℕ} (σ : Sample n) : Prop := 0 < ones σ ∧ 0 < twos σ
instance (n : ℕ) (σ : Sample n) : Decidable (Mixed σ) := inferInstanceAs (Decidable (0 < ones σ ∧ 0 < twos σ))
noncomputable def rootReal {n : ℕ} (σ : Sample n) : ℝ := -(twos σ : ℝ) / (ones σ : ℝ)
noncomputable def negativeRoot {n : ℕ} (σ : Sample n) : ℂ := rootReal σ

lemma rootReal_neg {n : ℕ} {σ : Sample n} (hσ : Mixed σ) : rootReal σ < 0 := by
  have ha : (0 : ℝ) < ones σ := by exact_mod_cast hσ.1
  have hb : (0 : ℝ) < twos σ := by exact_mod_cast hσ.2
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hb) ha

lemma negativeRoot_ne_zero {n : ℕ} {σ : Sample n} (hσ : Mixed σ) : negativeRoot σ ≠ 0 := by
  unfold negativeRoot
  exact_mod_cast ne_of_lt (rootReal_neg hσ)

lemma root_arg {n : ℕ} {σ : Sample n} (hσ : Mixed σ) : (negativeRoot σ).arg = Real.pi :=
  Complex.arg_ofReal_of_neg (rootReal_neg hσ)

lemma linear_ne_zero {n : ℕ} {σ : Sample n} (hσ : Mixed σ) :
    (Polynomial.C (ones σ : ℂ) * Polynomial.X + Polynomial.C (twos σ : ℂ)) ≠ 0 := by
  intro hh
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff 1) hh
  simp at hc
  exact Nat.ne_of_gt hσ.1 hc

lemma linear_roots {n : ℕ} {σ : Sample n} (hσ : Mixed σ) :
    (Polynomial.C (ones σ : ℂ) * Polynomial.X + Polynomial.C (twos σ : ℂ)).roots =
      {negativeRoot σ} := by
  have ha : (ones σ : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hσ.1
  have hh := Polynomial.roots_C_mul_X_add_C_of_IsUnit (twos σ : ℂ) (Units.mk0 (ones σ : ℂ) ha)
  convert hh using 1
  simp only [negativeRoot,rootReal,Units.val_inv_eq_inv_val,Units.val_mk0]
  push_cast
  congr 1
  field_simp

lemma actual_roots (n : ℕ) {σ : Sample n} (hσ : Mixed σ) :
    (treePolynomial n σ).roots =
      (totalWeight σ - 2) • ({0} : Multiset ℂ) + {negativeRoot σ} := by
  rw [tree_polynomial_factor,Polynomial.roots_mul
    (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (linear_ne_zero hσ)),
    Polynomial.roots_X_pow,linear_roots hσ]

lemma actual_nonzero_roots (n : ℕ) {σ : Sample n} (hσ : Mixed σ) :
    ((treePolynomial n σ).roots.filter fun z => z ≠ 0) = {negativeRoot σ} := by
  rw [actual_roots n hσ]
  simp [Multiset.filter_add,Multiset.filter_nsmul,Multiset.filter_singleton,negativeRoot_ne_zero hσ]

/-- Empirical CDF of actual polynomial root arguments, counting multiplicities.
For the full-root convention this uses Mathlib's explicit arg(0)=0. -/
noncomputable def empiricalCDF (zs : Multiset ℂ) (x : ℝ) : ℝ := by
  classical
  exact ((zs.filter fun z => z.arg ≤ x).card : ℝ) / zs.card

noncomputable def uniformCDF (x : ℝ) : ℝ :=
  if x < 0 then 0 else if 2*Real.pi < x then 1 else x / (2*Real.pi)

lemma empiricalCDF_bounds (zs : Multiset ℂ) (x : ℝ) :
    0 ≤ empiricalCDF zs x ∧ empiricalCDF zs x ≤ 1 := by
  classical
  unfold empiricalCDF
  by_cases hz : zs.card = 0
  · have he := Multiset.card_eq_zero.mp hz
    simp [he]
  · have hc : (0 : ℝ) < zs.card := by exact_mod_cast Nat.pos_of_ne_zero hz
    exact ⟨div_nonneg (Nat.cast_nonneg _) hc.le,
      (div_le_one hc).mpr (by exact_mod_cast Multiset.card_le_card (Multiset.filter_le _ _))⟩

lemma uniformCDF_bounds (x : ℝ) : 0 ≤ uniformCDF x ∧ uniformCDF x ≤ 1 := by
  unfold uniformCDF
  split_ifs with h0 h1
  · norm_num
  · norm_num
  · have hp : 0 < 2*Real.pi := by positivity
    exact ⟨div_nonneg (le_of_not_gt h0) hp.le,(div_le_one hp).mpr (le_of_not_gt h1)⟩

/-- Full Kolmogorov distance of the empirical angular measure from uniform
measure on [0,2*pi], defined by its CDF supremum. -/
noncomputable def KS (zs : Multiset ℂ) : ℝ :=
  sSup (Set.range fun x : ℝ => |empiricalCDF zs x - uniformCDF x|)

lemma KS_bounded (zs : Multiset ℂ) :
    BddAbove (Set.range fun x : ℝ => |empiricalCDF zs x - uniformCDF x|) := by
  refine ⟨1, ?_⟩
  rintro y ⟨x,rfl⟩
  have h1 := empiricalCDF_bounds zs x
  have h2 := uniformCDF_bounds x
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma KS_at (zs : Multiset ℂ) (x : ℝ) :
    |empiricalCDF zs x - uniformCDF x| ≤ KS zs :=
  le_csSup (KS_bounded zs) ⟨x,rfl⟩

lemma uniformCDF_pi : uniformCDF Real.pi = 1/2 := by
  have hp := Real.pi_pos
  simp only [uniformCDF,not_lt_of_ge hp.le,↓reduceIte]
  rw [if_neg (by linarith)]
  field_simp
  ring
lemma uniformCDF_zero : uniformCDF 0 = 0 := by simp [uniformCDF,Real.pi_pos.le]

/-- If zero roots are discarded, the actual remaining root measure is delta_pi. -/
theorem nonzero_KS_lower (n : ℕ) {σ : Sample n} (hσ : Mixed σ) :
    (1/2 : ℝ) ≤ KS ((treePolynomial n σ).roots.filter fun z => z ≠ 0) := by
  have hh := KS_at ((treePolynomial n σ).roots.filter fun z => z ≠ 0) Real.pi
  rw [actual_nonzero_roots n hσ] at hh ⊢
  rw [uniformCDF_pi] at hh
  norm_num [empiricalCDF,Multiset.filter_singleton,root_arg hσ] at hh
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)] at hh
  exact hh

/-- With the explicit arg(0)=0 convention, at least half of all roots have angle
zero; this convention also gives a fixed Kolmogorov obstruction. -/
theorem all_KS_lower (n : ℕ) {σ : Sample n} (hσ : Mixed σ) :
    (1/2 : ℝ) ≤ KS (treePolynomial n σ).roots := by
  have hh := KS_at (treePolynomial n σ).roots 0
  have hw := totalWeight_lower n σ
  have harg := root_arg hσ
  have hp := Real.pi_pos
  have hc : (0 : ℝ) < (totalWeight σ - 2 : ℕ) + 1 := by positivity
  have he : empiricalCDF (treePolynomial n σ).roots 0 =
      (totalWeight σ - 2 : ℕ) / ((totalWeight σ - 2 : ℕ) + 1 : ℝ) := by
    rw [actual_roots n hσ]
    simp [empiricalCDF,Multiset.filter_add,Multiset.filter_nsmul,Multiset.filter_singleton,harg,not_le_of_gt hp]
  rw [he,uniformCDF_zero,sub_zero,abs_of_nonneg (by positivity)] at hh
  have hd : (1/2 : ℝ) ≤ (totalWeight σ - 2 : ℕ) / ((totalWeight σ - 2 : ℕ) + 1 : ℝ) := by
    apply (le_div_iff₀ hc).mpr
    have hq : (1 : ℝ) ≤ (totalWeight σ - 2 : ℕ) := by exact_mod_cast (show 1 ≤ totalWeight σ - 2 by omega)
    linarith
  exact hd.trans hh

end Conjecture470




namespace Conjecture470
open Filter Topology

/-- The finite uniform product law on all one/two edge assignments. -/
noncomputable def eventProbability (n : ℕ) (P : Sample n → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / Fintype.card (Sample n)

lemma sample_card (n : ℕ) : Fintype.card (Sample n) = 2^(n+3) := by
  rw [Fintype.card_eq_nat_card, Nat.card_fun]
  have hb : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card]; rfl
  have hv : Nat.card (Vertex (n+3)) = n+3 := by rw [Nat.card_eq_fintype_card,input_vertex_count]
  rw [hb,hv]

lemma event_probability_bounds (n : ℕ) (P : Sample n → Prop) :
    0 ≤ eventProbability n P ∧ eventProbability n P ≤ 1 := by
  classical
  unfold eventProbability
  have hc : (0 : ℝ) < Fintype.card (Sample n) := by exact_mod_cast Fintype.card_pos
  exact ⟨div_nonneg (Nat.cast_nonneg _) hc.le,
    (div_le_one hc).mpr (by exact_mod_cast Finset.card_filter_le (Finset.univ : Finset (Sample n)) P)⟩

lemma total_probability (n : ℕ) : eventProbability n (fun _ => True) = 1 := by
  simp [eventProbability]

/-- The probability of every complete assignment is the product of the one-half
masses of its individual edges.  Thus this is the actual independent fair-bit law. -/
lemma product_assignment_probability (n : ℕ) (σ : Sample n) :
    eventProbability n (fun τ => τ = σ) = ∏ _i : Vertex (n+3), (1/2 : ℝ) := by
  classical
  have he : (Finset.univ.filter fun τ : Sample n => τ = σ) = {σ} := by ext τ; simp
  unfold eventProbability
  rw [Finset.filter_congr_decidable]
  rw [he,Finset.card_singleton,sample_card]
  simp only [Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat,Finset.prod_const,
    Finset.card_univ,input_vertex_count,div_pow,one_pow]
lemma probability_mono (n : ℕ) {P Q : Sample n → Prop} (h : ∀ σ, P σ → Q σ) :
    eventProbability n P ≤ eventProbability n Q := by
  classical
  unfold eventProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show Finset.univ.filter P ⊆ Finset.univ.filter Q by
    intro σ hσ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h σ (Finset.mem_filter.mp hσ).2⟩)

lemma ones_pos_iff (n : ℕ) (σ : Sample n) : 0 < ones σ ↔ ∃ i, σ i = false := by
  simp [ones,Finset.card_pos,Finset.filter_nonempty_iff]
lemma twos_pos_iff (n : ℕ) (σ : Sample n) : 0 < twos σ ↔ ∃ i, σ i = true := by
  simp [twos,Finset.card_pos,Finset.filter_nonempty_iff]

lemma mixed_iff_nonconstant (n : ℕ) (σ : Sample n) :
    Mixed σ ↔ σ ≠ (fun _ => false) ∧ σ ≠ (fun _ => true) := by
  rw [Mixed,ones_pos_iff,twos_pos_iff]
  constructor
  · rintro ⟨⟨i,hi⟩,⟨j,hj⟩⟩
    constructor
    · intro hh
      simp [hh] at hj
    · intro hh
      simp [hh] at hi
  · rintro ⟨hfalse,htrue⟩
    constructor
    · by_contra hh
      push_neg at hh
      have heq : σ = fun _ => true := by funext i; simpa using hh i
      exact htrue heq
    · by_contra hh
      push_neg at hh
      have heq : σ = fun _ => false := by funext i; simpa using hh i
      exact hfalse heq

lemma mixed_count (n : ℕ) :
    (Finset.univ.filter (Mixed (n := n))).card = 2^(n+3) - 2 := by
  classical
  have hf : Finset.univ.filter (Mixed (n := n)) =
      (Finset.univ : Finset (Sample n)) \ {fun _ => false, fun _ => true} := by
    ext σ
    simp [mixed_iff_nonconstant,ne_eq,and_comm]
  have hd : (fun _ : Vertex (n+3) => false) ≠ (fun _ => true) := by
    intro h
    have hh := congrFun h 0
    contradiction
  rw [hf,Finset.card_sdiff (Finset.subset_univ _),Finset.card_pair hd,Finset.card_univ,sample_card]

lemma probability_mixed (n : ℕ) :
    eventProbability n Mixed = 1 - 2 / (2 : ℝ)^(n+3) := by
  unfold eventProbability
  have hm : (Finset.univ.filter (fun σ : Sample n => Mixed σ)).card = 2^(n+3)-2 := by
    convert mixed_count n using 1
  rw [Finset.filter_congr_decidable]
  rw [hm,sample_card]
  have hpow : 0 < (2 : ℕ)^n := pow_pos (by decide) n
  have hle : 2 ≤ (2 : ℕ)^(n+3) := by rw [pow_add]; norm_num; omega
  rw [Nat.cast_sub hle,Nat.cast_pow,Nat.cast_ofNat]
  have hn : (2 : ℝ)^(n+3) ≠ 0 := by positivity
  field_simp

lemma mixed_probability_tends_one :
    Tendsto (fun n : ℕ => eventProbability n Mixed) atTop (𝓝 1) := by
  have hp : Tendsto (fun n : ℕ => (1/2 : ℝ)^(n+3)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]; norm_num : |(1/2 : ℝ)| < 1)).comp
        (tendsto_add_atTop_nat 3)
  have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul hp)
  simpa only [probability_mixed,one_div,one_mul,inv_pow,mul_zero,sub_zero,div_eq_mul_inv] using hh

theorem nonzero_failure_probability (n : ℕ) :
    1 - 2 / (2 : ℝ)^(n+3) ≤ eventProbability n
      (fun σ => 0 < ((treePolynomial n σ).roots.filter fun z => z ≠ 0).card ∧
        (1/2 : ℝ) ≤ KS ((treePolynomial n σ).roots.filter fun z => z ≠ 0)) := by
  rw [← probability_mixed]
  apply probability_mono n
  intro σ hσ
  exact ⟨by rw [actual_nonzero_roots n hσ]; simp, nonzero_KS_lower n hσ⟩

theorem all_failure_probability (n : ℕ) :
    1 - 2 / (2 : ℝ)^(n+3) ≤ eventProbability n
      (fun σ => 0 < (treePolynomial n σ).roots.card ∧
        (1/2 : ℝ) ≤ KS (treePolynomial n σ).roots) := by
  rw [← probability_mixed]
  apply probability_mono n
  intro σ hσ
  exact ⟨by rw [actual_roots n hσ]; simp, all_KS_lower n hσ⟩

/-- With probability tending to one, the actual nonzero-root empirical measure
is nonempty and its Kolmogorov distance is at least one half. -/
theorem nonzero_failure_tends_one :
    Tendsto (fun n : ℕ => eventProbability n (fun σ =>
      0 < ((treePolynomial n σ).roots.filter fun z => z ≠ 0).card ∧
      (1/2 : ℝ) ≤ KS ((treePolynomial n σ).roots.filter fun z => z ≠ 0)))
      atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le mixed_probability_tends_one
    tendsto_const_nhds
  · intro n
    simpa only [probability_mixed] using (nonzero_failure_probability n)
  · intro n
    exact (event_probability_bounds n _).2

/-- The full-root convention arg(0)=0 has the same high-probability obstruction. -/
theorem all_failure_tends_one :
    Tendsto (fun n : ℕ => eventProbability n (fun σ =>
      0 < (treePolynomial n σ).roots.card ∧
      (1/2 : ℝ) ≤ KS (treePolynomial n σ).roots)) atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le mixed_probability_tends_one
    tendsto_const_nhds
  · intro n
    simpa only [probability_mixed] using (all_failure_probability n)
  · intro n
    exact (event_probability_bounds n _).2

theorem nonzero_failure_not_tends_zero :
    ¬ Tendsto (fun n : ℕ => eventProbability n (fun σ =>
      0 < ((treePolynomial n σ).roots.filter fun z => z ≠ 0).card ∧
      (1/2 : ℝ) ≤ KS ((treePolynomial n σ).roots.filter fun z => z ≠ 0)))
      atTop (𝓝 0) := by
  intro h
  have hh := tendsto_nhds_unique nonzero_failure_tends_one h
  norm_num at hh

theorem all_failure_not_tends_zero :
    ¬ Tendsto (fun n : ℕ => eventProbability n (fun σ =>
      0 < (treePolynomial n σ).roots.card ∧
      (1/2 : ℝ) ≤ KS (treePolynomial n σ).roots)) atTop (𝓝 0) := by
  intro h
  have hh := tendsto_nhds_unique all_failure_tends_one h
  norm_num at hh

end Conjecture470

#print axioms Conjecture470.vertex_transitive
#print axioms Conjecture470.treeEquiv
#print axioms Conjecture470.tree_polynomial_factor
#print axioms Conjecture470.actual_roots
#print axioms Conjecture470.product_assignment_probability
#print axioms Conjecture470.nonzero_failure_tends_one
#print axioms Conjecture470.all_failure_tends_one
#print axioms Conjecture470.nonzero_failure_not_tends_zero
#print axioms Conjecture470.all_failure_not_tends_zero








