import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators
namespace Conjecture7841

/-- Vertices and edge labels of a cyclic multigraph.  Edge `i` joins `i` to `i+1`.
For order two there are two parallel edges; these must not be simplified away. -/
abbrev Vertex (n : ℕ) := ZMod n

/-- The actual number of original cycle edges crossing a Boolean vertex cut. -/
def cut (n : ℕ) [NeZero n] (A : Vertex n → Bool) : ℤ :=
  ∑ i : Vertex n, if A i ≠ A (i + 1) then 1 else 0

def Proper {n : ℕ} (A : Vertex n → Bool) : Prop :=
  (∃ i, A i = true) ∧ (∃ i, A i = false)

/-- Rotate edge `e` to edge zero, before contracting its endpoints. -/
def rotation (n : ℕ) (e : Vertex n) (x : Vertex n) : Vertex n := x - e

/-- Contract the edge 0--1 in the cycle of order n+3; retain every other edge. -/
def collapse (n : ℕ) (x : Vertex (n + 3)) : Vertex (n + 2) :=
  ((x.val - 1 : ℕ) : Vertex (n + 2))

def contract (n : ℕ) (e : Vertex (n + 3)) : Vertex (n + 3) → Vertex (n + 2) :=
  collapse n ∘ rotation (n + 3) e

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

end Conjecture7841




namespace Conjecture7841

lemma collapse_zero (n : ℕ) : collapse n 0 = 0 := by simp [collapse]
lemma collapse_one (n : ℕ) : collapse n 1 = 0 := by
  letI : Fact (1 < n+3) := ⟨by omega⟩
  simp only [collapse]
  rw [ZMod.val_one (n+3)]
  norm_num

/-- Each surviving source edge has exactly the endpoints of its target edge. -/
lemma collapse_edge (n : ℕ) (i : Vertex (n+3)) (hi : i ≠ 0) :
    collapse n (i+1) = collapse n i + 1 := by
  letI : Fact (1 < n+3) := ⟨by omega⟩
  letI : Fact (1 < n+2) := ⟨by omega⟩
  have hval : i.val < n + 3 := ZMod.val_lt i
  have hpos : 0 < i.val := Nat.pos_of_ne_zero (by simpa using hi)
  have hs : (i+1).val = (i.val+1) % (n+3) := by
    rw [ZMod.val_add, ZMod.val_one]
  unfold collapse
  rw [hs]
  by_cases htop : i.val+1 = n+3
  · rw [htop, Nat.mod_self]
    have hv : i.val - 1 = n+1 := by omega
    rw [hv]
    apply ZMod.val_injective
    simp only [Nat.sub_eq_zero_of_le (show 0 ≤ 1 by omega), Nat.cast_zero, ZMod.val_zero, ZMod.val_add, ZMod.val_natCast, ZMod.val_one]
    rw [Nat.mod_eq_of_lt (show n+1 < n+2 by omega)]
    have hn : n+1+1 = n+2 := by omega
    rw [hn, Nat.mod_self]
  · have hlt : i.val+1 < n+3 := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have hsub : i.val+1-1 = i.val := by omega
    rw [hsub]
    have heq : i.val = (i.val-1)+1 := by omega
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun k : ℕ => (k : Vertex (n+2))) heq

lemma collapse_surjective (n : ℕ) : Function.Surjective (collapse n) := by
  intro y
  refine ⟨((y.val+1 : ℕ) : Vertex (n+3)), ?_⟩
  have hy : y.val < n+2 := ZMod.val_lt y
  simp only [collapse, ZMod.val_natCast]
  rw [Nat.mod_eq_of_lt (by omega), Nat.add_sub_cancel]
  exact ZMod.natCast_zmod_val y

lemma surviving_edge_bijection (n : ℕ) :
    Function.Bijective (fun i : {i : Vertex (n+3) // i ≠ 0} => collapse n i.1) := by
  constructor
  · intro i j hij
    apply Subtype.ext
    apply ZMod.val_injective
    have hi : i.val.val < n+3 := ZMod.val_lt i.val
    have hj : j.val.val < n+3 := ZMod.val_lt j.val
    have hi0 : 0 < i.val.val := Nat.pos_of_ne_zero (by simpa using i.property)
    have hj0 : 0 < j.val.val := Nat.pos_of_ne_zero (by simpa using j.property)
    have hv := congrArg ZMod.val hij
    simp only [collapse, ZMod.val_natCast] at hv
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
    omega
  · intro y
    refine ⟨⟨((y.val+1 : ℕ) : Vertex (n+3)), ?_⟩, ?_⟩
    · have hy : y.val < n+2 := ZMod.val_lt y
      intro hh
      have hv := congrArg ZMod.val hh
      simp only [ZMod.val_natCast, ZMod.val_zero] at hv
      rw [Nat.mod_eq_of_lt (by omega)] at hv
      omega
    · have hy : y.val < n+2 := ZMod.val_lt y
      simp only [collapse, ZMod.val_natCast]
      rw [Nat.mod_eq_of_lt (by omega), Nat.add_sub_cancel]
      exact ZMod.natCast_zmod_val y

end Conjecture7841



namespace Conjecture7841

lemma sum_collapse (n : ℕ) (f : Vertex (n+2) → ℤ) :
    (∑ i ∈ (Finset.univ : Finset (Vertex (n+3))).erase 0, f (collapse n i)) = ∑ j, f j := by
  apply Finset.sum_bij (fun i _ => collapse n i) (fun _ _ => Finset.mem_univ _)
  · intro i hi j hj hij
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
    have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
    exact congrArg Subtype.val ((surviving_edge_bijection n).1 (a₁ := ⟨i, hi0⟩) (a₂ := ⟨j, hj0⟩) hij)
  · intro j _
    obtain ⟨i, hi⟩ := (surviving_edge_bijection n).2 j
    exact ⟨i.val, Finset.mem_erase.mpr ⟨i.property, Finset.mem_univ _⟩, hi⟩
  · intro _ _
    rfl

lemma cut_collapse (n : ℕ) (A : Vertex (n+2) → Bool) :
    cut (n+3) (A ∘ collapse n) = cut (n+2) A := by
  unfold cut
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Vertex (n+3)))]
  simp only [Function.comp_apply, zero_add, collapse_zero, collapse_one, ne_eq,
    not_true_eq_false, ↓reduceIte, add_zero]
  calc
    _ = ∑ i ∈ (Finset.univ : Finset (Vertex (n+3))).erase 0,
        (if A (collapse n i) ≠ A (collapse n i + 1) then (1 : ℤ) else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [collapse_edge n i (Finset.mem_erase.mp hi).1]
    _ = _ := by simpa only [] using sum_collapse n (fun j => if A j ≠ A (j+1) then (1 : ℤ) else 0)

lemma cut_rotation {n : ℕ} [NeZero n] (A : Vertex n → Bool) (e : Vertex n) :
    cut n (A ∘ rotation n e) = cut n A := by
  unfold cut
  have hr (i : Vertex n) : rotation n e (i+1) = rotation n e i + 1 := by
    dsimp [rotation]; abel
  simp only [Function.comp_apply, hr]
  simpa only [rotation, sub_eq_add_neg, Equiv.addRight] using Equiv.sum_comp (Equiv.addRight (-e)) (fun i => if A i ≠ A (i+1) then (1 : ℤ) else 0)

lemma cut_contract (n : ℕ) (A : Vertex (n+2) → Bool) (e : Vertex (n+3)) :
    cut (n+3) (A ∘ contract n e) = cut (n+2) A := by
  change cut (n+3) ((A ∘ collapse n) ∘ rotation (n+3) e) = _
  rw [cut_rotation, cut_collapse]

lemma contract_surjective (n : ℕ) (e : Vertex (n+3)) :
    Function.Surjective (contract n e) := by
  apply (collapse_surjective n).comp
  intro y
  refine ⟨y+e, ?_⟩
  simp [rotation]

lemma proper_pullback {m n : ℕ} {A : Vertex n → Bool} (ha : Proper A)
    (f : Vertex m → Vertex n) (hf : Function.Surjective f) : Proper (A ∘ f) := by
  rcases ha with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  obtain ⟨x, hx⟩ := hf i
  obtain ⟨y, hy⟩ := hf j
  exact ⟨⟨x, by simpa [Function.comp_apply, hx]⟩, ⟨y, by simpa [Function.comp_apply, hy]⟩⟩

end Conjecture7841



namespace Conjecture7841

/-- A full sequence of random edge choices.  At each stage all currently remaining
edges are distinct labels, including the parallel edges in the final two-cycle. -/
def History : ℕ → Type
  | 0 => Unit
  | k+1 => Vertex (k+3) × History k

instance historyFintype : (k : ℕ) → Fintype (History k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k+1 => by
    change Fintype (Vertex (k+3) × History k)
    letI := historyFintype k
    infer_instance

instance historyNonempty : (k : ℕ) → Nonempty (History k)
  | 0 => inferInstanceAs (Nonempty Unit)
  | k+1 => by
    change Nonempty (Vertex (k+3) × History k)
    letI := historyNonempty k
    infer_instance

/-- At two supervertices return their unique bipartition.  Every recursive step
pulls this actual vertex cut back along the explicit contraction map. -/
def output : (k : ℕ) → History k → Vertex (k+2) → Bool
  | 0, _ => fun x => decide (x = 0)
  | k+1, (e, h) => output k h ∘ contract k e

lemma terminal_proper : Proper (fun x : Vertex 2 => decide (x = 0)) := by
  constructor
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩

lemma terminal_cut : cut 2 (fun x : Vertex 2 => decide (x = 0)) = 2 := by
  decide

lemma every_history_proper : ∀ (k : ℕ) (h : History k), Proper (output k h)
  | 0, _ => terminal_proper
  | k+1, (e,h) => proper_pullback (every_history_proper k h) _ (contract_surjective k e)

lemma every_history_cut : ∀ (k : ℕ) (h : History k), cut (k+2) (output k h) = 2
  | 0, _ => terminal_cut
  | k+1, (e,h) => (cut_contract k (output k h) e).trans (every_history_cut k h)

/-- Actual success means the output is a nontrivial minimum cut of the original
cycle, not that a preselected minimum cut has survived. -/
def Success (k : ℕ) (h : History k) : Prop :=
  Proper (output k h) ∧ ∀ A : Vertex (k+2) → Bool,
    Proper A → cut (k+2) (output k h) ≤ cut (k+2) A

lemma every_history_success (k : ℕ) (h : History k) : Success k h := by
  refine ⟨every_history_proper k h, ?_⟩
  intro A ha
  rw [every_history_cut]
  exact minimum_cut_lower_bound A ha

/-- Every edge choice is uniform at each stage.  Therefore all full histories have
identical probability, the reciprocal of this Cartesian product's cardinality. -/
noncomputable def successProbability (k : ℕ) : ℝ := by
  classical
  exact ((Finset.univ.filter (Success k)).card : ℝ) / Fintype.card (History k)

lemma history_card_succ (k : ℕ) :
    Fintype.card (History (k+1)) = (k+3) * Fintype.card (History k) := by
  change Fintype.card (Vertex (k+3) × History k) = _
  rw [Fintype.card_prod, ZMod.card]

/-- Karger's actual probability of outputting any minimum cut on C_(k+2). -/
theorem cycle_success_probability (k : ℕ) : successProbability k = 1 := by
  classical
  have hf : Finset.univ.filter (Success k) = (Finset.univ : Finset (History k)) := by
    ext h
    simp [every_history_success k h]
  unfold successProbability
  rw [hf, Finset.card_univ]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

end Conjecture7841


namespace Conjecture7841

lemma chosen_edge_collapses (n : ℕ) (e : Vertex (n+3)) :
    contract n e e = contract n e (e+1) := by
  simp only [contract, Function.comp_apply, rotation, sub_self]
  have he : e+1-e = (1 : Vertex (n+3)) := by abel
  rw [he, collapse_zero, collapse_one]

lemma other_edge_preserved (n : ℕ) (e i : Vertex (n+3)) (hi : i ≠ e) :
    contract n e (i+1) = contract n e i + 1 := by
  have hir : rotation (n+3) e i ≠ 0 := sub_ne_zero.mpr hi
  have hr : rotation (n+3) e (i+1) = rotation (n+3) e i + 1 := by
    dsimp [rotation]; abel
  simp only [contract, Function.comp_apply, hr, collapse_edge n _ hir]

lemma exactly_one_edge_deleted (n : ℕ) (e i : Vertex (n+3)) :
    contract n e i = contract n e (i+1) ↔ i = e := by
  constructor
  · intro h
    by_contra hi
    rw [other_edge_preserved n e i hi] at h
    have h1 : (1 : Vertex (n+2)) = 0 := by
      exact (add_left_cancel (show contract n e i + 0 = contract n e i + 1 by simpa using h)).symm
    have hv := congrArg ZMod.val h1
    rw [ZMod.val_one_eq_one_mod, ZMod.val_zero, Nat.mod_eq_of_lt (by omega)] at hv
    omega
  · rintro rfl
    exact chosen_edge_collapses n i

/-- Source edge labels other than the selected one are in one-to-one correspondence
with every edge of the contracted cycle.  Parallel edges are retained separately. -/
lemma contraction_edge_bijection (n : ℕ) (e : Vertex (n+3)) :
    Function.Bijective (fun i : {i : Vertex (n+3) // i ≠ e} => contract n e i.1) := by
  constructor
  · intro i j hij
    have hi : rotation (n+3) e i.val ≠ 0 := sub_ne_zero.mpr i.property
    have hj : rotation (n+3) e j.val ≠ 0 := sub_ne_zero.mpr j.property
    have heq := congrArg Subtype.val ((surviving_edge_bijection n).1
      (a₁ := ⟨rotation (n+3) e i.val, hi⟩) (a₂ := ⟨rotation (n+3) e j.val, hj⟩) hij)
    apply Subtype.ext
    exact sub_left_injective heq
  · intro y
    obtain ⟨i, hi⟩ := (surviving_edge_bijection n).2 y
    refine ⟨⟨i.val+e, ?_⟩, ?_⟩
    · intro heq
      have : i.val = 0 := add_right_cancel (show i.val+e = 0+e by simpa using heq)
      exact i.property this
    · simpa [contract, rotation] using hi

/-- Every O(1/n) correction is eventually far below the actual cycle success
probability, even if the purported equality is required only at arbitrarily large n. -/
theorem no_cycle_sharpness (ε : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (N : ℕ)
    (hε : ∀ k ≥ N, |ε k| ≤ C / (k+2)) (K : ℕ) :
    ∃ k ≥ K, 2 * (1 - ε k) / (k+2)^2 < successProbability k := by
  obtain ⟨r, hr⟩ := exists_nat_gt C
  let k := r + N + K + 4
  have hkN : N ≤ k := by omega
  have hkK : K ≤ k := by omega
  have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast (show 4 ≤ k by omega)
  have hrk : (r : ℝ) ≤ k := by exact_mod_cast (show r ≤ k by omega)
  have hkC : C < k := lt_of_lt_of_le hr hrk
  have hden : (1 : ℝ) ≤ k+2 := by linarith
  have hsmall : C / (k+2) ≤ C := div_le_self hC hden
  have hbound : -C ≤ ε k := by
    have ht := (abs_le.mp (hε k hkN)).1
    linarith
  refine ⟨k, hkK, ?_⟩
  rw [cycle_success_probability]
  apply (div_lt_iff₀ (sq_pos_of_pos (show (0 : ℝ) < k+2 by linarith))).2
  nlinarith [sq_nonneg ((k : ℝ)-2)]

#print axioms cycle_success_probability
#print axioms no_cycle_sharpness
#print axioms exactly_one_edge_deleted
#print axioms contraction_edge_bijection
#print axioms minimum_cut_lower_bound

end Conjecture7841



namespace Conjecture7841
open Filter Topology

/-- Under even the weaker assumption epsilon tends to zero, the proposed bound
vanishes on cycles, whereas their actual success probability is constantly one. -/
theorem proposed_bound_tends_zero (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k : ℕ => 2 * (1-ε k) / (k+2)^2) atTop (𝓝 0) := by
  have hi : Tendsto (fun k : ℕ => (1 : ℝ) / (k+2)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 2)
  have hn : Tendsto (fun k : ℕ => (2 : ℝ) * (1-ε k)) atTop (𝓝 2) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hε)
  have hh := hn.mul (hi.pow 2)
  simpa only [one_div, one_mul, inv_pow, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), div_eq_mul_inv] using hh

#print axioms proposed_bound_tends_zero
end Conjecture7841



namespace Conjecture7841

/-- Probability of a complete history under actual sequential uniform edge
sampling.  The reciprocal factors are the current numbers of non-loop edges. -/
noncomputable def pathWeight : (k : ℕ) → History k → ℝ
  | 0, _ => 1
  | k+1, (_, h) => (1 / (k+3)) * pathWeight k h

lemma pathWeight_uniform : ∀ (k : ℕ) (h : History k),
    pathWeight k h = 1 / Fintype.card (History k)
  | 0, _ => by simp [pathWeight, History]
  | k+1, (_, h) => by
    rw [pathWeight, pathWeight_uniform k h, history_card_succ]
    push_cast
    simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
    ring

/-- The success probability computed by summing the actual algorithm's path
probabilities over its successful outcomes. -/
noncomputable def actualSuccessProbability (k : ℕ) : ℝ := by
  classical
  exact ∑ h : History k, if Success k h then pathWeight k h else 0

theorem actual_cycle_success_probability (k : ℕ) : actualSuccessProbability k = 1 := by
  classical
  unfold actualSuccessProbability
  simp only [every_history_success, ↓reduceIte, pathWeight_uniform,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card (History k) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact mul_one_div_cancel hc

lemma actual_eq_uniform (k : ℕ) : actualSuccessProbability k = successProbability k := by
  rw [actual_cycle_success_probability, cycle_success_probability]

theorem actual_no_cycle_sharpness (ε : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (N : ℕ)
    (hε : ∀ k ≥ N, |ε k| ≤ C / (k+2)) (K : ℕ) :
    ∃ k ≥ K, 2 * (1 - ε k) / (k+2)^2 < actualSuccessProbability k := by
  simpa only [actual_eq_uniform] using no_cycle_sharpness ε C hC N hε K

#print axioms actual_cycle_success_probability
#print axioms actual_no_cycle_sharpness
#print axioms pathWeight_uniform
end Conjecture7841


namespace Conjecture7841

/-- The actual simple connected input graph; intermediate order-two states retain
parallel edges and are deliberately represented by edge labels, not simplified. -/
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

/-- Crossing of an actual undirected simple-graph edge by a vertex bipartition. -/
def crosses {n : ℕ} (A : Vertex (n+3) → Bool) : Sym2 (Vertex (n+3)) → Bool :=
  Sym2.lift ⟨fun u v => decide (A u ≠ A v), fun u v => by simp [ne_comm]⟩

lemma crossing_label (n : ℕ) (A : Vertex (n+3) → Bool) (i : Vertex (n+3)) :
    crosses A (edgeLabel n i) = decide (A i ≠ A (i+1)) := rfl

/-- The integer cut formula used throughout the algorithm counts precisely the
crossing edges of Mathlib's actual simple cycle input, with no multiplicity proxy. -/
lemma cut_is_actual_edge_count (n : ℕ) (A : Vertex (n+3) → Bool) :
    cut (n+3) A = ∑ e ∈ (inputGraph n).edgeFinset,
      if crosses A e = true then (1 : ℤ) else 0 := by
  rw [input_edges, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i _
    simp only [crossing_label, decide_eq_true_eq]
  · exact fun i _ j _ h => edgeLabel_injective n h

#print axioms input_connected
#print axioms input_edges
#print axioms cut_is_actual_edge_count
end Conjecture7841


namespace Conjecture7841

/-- The quotient map identifies exactly the two endpoints of the selected edge.
This, together with the edge bijection, verifies ordinary multigraph contraction. -/
lemma contraction_vertex_fibers (n : ℕ) (e x y : Vertex (n+3)) :
    contract n e x = contract n e y ↔
      x = y ∨ (x = e ∧ y = e+1) ∨ (x = e+1 ∧ y = e) := by
  have hnext : e+1 ≠ e := by
    intro h
    have h1 : (1 : Vertex (n+3)) = 0 := add_left_cancel (show e+1=e+0 by simpa using h)
    have hv := congrArg ZMod.val h1
    rw [ZMod.val_one_eq_one_mod, ZMod.val_zero, Nat.mod_eq_of_lt (by omega)] at hv
    omega
  have hinj := (contraction_edge_bijection n e).1
  constructor
  · intro h
    by_cases hx : x=e
    · by_cases hy : y=e
      · exact Or.inl (hx.trans hy.symm)
      · have heq : contract n e y = contract n e (e+1) := h.symm.trans (by rw [hx]; exact chosen_edge_collapses n e)
        have hy1 := congrArg Subtype.val (hinj (a₁ := ⟨y,hy⟩) (a₂ := ⟨e+1,hnext⟩) heq)
        exact Or.inr (Or.inl ⟨hx,hy1⟩)
    · by_cases hy : y=e
      · have heq : contract n e x = contract n e (e+1) := h.trans (by rw [hy]; exact chosen_edge_collapses n e)
        have hx1 := congrArg Subtype.val (hinj (a₁ := ⟨x,hx⟩) (a₂ := ⟨e+1,hnext⟩) heq)
        exact Or.inr (Or.inr ⟨hx1,hy⟩)
      · exact Or.inl (congrArg Subtype.val (hinj (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) h))
  · intro h
    rcases h with h|⟨hx,hy⟩|⟨hx,hy⟩
    · rw [h]
    · rw [hx,hy]
      exact chosen_edge_collapses n e
    · rw [hx,hy]
      exact (chosen_edge_collapses n e).symm

#print axioms contraction_vertex_fibers
end Conjecture7841



namespace Conjecture7841

lemma input_vertex_count (n : ℕ) : Fintype.card (Vertex (n+3)) = n+3 := ZMod.card (n+3)

lemma input_edge_count (n : ℕ) : (inputGraph n).edgeFinset.card = n+3 := by
  rw [input_edges, Finset.card_image_of_injective _ (edgeLabel_injective n), Finset.card_univ,
    input_vertex_count]

/-- The output cut of every history is minimum for the edge set of the actual
Mathlib simple connected input C_(n+3), not just for an unrelated numeric model. -/
theorem actual_graph_success (n : ℕ) (h : History (n+1)) :
    Proper (output (n+1) h) ∧
    (∀ A : Vertex (n+3) → Bool, Proper A →
      (∑ e ∈ (inputGraph n).edgeFinset,
        if crosses (output (n+1) h) e = true then (1 : ℤ) else 0) ≤
      ∑ e ∈ (inputGraph n).edgeFinset, if crosses A e = true then (1 : ℤ) else 0) := by
  refine ⟨every_history_proper (n+1) h, ?_⟩
  intro A ha
  rw [← cut_is_actual_edge_count, ← cut_is_actual_edge_count]
  exact (every_history_success (n+1) h).2 A ha

/-- The cycle family of arbitrarily large simple connected inputs, with its
actual success probability and its actual minimum output cut. -/
theorem cycle_counterexample (n : ℕ) :
    (inputGraph n).Connected ∧
    Fintype.card (Vertex (n+3)) = n+3 ∧
    (inputGraph n).edgeFinset.card = n+3 ∧
    actualSuccessProbability (n+1) = 1 ∧
    ∀ h : History (n+1), cut (n+3) (output (n+1) h) = 2 := by
  exact ⟨input_connected n, input_vertex_count n, input_edge_count n,
    actual_cycle_success_probability (n+1), every_history_cut (n+1)⟩

#print axioms actual_graph_success
#print axioms cycle_counterexample
end Conjecture7841

namespace Conjecture7841
open Filter Topology

lemma pathWeight_nonneg (k : ℕ) (h : History k) : 0 ≤ pathWeight k h := by
  rw [pathWeight_uniform]
  exact one_div_nonneg.mpr (Nat.cast_nonneg _)

lemma sum_pathWeight (k : ℕ) : (∑ h : History k, pathWeight k h) = 1 := by
  simp only [pathWeight_uniform, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card (History k) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact mul_one_div_cancel hc

theorem actual_gap_tends_one (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k : ℕ => actualSuccessProbability k - 2 * (1-ε k) / (k+2)^2)
      atTop (𝓝 1) := by
  have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
    (proposed_bound_tends_zero ε hε)
  simpa only [actual_cycle_success_probability, sub_zero] using hh

/-- The difference does not even tend to zero, ruling out additive asymptotic
sharpness as well as the source's claimed exact equality. -/
theorem actual_gap_not_tends_zero (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    ¬ Tendsto (fun k : ℕ => actualSuccessProbability k - 2 * (1-ε k) / (k+2)^2)
      atTop (𝓝 0) := by
  intro hz
  have hh : (1 : ℝ) = 0 := tendsto_nhds_unique (actual_gap_tends_one ε hε) hz
  norm_num at hh

#print axioms pathWeight_nonneg
#print axioms sum_pathWeight
#print axioms actual_gap_tends_one
#print axioms actual_gap_not_tends_zero
end Conjecture7841
