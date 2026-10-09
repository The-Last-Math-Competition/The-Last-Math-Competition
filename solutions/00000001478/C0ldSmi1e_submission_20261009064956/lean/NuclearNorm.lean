import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
The complex 2 x 2 x 2 tensor nuclear norm, with Euclidean norms on all three factors.
Every admissible cost is the sum of products of factor norms in a finite rank-one
expansion. No coordinate bound or desired conclusion is built into the definition.
-/
namespace TLMC1478

noncomputable section

abbrev Vector := EuclideanSpace ℂ (Fin 2)
abbrev Tensor := Fin 2 → Fin 2 → Fin 2 → ℂ
abbrev FactorTriple := Vector × Vector × Vector

/-- The coordinate array of a pure tensor. Zero factors are allowed in decompositions. -/
noncomputable def rankOne (a b c : Vector) : Tensor := fun i j k => a i * b j * c k

noncomputable def termTensor (v : FactorTriple) : Tensor := rankOne v.1 v.2.1 v.2.2

def termCost (v : FactorTriple) : ℝ := ‖v.1‖ * ‖v.2.1‖ * ‖v.2.2‖

/-- All finite rank-one decomposition costs for the given tensor. -/
def decompositionCosts (T : Tensor) : Set ℝ :=
  {r | ∃ L : List FactorTriple,
    (L.map termTensor).sum = T ∧ (L.map termCost).sum = r}

/-- The usual complex tensor nuclear (projective) norm, as its infimum formula. -/
noncomputable def nuclearNorm (T : Tensor) : ℝ := sInf (decompositionCosts T)

noncomputable def nuclearBall : Set Tensor := {T | nuclearNorm T ≤ 1}

theorem termCost_nonneg (v : FactorTriple) : 0 ≤ termCost v := by
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)

theorem decompositionCosts_bddBelow (T : Tensor) : BddBelow (decompositionCosts T) := by
  refine ⟨0, ?_⟩
  rintro r ⟨L, _, rfl⟩
  exact List.sum_nonneg (fun x hx => by
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
    exact termCost_nonneg v)

/-- The standard coordinate expansion uses exactly the eight complex tensor entries. -/
def coordinateTerm (T : Tensor) (q : Fin 2 × Fin 2 × Fin 2) : FactorTriple :=
  (EuclideanSpace.single q.1 (T q.1 q.2.1 q.2.2),
    EuclideanSpace.single q.2.1 1, EuclideanSpace.single q.2.2 1)

theorem coordinate_expansion (T : Tensor) :
    ∑ q : Fin 2 × Fin 2 × Fin 2, termTensor (coordinateTerm T q) = T := by
  classical
  ext i j k
  simp [termTensor, coordinateTerm, rankOne, EuclideanSpace.single_apply,
    Fintype.sum_prod_type]

/-- The defining infimum is never over an empty set. -/
theorem decompositionCosts_nonempty (T : Tensor) : (decompositionCosts T).Nonempty := by
  classical
  let L := (Finset.univ : Finset (Fin 2 × Fin 2 × Fin 2)).toList.map (coordinateTerm T)
  refine ⟨(L.map termCost).sum, L, ?_, rfl⟩
  simpa only [L, List.map_map, Function.comp_def, Finset.sum_map_toList] using
    coordinate_expansion T

/-- A coordinate of a pure tensor is bounded by its genuine decomposition cost. -/
theorem norm_termTensor_le (v : FactorTriple) (i j k : Fin 2) :
    ‖termTensor v i j k‖ ≤ termCost v := by
  simp only [termTensor, rankOne, norm_mul, termCost]
  exact mul_le_mul
    (mul_le_mul (PiLp.norm_apply_le v.1 i) (PiLp.norm_apply_le v.2.1 j)
      (norm_nonneg _) (norm_nonneg _))
    (PiLp.norm_apply_le v.2.2 k) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem norm_list_sum_coordinate_le (L : List FactorTriple) (i j k : Fin 2) :
    ‖(L.map termTensor).sum i j k‖ ≤ (L.map termCost).sum := by
  induction L with
  | nil => simp
  | cons v L ih =>
    simpa only [List.map_cons, List.sum_cons, Pi.add_apply] using
      (norm_add_le (termTensor v i j k) ((L.map termTensor).sum i j k)).trans
        (add_le_add (norm_termTensor_le v i j k) ih)

theorem coordinate_le_nuclearNorm (T : Tensor) (i j k : Fin 2) :
    ‖T i j k‖ ≤ nuclearNorm T := by
  apply le_csInf (decompositionCosts_nonempty T)
  rintro r ⟨L, hT, rfl⟩
  rw [← hT]
  exact norm_list_sum_coordinate_le L i j k

theorem nuclearNorm_nonneg (T : Tensor) : 0 ≤ nuclearNorm T := by
  exact (norm_nonneg (T 0 0 0)).trans (coordinate_le_nuclearNorm T 0 0 0)

/-- If the minimum cost is exhibited, the infimum definition equals that minimum. -/
theorem nuclearNorm_eq_minimum (T : Tensor) (m : ℝ)
    (hm : m ∈ decompositionCosts T) (hle : ∀ r ∈ decompositionCosts T, m ≤ r) :
    nuclearNorm T = m := by
  exact le_antisymm (csInf_le (decompositionCosts_bddBelow T) hm)
    (le_csInf (decompositionCosts_nonempty T) hle)

theorem nuclearNorm_rankOne_le (a b c : Vector) :
    nuclearNorm (rankOne a b c) ≤ ‖a‖ * ‖b‖ * ‖c‖ := by
  apply csInf_le (decompositionCosts_bddBelow _)
  exact ⟨[(a,b,c)], by simp [termTensor], by simp [termCost]⟩

theorem nuclearNorm_zero : nuclearNorm (0 : Tensor) = 0 := by
  apply le_antisymm _ (nuclearNorm_nonneg _)
  apply csInf_le (decompositionCosts_bddBelow _)
  exact ⟨[], by simp, by simp⟩

def basisTensor : Tensor := rankOne (EuclideanSpace.single 0 1)
  (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)

@[simp] theorem basisTensor_origin : basisTensor 0 0 0 = 1 := by
  simp [basisTensor, rankOne, EuclideanSpace.single_apply]

theorem nuclearNorm_basisTensor : nuclearNorm basisTensor = 1 := by
  apply le_antisymm
  · simpa only [EuclideanSpace.norm_single, norm_one, mul_one] using
      nuclearNorm_rankOne_le (EuclideanSpace.single 0 1)
        (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)
  · simpa using coordinate_le_nuclearNorm basisTensor 0 0 0

theorem zero_mem_nuclearBall : (0 : Tensor) ∈ nuclearBall := by
  simp [nuclearBall, nuclearNorm_zero]

theorem basisTensor_mem_nuclearBall : basisTensor ∈ nuclearBall := by
  simp [nuclearBall, nuclearNorm_basisTensor]

theorem nuclearBall_coordinate_bound {T : Tensor} (hT : T ∈ nuclearBall) (i j k : Fin 2) :
    ‖T i j k‖ ≤ 1 :=
  (coordinate_le_nuclearNorm T i j k).trans hT

/-- A pure tensor vanishes exactly when at least one factor vanishes. -/
theorem termTensor_eq_zero_iff (v : FactorTriple) :
    termTensor v = 0 ↔ v.1 = 0 ∨ v.2.1 = 0 ∨ v.2.2 = 0 := by
  constructor
  · intro hv
    by_contra h
    push_neg at h
    obtain ⟨i, hi⟩ : ∃ i, v.1 i ≠ 0 := by
      by_contra ha
      push_neg at ha
      apply h.1
      ext i
      exact ha i
    obtain ⟨j, hj⟩ : ∃ j, v.2.1 j ≠ 0 := by
      by_contra hb
      push_neg at hb
      apply h.2.1
      ext j
      exact hb j
    obtain ⟨k, hk⟩ : ∃ k, v.2.2 k ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply h.2.2
      ext k
      exact hc k
    have hvalue := congrFun (congrFun (congrFun hv i) j) k
    exact (mul_ne_zero (mul_ne_zero hi hj) hk) hvalue
  · rintro (ha | hb | hc) <;> ext i j k <;> simp [termTensor, rankOne, *]

theorem termCost_eq_zero_of_tensor_zero (v : FactorTriple) (hv : termTensor v = 0) :
    termCost v = 0 := by
  rcases (termTensor_eq_zero_iff v).mp hv with (ha | hb | hc) <;> simp [termCost, *]

/-- Deleting zero pure tensors preserves both tensor sum and scalar cost. -/
theorem remove_zero_terms (L : List FactorTriple) :
    ∃ K : List FactorTriple,
      (∀ v ∈ K, termTensor v ≠ 0) ∧
      (K.map termTensor).sum = (L.map termTensor).sum ∧
      (K.map termCost).sum = (L.map termCost).sum := by
  classical
  induction L with
  | nil => exact ⟨[], by simp⟩
  | cons v L ih =>
    obtain ⟨K, hK, hsum, hcost⟩ := ih
    by_cases hv : termTensor v = 0
    · refine ⟨K, hK, ?_, ?_⟩
      · simpa only [List.map_cons, List.sum_cons, hv, zero_add] using hsum
      · simpa only [List.map_cons, List.sum_cons, termCost_eq_zero_of_tensor_zero v hv,
          zero_add] using hcost
    · refine ⟨v :: K, ?_, ?_, ?_⟩
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hv
        · exact hK w hw
      · simp only [List.map_cons, List.sum_cons, hsum]
      · simp only [List.map_cons, List.sum_cons, hcost]

/-- Allowing zero factors does not alter the costs obtainable using actual
nonzero rank-one (decomposable) tensors. -/
theorem mem_decompositionCosts_iff_nonzero_terms (T : Tensor) (r : ℝ) :
    r ∈ decompositionCosts T ↔ ∃ L : List FactorTriple,
      (∀ v ∈ L, termTensor v ≠ 0) ∧
      (L.map termTensor).sum = T ∧ (L.map termCost).sum = r := by
  constructor
  · rintro ⟨L, hsum, hcost⟩
    obtain ⟨K, hK, hKsum, hKcost⟩ := remove_zero_terms L
    exact ⟨K, hK, hKsum.trans hsum, hKcost.trans hcost⟩
  · rintro ⟨L, _, hsum, hcost⟩
    exact ⟨L, hsum, hcost⟩

/-- Literal attained-minimum version of the source's wording. -/
noncomputable def minimumNuclearBall : Set Tensor :=
  {T | ∃ r, IsLeast (decompositionCosts T) r ∧ r ≤ 1}

/-- Any attained minimum is the same value as the usual infimum definition. -/
theorem minimumNuclearBall_subset : minimumNuclearBall ⊆ nuclearBall := by
  rintro T ⟨r, hr, hr1⟩
  change nuclearNorm T ≤ 1
  rw [nuclearNorm_eq_minimum T r hr.1 (fun s hs => hr.2 hs)]
  exact hr1

/-- A decomposition achieving the infimum is a genuine minimum decomposition. -/
theorem isLeast_cost_of_mem_of_norm_eq {T : Tensor} {r : ℝ}
    (hr : r ∈ decompositionCosts T) (heq : nuclearNorm T = r) :
    IsLeast (decompositionCosts T) r := by
  refine ⟨hr, ?_⟩
  intro s hs
  rw [← heq]
  exact csInf_le (decompositionCosts_bddBelow T) hs

theorem zero_mem_minimumNuclearBall : (0 : Tensor) ∈ minimumNuclearBall := by
  refine ⟨0, isLeast_cost_of_mem_of_norm_eq ?_ nuclearNorm_zero, zero_le_one⟩
  exact ⟨[], by simp, by simp⟩

theorem basisTensor_mem_minimumNuclearBall : basisTensor ∈ minimumNuclearBall := by
  refine ⟨1, isLeast_cost_of_mem_of_norm_eq ?_ nuclearNorm_basisTensor, le_rfl⟩
  refine ⟨[(EuclideanSpace.single 0 1, EuclideanSpace.single 0 1,
    EuclideanSpace.single 0 1)], ?_, ?_⟩
  · simp [termTensor, basisTensor]
  · simp [termCost, EuclideanSpace.norm_single]

end

end TLMC1478
