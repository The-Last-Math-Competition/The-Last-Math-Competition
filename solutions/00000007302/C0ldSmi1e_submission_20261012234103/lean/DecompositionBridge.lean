import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.NormedSpace.PiTensorProduct.ProjectiveSeminorm

open scoped BigOperators TensorProduct

namespace DecompositionBridge

noncomputable section

abbrev Factor := EuclideanSpace ℝ (Fin 2)
abbrev Factors := Fin 3 → Factor
abbrev Tensor := PiTensorProduct ℝ (fun _ : Fin 3 => Factor)
abbrev WeightedList := FreeAddMonoid (ℝ × Factors)

/-- Move a coefficient into the zeroth tensor factor. -/
def absorb (p : ℝ × Factors) : Factors :=
  Function.update p.2 0 (p.1 • p.2 0)

@[simp] theorem tprod_absorb (p : ℝ × Factors) :
    PiTensorProduct.tprod ℝ (absorb p) = p.1 • PiTensorProduct.tprod ℝ p.2 := by
  simp [absorb]

@[simp] theorem cost_absorb (p : ℝ × Factors) :
    (∏ i : Fin 3, ‖absorb p i‖) = ‖p.1‖ * ∏ i : Fin 3, ‖p.2 i‖ := by
  simp [absorb, Fin.prod_univ_succ, norm_smul, mul_assoc]

/-- An ordinary finite sum of pure tensors, with no separate scalar coefficients. -/
def ordinarySum (l : List Factors) : Tensor :=
  (l.map (fun m => PiTensorProduct.tprod ℝ m)).sum

/-- The sum of products of factor norms for an ordinary decomposition. -/
def ordinaryCost (l : List Factors) : ℝ :=
  (l.map (fun m => ∏ i : Fin 3, ‖m i‖)).sum

def weightedToOrdinary (p : WeightedList) : List Factors := p.toList.map absorb

def ordinaryToWeighted (l : List Factors) : WeightedList :=
  FreeAddMonoid.ofList (l.map (fun m => ((1 : ℝ), m)))

theorem ordinarySum_weightedToOrdinary (p : WeightedList) :
    ordinarySum (weightedToOrdinary p) =
      (p.toList.map (fun q => q.1 • PiTensorProduct.tprod ℝ q.2)).sum := by
  simp [ordinarySum, weightedToOrdinary, List.map_map, Function.comp_def]

theorem ordinaryCost_weightedToOrdinary (p : WeightedList) :
    ordinaryCost (weightedToOrdinary p) = PiTensorProduct.projectiveSeminormAux p := by
  simp [ordinaryCost, weightedToOrdinary, PiTensorProduct.projectiveSeminormAux,
    List.map_map, Function.comp_def]

theorem weightedToOrdinary_sum {x : Tensor} {p : WeightedList}
    (hp : p ∈ PiTensorProduct.lifts x) : ordinarySum (weightedToOrdinary p) = x := by
  rw [ordinarySum_weightedToOrdinary]
  exact (PiTensorProduct.mem_lifts_iff x p).mp hp

theorem ordinaryToWeighted_mem_lifts {x : Tensor} {l : List Factors}
    (hl : ordinarySum l = x) : ordinaryToWeighted l ∈ PiTensorProduct.lifts x := by
  rw [PiTensorProduct.mem_lifts_iff]
  simpa [ordinaryToWeighted, ordinarySum, List.map_map, Function.comp_def] using hl

theorem projectiveSeminormAux_ordinaryToWeighted (l : List Factors) :
    PiTensorProduct.projectiveSeminormAux (ordinaryToWeighted l) = ordinaryCost l := by
  simp [ordinaryToWeighted, ordinaryCost, PiTensorProduct.projectiveSeminormAux,
    List.map_map, Function.comp_def]

/-- All costs of ordinary finite pure-tensor decompositions of `x`. -/
def ordinaryCosts (x : Tensor) : Set ℝ :=
  {r | ∃ l : List Factors, ordinarySum l = x ∧ ordinaryCost l = r}

/-- Every tensor admits an ordinary finite pure-tensor decomposition. -/
theorem ordinaryDecomposition_exists (x : Tensor) :
    ∃ l : List Factors, ordinarySum l = x := by
  obtain ⟨p, hp⟩ := PiTensorProduct.nonempty_lifts x
  exact ⟨weightedToOrdinary p, weightedToOrdinary_sum hp⟩

theorem ordinaryCost_nonneg (l : List Factors) : 0 ≤ ordinaryCost l := by
  rw [← projectiveSeminormAux_ordinaryToWeighted]
  exact PiTensorProduct.projectiveSeminormAux_nonneg _

theorem ordinaryCosts_nonempty (x : Tensor) : (ordinaryCosts x).Nonempty := by
  obtain ⟨l, hl⟩ := ordinaryDecomposition_exists x
  exact ⟨ordinaryCost l, l, hl, rfl⟩

/-- Zero is a lower bound for all feasible ordinary decomposition costs. -/
theorem ordinaryCosts_bddBelow (x : Tensor) : BddBelow (ordinaryCosts x) := by
  refine ⟨0, ?_⟩
  rintro r ⟨l, _, rfl⟩
  exact ordinaryCost_nonneg l

/-- Weighted lifts and ordinary finite decompositions attain exactly the same costs. -/
theorem costRange_eq (x : Tensor) :
    Set.range (fun p : PiTensorProduct.lifts x => PiTensorProduct.projectiveSeminormAux p.1) =
      ordinaryCosts x := by
  ext r
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨weightedToOrdinary p.1, weightedToOrdinary_sum p.2,
      ordinaryCost_weightedToOrdinary p.1⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨ordinaryToWeighted l, ordinaryToWeighted_mem_lifts hl⟩,
      projectiveSeminormAux_ordinaryToWeighted l⟩

/-- Mathlib's projective seminorm is the infimum over ordinary finite decompositions. -/
theorem projectiveSeminorm_eq_sInf_ordinaryCosts (x : Tensor) :
    PiTensorProduct.projectiveSeminorm x = sInf (ordinaryCosts x) := by
  rw [PiTensorProduct.projectiveSeminorm_apply]
  change sInf (Set.range _) = sInf (ordinaryCosts x)
  rw [costRange_eq]

end

end DecompositionBridge
