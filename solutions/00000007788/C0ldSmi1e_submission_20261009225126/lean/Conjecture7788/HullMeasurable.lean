import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open Set MeasureTheory
open scoped BigOperators

namespace Conjecture7788

lemma hull_range_image_simplex {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E] (x : ι → E) :
    convexHull ℝ (range x) =
      (fun w : ι → ℝ => ∑ i, w i • x i) '' stdSimplex ℝ ι := by
  let L : (ι → ℝ) →ₗ[ℝ] E := ∑ i, (LinearMap.proj i).smulRight (x i)
  have hL : (fun w : ι → ℝ => ∑ i, w i • x i) = L := by
    ext w
    simp [L, LinearMap.sum_apply]
  rw [hL, ← convexHull_basis_eq_stdSimplex, LinearMap.image_convexHull, ← Set.range_comp]
  congr 1
  ext y
  simp [L, LinearMap.sum_apply, Function.comp_def, ite_smul, Finset.filter_eq]

lemma hull_graph_closed (N : ℕ) :
    IsClosed {p : (Fin N → EuclideanSpace ℝ (Fin 2)) × EuclideanSpace ℝ (Fin 2) |
      p.2 ∈ convexHull ℝ (range p.1)} := by
  let S := ↥(stdSimplex ℝ (Fin N))
  let A := (Fin N → EuclideanSpace ℝ (Fin 2)) × EuclideanSpace ℝ (Fin 2)
  have hc : Continuous (fun p : A × S => ∑ i, (p.2.val i) • (p.1.1 i)) := by
    dsimp [A, S]
    apply continuous_finset_sum
    intro i _
    exact ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)).smul
      ((continuous_apply i).comp (continuous_fst.comp continuous_fst))
  have he : IsClosed {p : A × S | (∑ i, (p.2.val i) • (p.1.1 i)) = p.1.2} :=
    isClosed_eq hc (show Continuous (fun p : A × S => p.1.2) from by
      dsimp [A, S]
      fun_prop)
  have hi := isClosedMap_fst_of_compactSpace _ he
  convert hi using 1
  ext p
  simp only [mem_setOf_eq, mem_image, Prod.exists, exists_and_right, exists_eq_right]
  rw [hull_range_image_simplex]
  simp only [mem_image]
  exact ⟨fun ⟨w, hw, h⟩ => ⟨⟨w, hw⟩, h⟩, fun ⟨w, h⟩ => ⟨w.val, w.property, h⟩⟩

lemma hull_volume_measurable (N : ℕ) :
    Measurable (fun x : Fin N → EuclideanSpace ℝ (Fin 2) =>
      volume (convexHull ℝ (range x))) := by
  have h := measurable_measure_prodMk_left (ν := (volume : Measure (EuclideanSpace ℝ (Fin 2))))
    (hull_graph_closed N).measurableSet
  exact h

end Conjecture7788
