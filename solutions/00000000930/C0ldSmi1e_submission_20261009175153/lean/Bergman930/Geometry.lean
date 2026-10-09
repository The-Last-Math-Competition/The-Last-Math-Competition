import Bergman930.Commutant
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.InnerProductSpace.Projection

noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology ComplexConjugate
namespace Bergman930

/-- The canonical map to genuine L² equivalence classes for Lebesgue area. -/
def toL2 : A2 →ₗ[ℂ] Lp ℂ 2 area where
  toFun f := (square_integrable f).toLp f
  map_add' f g := MemLp.toLp_add (square_integrable f) (square_integrable g)
  map_smul' c f := MemLp.toLp_const_smul c (square_integrable f)

theorem toL2_injective : Function.Injective toL2 := by
  intro f g h
  have hae : (f : ℂ → ℂ) =ᵐ[area] g :=
    ((square_integrable f).toLp_eq_toLp_iff (square_integrable g)).mp h
  have hpt := Measure.eqOn_open_of_ae_eq hae disk_open
    (holomorphic f).continuousOn (holomorphic g).continuousOn
  exact ext (fun z hz => hpt hz)

/-- The exact Bergman space as a subspace of genuine area-L². -/
def l2Space : Submodule ℂ (Lp ℂ 2 area) := LinearMap.range toL2

/-- No square-integrable holomorphic functions are lost, identified, or added. -/
def functionEquivL2 : A2 ≃ₗ[ℂ] l2Space := LinearEquiv.ofInjective toL2 toL2_injective

/-- The Bergman shift in the L² realization, conjugate to actual M_z. -/
def l2Shift : l2Space →ₗ[ℂ] l2Space :=
  functionEquivL2.toLinearMap.comp (shift.comp functionEquivL2.symm.toLinearMap)

/-- The L² inner product is conjugate-linear in the first variable and linear in
  the second, exactly as in Mathlib. -/
theorem inner_toL2 (f g : A2) :
    @inner ℂ _ _ (toL2 f) (toL2 g) = ∫ z, conj (f z) * g z ∂area := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(square_integrable f).coeFn_toLp,
    (square_integrable g).coeFn_toLp] with z hf hg
  simp [toL2, hf, hg, mul_comm]

end Bergman930
