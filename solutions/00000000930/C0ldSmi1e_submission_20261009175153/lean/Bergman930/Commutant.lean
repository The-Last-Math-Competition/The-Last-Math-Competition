import Bergman930.Bergman
import Mathlib.LinearAlgebra.Projection
import Mathlib.SetTheory.Cardinal.Continuum

noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology
namespace Bergman930

/-- Every complex-linear map commuting with M_z acts pointwise by its value on 1.
No boundedness or continuity assumption on the map is needed. -/
theorem commuting_map_apply (P : A2 →ₗ[ℂ] A2)
    (hP : P.comp shift = shift.comp P) (f : A2) (w : ℂ) (hw : w ∈ disk) :
    P f w = f w * P one w := by
  have hc (g : A2) : P (shift g) = shift (P g) := LinearMap.congr_fun hP g
  have h := congrArg (fun g : A2 => P g w) (division_identity f w hw)
  simp only [map_sub, map_smul, sub_apply, smul_apply, hc, shift_apply] at h
  have he : P f w - f w * P one w = 0 := by simpa only [sub_self] using h
  exact sub_eq_zero.mp he

/-- The commutant of the actual Bergman shift has no nontrivial idempotents. -/
theorem commuting_idempotent_eq_zero_or_id (P : A2 →ₗ[ℂ] A2)
    (hP : P.comp shift = shift.comp P) (hI : P.comp P = P) :
    P = 0 ∨ P = LinearMap.id := by
  have he (w : ℂ) (hw : w ∈ disk) : P one w * (P one w - 1) = 0 := by
    have hi := congrArg (fun f : A2 => f w) (LinearMap.congr_fun hI one)
    change P (P one) w = P one w at hi
    rw [commuting_map_apply P hP (P one) w hw] at hi
    calc
      P one w * (P one w - 1) = P one w * P one w - P one w := by ring
      _ = 0 := sub_eq_zero.mpr hi
  have hd := (holomorphic (P one)).analyticOnNhd disk_open
  rcases hd.eq_zero_or_eq_zero_of_mul_eq_zero (hd.sub analyticOnNhd_const) he
      (convex_ball (0 : ℂ) 1).isPreconnected with hzero | hone
  · left
    apply LinearMap.ext
    intro f
    ext w hw
    simp [commuting_map_apply P hP f w hw, hzero w hw]
  · right
    apply LinearMap.ext
    intro f
    ext w hw
    have hw' : P one w = 1 := sub_eq_zero.mp (hone w hw)
    simp [commuting_map_apply P hP f w hw, hw']

/-- Invariance under multiplication by z. -/
def Invariant (M : Submodule ℂ A2) : Prop := ∀ f ∈ M, shift f ∈ M

/-- A stronger algebraic conclusion: every invariant subspace having an invariant
algebraic complement is trivial. -/
theorem invariant_complemented_eq_bot_or_top (M N : Submodule ℂ A2)
    (hMN : IsCompl M N) (hM : Invariant M) (hN : Invariant N) : M = ⊥ ∨ M = ⊤ := by
  let p : A2 →ₗ[ℂ] M := M.linearProjOfIsCompl N hMN
  let P : A2 →ₗ[ℂ] A2 := M.subtype.comp p
  have hleft (f : M) : P f = f := by
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hMN f)
  have hright (f : N) : P f = 0 := by
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hMN f)
  have hid : P.comp P = P := by
    apply LinearMap.ext
    intro f
    exact hleft (p f)
  have hcomm : P.comp shift = shift.comp P := by
    apply LinearMap.ext
    intro f
    obtain ⟨u, v, huv, _⟩ := Submodule.existsUnique_add_of_isCompl hMN f
    rw [← huv]
    have hlu : P (shift u) = shift u := hleft ⟨shift u, hM u u.2⟩
    have hrv : P (shift v) = 0 := hright ⟨shift v, hN v v.2⟩
    change P (shift ((u : A2) + v)) = shift (P ((u : A2) + v))
    simp only [map_add, hlu, hrv, hleft u, hright v, add_zero]
  rcases commuting_idempotent_eq_zero_or_id P hcomm hid with hzero | hone
  · left
    apply (Submodule.eq_bot_iff M).mpr
    intro f hf
    have h := hleft ⟨f, hf⟩
    simpa only [hzero, LinearMap.zero_apply] using h.symm
  · right
    apply Submodule.eq_top_iff'.mpr
    intro f
    have h : P f ∈ M := (p f).2
    simpa only [hone, LinearMap.id_apply] using h

end Bergman930
