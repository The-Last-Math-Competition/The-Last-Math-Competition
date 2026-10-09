import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Tactic

/-!
The ordinary unweighted Bergman space of the open complex unit disk. Functions
are represented by their zero extensions off the disk. Area is unnormalized
Lebesgue measure dx dy. This choice rescales the usual normalized inner product
by the positive constant pi and changes neither reducing subspaces nor M_z.
-/
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology
namespace Bergman930

def disk : Set ℂ := ball 0 1

def area : Measure ℂ := volume.restrict disk

theorem disk_open : IsOpen disk := isOpen_ball

theorem disk_measurable : MeasurableSet disk := disk_open.measurableSet

theorem zero_mem_disk : (0 : ℂ) ∈ disk := by simp [disk]

instance : IsFiniteMeasure area :=
  isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne

/-- Exactly the square-integrable holomorphic functions on the open unit disk,
with unique zero extension outside it. -/
def space : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | DifferentiableOn ℂ f disk ∧ MemLp f 2 area ∧
    ∀ z, z ∉ disk → f z = 0}
  zero_mem' := ⟨differentiableOn_const 0, MemLp.zero, by simp⟩
  add_mem' := by
    rintro f g ⟨hf, hfm, hfo⟩ ⟨hg, hgm, hgo⟩
    exact ⟨hf.add hg, hfm.add hgm, fun z hz => by simp [hfo z hz, hgo z hz]⟩
  smul_mem' := by
    rintro c f ⟨hf, hfm, hfo⟩
    exact ⟨hf.const_smul c, hfm.const_smul c, fun z hz => by simp [hfo z hz]⟩

abbrev A2 := ↥space

instance : CoeFun A2 (fun _ => ℂ → ℂ) := ⟨fun f => f.1⟩

theorem holomorphic (f : A2) : DifferentiableOn ℂ f disk := f.2.1

theorem square_integrable (f : A2) : MemLp f 2 area := f.2.2.1

theorem zero_off_disk (f : A2) (z : ℂ) (hz : z ∉ disk) : f z = 0 := f.2.2.2 z hz

@[ext] theorem ext {f g : A2} (h : ∀ z ∈ disk, f z = g z) : f = g := by
  apply Subtype.ext
  funext z
  by_cases hz : z ∈ disk
  · exact h z hz
  · rw [zero_off_disk f z hz, zero_off_disk g z hz]

@[simp] theorem zero_apply (z : ℂ) : (0 : A2) z = 0 := rfl
@[simp] theorem add_apply (f g : A2) (z : ℂ) : (f + g) z = f z + g z := rfl
@[simp] theorem sub_apply (f g : A2) (z : ℂ) : (f - g) z = f z - g z := rfl
@[simp] theorem smul_apply (c : ℂ) (f : A2) (z : ℂ) : (c • f) z = c * f z := rfl

/-- The constant-one holomorphic function, zero-extended off the disk. -/
def one : A2 := ⟨disk.indicator (fun _ => (1 : ℂ)), by
  refine ⟨(differentiableOn_const 1).congr ?_, ?_, ?_⟩
  · intro z hz
    exact indicator_of_mem hz _
  · exact MemLp.indicator disk_measurable (memLp_const 1)
  · intro z hz
    exact indicator_of_not_mem hz _⟩

@[simp] theorem one_apply (z : ℂ) (hz : z ∈ disk) : one z = 1 :=
  by exact indicator_of_mem hz (fun _ => (1 : ℂ))

theorem one_ne_zero : one ≠ 0 := by
  intro h
  have h' := congrArg (fun f : A2 => f 0) h
  simp [one_apply 0 zero_mem_disk] at h'

instance : Nontrivial A2 := ⟨⟨one, 0, one_ne_zero⟩⟩

/-- Multiplication by the actual independent variable z. -/
def shift : A2 →ₗ[ℂ] A2 where
  toFun f := ⟨fun z => z * f z, by
    refine ⟨differentiableOn_id.mul (holomorphic f), ?_, ?_⟩
    · apply (square_integrable f).norm.mono'
        ((continuousOn_id.mul (holomorphic f).continuousOn).aestronglyMeasurable disk_measurable)
      filter_upwards [ae_restrict_mem disk_measurable] with z hz
      rw [norm_mul]
      have hz' : ‖z‖ < 1 := by simpa [disk] using hz
      exact mul_le_of_le_one_left (norm_nonneg _) hz'.le
    · intro z hz
      simp [zero_off_disk f z hz]⟩
  map_add' f g := by ext z hz; simp [mul_add]
  map_smul' c f := by ext z hz; simp [mul_left_comm]

@[simp] theorem shift_apply (f : A2) (z : ℂ) : shift f z = z * f z := rfl

/-- The holomorphic divided difference belongs to A². -/
theorem dslope_memLp (f : A2) (w : ℂ) (hw : w ∈ disk) :
    MemLp (dslope f w) 2 area := by
  have hd : DifferentiableOn ℂ (dslope f w) disk :=
    (Complex.differentiableOn_dslope (disk_open.mem_nhds hw)).mpr (holomorphic f)
  have hc : ContinuousAt (dslope f w) w :=
    continuousAt_dslope_same.mpr ((holomorphic f).differentiableAt (disk_open.mem_nhds hw))
  obtain ⟨r, hr, hbound⟩ := Metric.eventually_nhds_iff.mp
    (hc.norm.eventually (gt_mem_nhds (lt_add_one ‖dslope f w w‖)))
  let C : ℝ := ‖dslope f w w‖ + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm : MemLp (fun z => C + r⁻¹ * (‖f z‖ + ‖f w‖)) 2 area :=
    (memLp_const C).add (((square_integrable f).norm.add (memLp_const ‖f w‖)).const_mul r⁻¹)
  apply hm.mono' (hd.continuousOn.aestronglyMeasurable disk_measurable)
  filter_upwards with z
  by_cases hz : dist z w < r
  · exact (hbound hz).le.trans (le_add_of_nonneg_right (by positivity))
  · have hrz : r ≤ ‖z - w‖ := by simpa [dist_eq_norm] using le_of_not_gt hz
    have hzw : z ≠ w := by intro h; subst z; simp at hrz; linarith
    rw [dslope_of_ne f hzw, slope, norm_smul, norm_inv]
    calc
      ‖z - w‖⁻¹ * ‖f z - f w‖ ≤ r⁻¹ * (‖f z‖ + ‖f w‖) := by
        apply mul_le_mul (inv_anti₀ hr hrz) (norm_sub_le _ _) (norm_nonneg _)
        positivity
      _ ≤ C + r⁻¹ * (‖f z‖ + ‖f w‖) := le_add_of_nonneg_left hC

/-- Zero extension of the holomorphic divided difference. -/
def dividedDifference (f : A2) (w : ℂ) (hw : w ∈ disk) : A2 :=
  ⟨disk.indicator (dslope f w), by
    refine ⟨?_, MemLp.indicator disk_measurable (dslope_memLp f w hw), ?_⟩
    · apply ((Complex.differentiableOn_dslope (disk_open.mem_nhds hw)).mpr (holomorphic f)).congr
      intro z hz
      exact indicator_of_mem hz _
    · intro z hz
      exact indicator_of_not_mem hz _⟩

@[simp] theorem dividedDifference_apply (f : A2) (w : ℂ) (hw : w ∈ disk)
    (z : ℂ) (hz : z ∈ disk) : dividedDifference f w hw z = dslope f w z :=
  indicator_of_mem hz _

/-- The local-division identity in the actual function space. -/
theorem division_identity (f : A2) (w : ℂ) (hw : w ∈ disk) :
    f - f w • one = shift (dividedDifference f w hw) - w • dividedDifference f w hw := by
  ext z hz
  simp only [sub_apply, smul_apply, one_apply z hz, mul_one, shift_apply,
    dividedDifference_apply f w hw z hz]
  simpa only [smul_eq_mul, sub_mul] using (sub_smul_dslope f w z).symm

end Bergman930
