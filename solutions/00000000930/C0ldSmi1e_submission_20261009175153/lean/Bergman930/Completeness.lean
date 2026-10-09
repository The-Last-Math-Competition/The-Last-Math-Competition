import Bergman930.Evaluation
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

noncomputable section
open Set Metric MeasureTheory Filter Complex
open scoped ENNReal Topology Real
namespace Bergman930

/-- L²-Cauchy sequences of Bergman functions are uniformly Cauchy on smaller disks. -/
theorem uniformCauchy_on_smaller_disk (f : ℕ → A2)
    (hf : CauchySeq (fun n => toL2 (f n))) (t : ℝ) (ht : t < 1) :
    UniformCauchySeqOn (fun n z => f n z) atTop (ball (0 : ℂ) t) := by
  let R : ℝ := (1 - t) / 2
  have hR : 0 < R := by dsimp [R]; linarith
  let K : ℝ := areaConstant / (π * R ^ 2)
  have hK : 0 ≤ K := by dsimp [K, areaConstant]; positivity
  have hK1 : 0 < K + 1 := by linarith
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hf (ε / (K + 1)) (div_pos hε hK1)
  refine ⟨N, fun m hm n hn w hw => ?_⟩
  have hw' : ‖w‖ < t := by simpa using hw
  have hball : closedBall w R ⊆ disk := by
    intro z hz
    have hz' : ‖z - w‖ ≤ R := mem_closedBall_iff_norm.mp hz
    have hnz : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
      simpa only [sub_add_cancel] using norm_add_le (z - w) w
    change z ∈ ball (0 : ℂ) 1
    rw [mem_ball_iff_norm, sub_zero]
    dsimp [R] at hz'
    linarith
  have he := evaluation_bound (f m - f n) w R hR hball
  have hb : dist (f m w) (f n w) ≤ K * dist (toL2 (f m)) (toL2 (f n)) := by
    simpa only [dist_eq_norm, sub_apply, map_sub, K] using he
  calc
    dist (f m w) (f n w) ≤ (K + 1) * dist (toL2 (f m)) (toL2 (f n)) :=
      hb.trans (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg)
    _ < (K + 1) * (ε / (K + 1)) := mul_lt_mul_of_pos_left (hN m hm n hn) hK1
    _ = ε := mul_div_cancel₀ ε hK1.ne'

theorem exists_pointwise_limit (f : ℕ → A2)
    (hf : CauchySeq (fun n => toL2 (f n))) (z : ℂ) (hz : z ∈ disk) :
    ∃ c : ℂ, Tendsto (fun n => f n z) atTop (𝓝 c) := by
  have hz' : ‖z‖ < 1 := by simpa [disk] using hz
  obtain ⟨t, hzt, ht⟩ := exists_between hz'
  exact cauchySeq_tendsto_of_complete
    ((uniformCauchy_on_smaller_disk f hf t ht).cauchySeq (by simpa using hzt))

/-- The holomorphic area-L² subspace is closed in genuine L². -/
theorem l2Space_isClosed : IsClosed (l2Space : Set (Lp ℂ 2 area)) := by
  classical
  apply isSeqClosed_iff_isClosed.mp
  intro u U hu hU
  choose f hfu using hu
  have hconv : Tendsto (fun n => toL2 (f n)) atTop (𝓝 U) := by
    simpa only [hfu] using hU
  have hc : CauchySeq (fun n => toL2 (f n)) := hconv.cauchySeq
  let g : ℂ → ℂ := fun z => if hz : z ∈ disk then
    Classical.choose (exists_pointwise_limit f hc z hz) else 0
  have hglim (z : ℂ) (hz : z ∈ disk) : Tendsto (fun n => f n z) atTop (𝓝 (g z)) := by
    dsimp only [g]
    rw [dif_pos hz]
    exact Classical.choose_spec (exists_pointwise_limit f hc z hz)
  have hgoff (z : ℂ) (hz : z ∉ disk) : g z = 0 := by simp [g, hz]
  have hloc : TendstoLocallyUniformlyOn (fun n z => f n z) g atTop disk := by
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε z hz
    have hz' : ‖z‖ < 1 := by simpa [disk] using hz
    obtain ⟨t, hzt, ht⟩ := exists_between hz'
    have htd : ball (0 : ℂ) t ⊆ disk := ball_subset_ball ht.le
    have htend := (uniformCauchy_on_smaller_disk f hc t ht).tendstoUniformlyOn_of_tendsto
      (fun w hw => hglim w (htd hw))
    refine ⟨ball (0 : ℂ) t, mem_nhdsWithin_of_mem_nhds
      (isOpen_ball.mem_nhds (by simpa using hzt)), ?_⟩
    exact Metric.tendstoUniformlyOn_iff.mp htend ε hε
  have hghol : DifferentiableOn ℂ g disk :=
    hloc.differentiableOn (Eventually.of_forall (fun n => holomorphic (f n))) disk_open
  obtain ⟨ns, hns, hsub⟩ := (tendstoInMeasure_of_tendsto_Lp hconv).exists_seq_tendsto_ae
  have hrep : ∀ᵐ z ∂area, ∀ n, (toL2 (f n)) z = f n z := by
    rw [ae_all_iff]
    intro n
    exact (square_integrable (f n)).coeFn_toLp
  have hgeq : g =ᵐ[area] U := by
    filter_upwards [hsub, hrep, ae_restrict_mem disk_measurable] with z hsubz hrepz hz
    have hsubz' : Tendsto (fun i => f (ns i) z) atTop (𝓝 (U z)) := by
      simpa only [hrepz] using hsubz
    exact tendsto_nhds_unique ((hglim z hz).comp hns.tendsto_atTop) hsubz'
  have hgLp : MemLp g 2 area := (Lp.memLp U).ae_eq hgeq.symm
  let G : A2 := ⟨g, hghol, hgLp, hgoff⟩
  change U ∈ LinearMap.range toL2
  refine ⟨G, ?_⟩
  apply Lp.ext
  exact hgLp.coeFn_toLp.trans hgeq

/-- Completeness is proved from analytic closure, not assumed as a hypothesis. -/
instance l2Space_complete : CompleteSpace l2Space := l2Space_isClosed.completeSpace_coe

end Bergman930
