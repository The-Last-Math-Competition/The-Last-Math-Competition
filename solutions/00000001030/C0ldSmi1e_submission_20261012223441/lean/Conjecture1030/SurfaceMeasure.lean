import Conjecture1030.Definitions

noncomputable section
open scoped BigOperators ENNReal NNReal RealInnerProductSpace
open MeasureTheory Metric Set
namespace Conjecture1030
set_option maxHeartbeats 1200000

/-- Rational stereographic parametrization, with the last coordinate sign ε. -/
def stereo (ε : ℝ) (u : E2) : E :=
  !₂[2 * u 0 / (1 + ‖u‖ ^ 2), 2 * u 1 / (1 + ‖u‖ ^ 2),
    ε * ((1 - ‖u‖ ^ 2) / (1 + ‖u‖ ^ 2))]

 theorem stereo_denom_pos (u : E2) : 0 < 1 + ‖u‖ ^ 2 := by positivity

 theorem stereo_norm_sq (ε : ℝ) (hε : ε ^ 2 = 1) (u : E2) :
    ‖stereo ε u‖ ^ 2 = 1 := by
  have hd := ne_of_gt (stereo_denom_pos u)
  rw [norm_sq3]
  change (2 * u 0 / (1 + ‖u‖ ^ 2)) ^ 2 + (2 * u 1 / (1 + ‖u‖ ^ 2)) ^ 2 +
    (ε * ((1 - ‖u‖ ^ 2) / (1 + ‖u‖ ^ 2))) ^ 2 = 1
  rw [mul_pow ε, hε, one_mul]
  field_simp
  nlinarith [norm_sq2 u]

 theorem stereo_mem_sphere (ε : ℝ) (hε : ε ^ 2 = 1) (u : E2) :
    stereo ε u ∈ Metric.sphere (0 : E) 1 := by
  rw [Metric.mem_sphere, dist_zero_right]
  have h := stereo_norm_sq ε hε u
  nlinarith [norm_nonneg (stereo ε u)]

 theorem stereo_chordal (ε : ℝ) (hε : ε ^ 2 = 1) (u v : E2) :
    ‖stereo ε u - stereo ε v‖ ^ 2 * ((1 + ‖u‖ ^ 2) * (1 + ‖v‖ ^ 2)) =
      4 * ‖u - v‖ ^ 2 := by
  have hu := ne_of_gt (stereo_denom_pos u)
  have hv := ne_of_gt (stereo_denom_pos v)
  rw [norm_sq3]
  change ((2 * u 0 / (1 + ‖u‖ ^ 2) - 2 * v 0 / (1 + ‖v‖ ^ 2)) ^ 2 +
    (2 * u 1 / (1 + ‖u‖ ^ 2) - 2 * v 1 / (1 + ‖v‖ ^ 2)) ^ 2 +
    (ε * ((1 - ‖u‖ ^ 2) / (1 + ‖u‖ ^ 2)) -
     ε * ((1 - ‖v‖ ^ 2) / (1 + ‖v‖ ^ 2))) ^ 2) *
    ((1 + ‖u‖ ^ 2) * (1 + ‖v‖ ^ 2)) = 4 * ‖u - v‖ ^ 2
  rw [← mul_sub ε, mul_pow ε, hε, one_mul]
  field_simp
  simp only [norm_sq2, PiLp.sub_apply]
  ring

 theorem stereo_lipschitz (ε : ℝ) (hε : ε ^ 2 = 1) : LipschitzWith 2 (stereo ε) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [dist_eq_norm, dist_eq_norm]
  have hc := stereo_chordal ε hε u v
  have hp : 1 ≤ (1 + ‖u‖ ^ 2) * (1 + ‖v‖ ^ 2) := by
    nlinarith [sq_nonneg ‖u‖, sq_nonneg ‖v‖, mul_nonneg (sq_nonneg ‖u‖) (sq_nonneg ‖v‖)]
  have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg ‖stereo ε u - stereo ε v‖)
  norm_num at ⊢
  nlinarith [norm_nonneg (stereo ε u - stereo ε v), norm_nonneg (u - v)]

 theorem stereo_hemisphere (ε : ℝ) (hε : ε ^ 2 = 1) (x : E)
    (hx : ‖x‖ = 1) (hside : 0 ≤ ε * x 2) :
    ∃ u ∈ closedBall (0 : E2) 1, stereo ε u = x := by
  let t := ε * x 2
  have ht0 : 0 ≤ t := hside
  have hd : 0 < 1 + t := by linarith
  have hd0 : 1 + t ≠ 0 := ne_of_gt hd
  have ht2 : t ^ 2 = x 2 ^ 2 := by dsimp [t]; rw [mul_pow, hε, one_mul]
  have hxt : ε * t = x 2 := by
    dsimp [t]
    nlinarith [congrArg (fun q : ℝ => q * x 2) hε]
  have hxs : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1 := by rw [← norm_sq3, hx]; norm_num
  let u : E2 := !₂[x 0 / (1 + t), x 1 / (1 + t)]
  have hu : ‖u‖ ^ 2 = (1 - t) / (1 + t) := by
    rw [norm_sq2]
    change (x 0 / (1 + t)) ^ 2 + (x 1 / (1 + t)) ^ 2 = (1 - t) / (1 + t)
    field_simp
    nlinarith [hxs, ht2]
  have hud : 1 + ‖u‖ ^ 2 = 2 / (1 + t) := by
    rw [hu]
    field_simp
    ring
  refine ⟨u, ?_, ?_⟩
  · rw [mem_closedBall, dist_zero_right]
    have hfrac : (1 - t) / (1 + t) ≤ 1 := (div_le_iff₀ hd).2 (by linarith)
    nlinarith [norm_nonneg u]
  · apply PiLp.ext
    intro i
    fin_cases i
    · change 2 * (x 0 / (1 + t)) / (1 + ‖u‖ ^ 2) = x 0
      rw [hud]
      field_simp
    · change 2 * (x 1 / (1 + t)) / (1 + ‖u‖ ^ 2) = x 1
      rw [hud]
      field_simp
    · change ε * ((1 - ‖u‖ ^ 2) / (1 + ‖u‖ ^ 2)) = x 2
      rw [hud, hu]
      field_simp
      nlinarith [hxt]

 theorem sphere_stereo_cover : Metric.sphere (0 : E) 1 ⊆
    stereo 1 '' closedBall (0 : E2) 1 ∪ stereo (-1) '' closedBall (0 : E2) 1 := by
  intro x hx
  have hnorm : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
  by_cases hs : 0 ≤ x 2
  · obtain ⟨u, hu, hux⟩ := stereo_hemisphere 1 (by norm_num) x hnorm (by simpa)
    exact Or.inl ⟨u, hu, hux⟩
  · obtain ⟨u, hu, hux⟩ := stereo_hemisphere (-1) (by norm_num) x hnorm (by linarith)
    exact Or.inr ⟨u, hu, hux⟩

/-- Coordinate projection for the actual Euclidean metrics. -/
def planeProjection (x : E) : E2 := !₂[x 0, x 1]

 theorem planeProjection_lipschitz : LipschitzWith 1 planeProjection := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have hp : ‖planeProjection x - planeProjection y‖ ^ 2 =
      (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
    rw [norm_sq2]
    rfl
  have hx := norm_sq3 (x - y)
  simp only [PiLp.sub_apply] at hx
  nlinarith [sq_nonneg (x 2 - y 2), norm_nonneg (x - y),
    norm_nonneg (planeProjection x - planeProjection y)]

 theorem planeProjection_sphere : planeProjection '' Metric.sphere (0 : E) 1 =
    closedBall (0 : E2) 1 := by
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
    rw [mem_closedBall, dist_zero_right]
    have hp : ‖planeProjection x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by rw [norm_sq2]; rfl
    have hn := norm_sq3 x
    rw [hx'] at hn
    nlinarith [sq_nonneg (x 2), norm_nonneg (planeProjection x)]
  · intro hu
    have hu' : ‖u‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hu
    have hs : 0 ≤ 1 - ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
    let x : E := !₂[u 0, u 1, Real.sqrt (1 - ‖u‖ ^ 2)]
    refine ⟨x, ?_, ?_⟩
    · rw [mem_sphere, dist_zero_right]
      have hx : ‖x‖ ^ 2 = 1 := by
        rw [norm_sq3]
        change u 0 ^ 2 + u 1 ^ 2 + (Real.sqrt (1 - ‖u‖ ^ 2)) ^ 2 = 1
        rw [Real.sq_sqrt hs]
        nlinarith [norm_sq2 u]
      nlinarith [norm_nonneg x]
    · apply PiLp.ext
      intro i
      fin_cases i <;> rfl

/-- Dimension two Hausdorff measure is Haar on Euclidean two-space, not on E or S2. -/
instance planeHausdorffHaar :
    (Measure.hausdorffMeasure (2 : ℝ) : Measure E2).IsAddHaarMeasure := by
  simpa using (MeasureTheory.isAddHaarMeasure_hausdorffMeasure (E := E2))

 theorem plane_disk_mass_lt_top :
    (Measure.hausdorffMeasure (2 : ℝ) : Measure E2) (closedBall 0 1) < ∞ :=
  (isCompact_closedBall (0 : E2) 1).measure_lt_top

 theorem ambient_sphere_mass_lt_top :
    (Measure.hausdorffMeasure (2 : ℝ) : Measure E) (sphere 0 1) < ∞ := by
  have hp := (stereo_lipschitz 1 (by norm_num)).hausdorffMeasure_image_le
    (d := 2) (by norm_num) (closedBall (0 : E2) 1)
  have hn := (stereo_lipschitz (-1) (by norm_num)).hausdorffMeasure_image_le
    (d := 2) (by norm_num) (closedBall (0 : E2) 1)
  have hc : ((2 : ℝ≥0) : ℝ≥0∞) ^ (2 : ℝ) < ∞ := by norm_num
  have hfinite := ENNReal.mul_lt_top hc plane_disk_mass_lt_top
  apply lt_of_le_of_lt (measure_mono sphere_stereo_cover)
  apply lt_of_le_of_lt (measure_union_le _ _)
  exact ENNReal.add_lt_top.mpr ⟨lt_of_le_of_lt hp hfinite, lt_of_le_of_lt hn hfinite⟩

 theorem ambient_sphere_mass_pos :
    0 < (Measure.hausdorffMeasure (2 : ℝ) : Measure E) (sphere 0 1) := by
  have hball := Metric.measure_ball_pos
    (Measure.hausdorffMeasure (2 : ℝ) : Measure E2) (0 : E2) (show (0 : ℝ) < 1 by norm_num)
  have hp := planeProjection_lipschitz.hausdorffMeasure_image_le
    (d := 2) (by norm_num) (sphere (0 : E) 1)
  rw [planeProjection_sphere] at hp
  norm_num at hp
  exact lt_of_lt_of_le (lt_of_lt_of_le hball (measure_mono ball_subset_closedBall)) hp

/-- Intrinsic surface measure is exactly ambient H² restricted to the sphere. -/
 theorem map_surface : Measure.map (Subtype.val : S2 → E) surface =
    (Measure.hausdorffMeasure 2 : Measure E).restrict (sphere 0 1) := by
  simpa only [surface, Subtype.range_coe] using
    (isometry_subtype_coe (s := sphere (0 : E) 1)).map_hausdorffMeasure
      (d := 2) (Or.inl (by norm_num))

 theorem surface_mass_eq : surface Set.univ =
    (Measure.hausdorffMeasure 2 : Measure E) (sphere 0 1) := by
  symm
  simpa only [surface, Set.image_univ, Subtype.range_coe] using
    (isometry_subtype_coe (s := sphere (0 : E) 1)).hausdorffMeasure_image
      (d := 2) (Or.inl (by norm_num)) (Set.univ : Set S2)

 theorem surface_mass_pos : 0 < surface Set.univ := by
  rw [surface_mass_eq]
  exact ambient_sphere_mass_pos

 theorem surface_mass_lt_top : surface Set.univ < ∞ := by
  rw [surface_mass_eq]
  exact ambient_sphere_mass_lt_top

instance surfaceFinite : IsFiniteMeasure surface := ⟨surface_mass_lt_top⟩
instance surfaceNonzero : NeZero surface := ⟨Measure.measure_univ_pos.mp surface_mass_pos⟩
instance sigmaProbability : IsProbabilityMeasure sigma := by
  unfold sigma
  infer_instance

 theorem sigma_orthogonallyInvariant : OrthogonallyInvariant sigma := by
  intro U
  exact ((sphereIso U).measurePreserving_hausdorffMeasure 2).smul_measure (surface Set.univ)⁻¹

/-- Every polynomial restricted to the genuine sphere is measurable and integrable. -/
 theorem evalOnSphere_continuous (p : MvPolynomial (Fin 3) ℝ) :
    Continuous (evalOnSphere p) := by
  exact p.continuous_eval.comp (by fun_prop)

 theorem evalOnSphere_integrable (p : MvPolynomial (Fin 3) ℝ) :
    Integrable (evalOnSphere p) sigma := by
  have h := (evalOnSphere_continuous p).continuousOn.integrableOn_compact
    (μ := sigma) (isCompact_univ : IsCompact (Set.univ : Set S2))
  simpa only [integrableOn_univ] using h

end Conjecture1030
