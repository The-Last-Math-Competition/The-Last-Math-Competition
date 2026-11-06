import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Round
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Conjecture5609
noncomputable section
open scoped BigOperators
abbrev E := EuclideanSpace ℝ (Fin 3)
def point (t : ℝ) (z : Fin 3 → ℤ) : E :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![t * z 0, (z 1 : ℝ), (z 2 : ℝ)]
def lattice (t : ℝ) : Set E := Set.range (point t)
def packingRadii (t : ℝ) : Set ℝ :=
  {r | 0 ≤ r ∧ ∀ z : Fin 3 → ℤ, z ≠ 0 → 2 * r ≤ ‖point t z‖}
def coveringRadii (t : ℝ) : Set ℝ :=
  {r | 0 ≤ r ∧ ∀ x : E, ∃ z : Fin 3 → ℤ, ‖x - point t z‖ ≤ r}
def packingRadius (t : ℝ) : ℝ := sSup (packingRadii t)
def coveringRadius (t : ℝ) : ℝ := sInf (coveringRadii t)
def gap (t : ℝ) : ℝ := coveringRadius t / packingRadius t

lemma norm_sq (x : E) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt]
  · simp [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]; ring
  · positivity
lemma point_coord (t : ℝ) (z : Fin 3 → ℤ) :
    point t z 0 = t * z 0 ∧ point t z 1 = z 1 ∧ point t z 2 = z 2 := by
  simp [point]
lemma point_add (t : ℝ) (z w : Fin 3 → ℤ) :
    point t (z + w) = point t z + point t w := by
  ext i; fin_cases i <;> simp [point, mul_add]
lemma point_neg (t : ℝ) (z : Fin 3 → ℤ) : point t (-z) = -point t z := by
  ext i; fin_cases i <;> simp [point]
lemma point_zero (t : ℝ) : point t 0 = 0 := by
  ext i; fin_cases i <;> simp [point]
lemma point_sub (t : ℝ) (z w : Fin 3 → ℤ) :
    point t (z-w) = point t z - point t w := by
  rw [sub_eq_add_neg, point_add, point_neg, sub_eq_add_neg]
def latticeGroup (t : ℝ) : AddSubgroup E where
  carrier := lattice t
  zero_mem' := ⟨0, point_zero t⟩
  add_mem' := by
    rintro x y ⟨z,rfl⟩ ⟨w,rfl⟩
    exact ⟨z+w, point_add t z w⟩
  neg_mem' := by
    rintro x ⟨z,rfl⟩
    exact ⟨-z, point_neg t z⟩
lemma point_injective {t : ℝ} (ht : 1 ≤ t) : Function.Injective (point t) := by
  intro z w h
  have h0 := congrArg (fun x : E => x 0) h
  have h1 := congrArg (fun x : E => x 1) h
  have h2 := congrArg (fun x : E => x 2) h
  change t * (z 0 : ℝ) = t * (w 0 : ℝ) at h0
  change (z 1 : ℝ) = (w 1 : ℝ) at h1
  change (z 2 : ℝ) = (w 2 : ℝ) at h2
  have ht0 : t ≠ 0 := by linarith
  have hz0 : z 0 = w 0 := by exact_mod_cast (mul_left_cancel₀ ht0 h0)
  have hz1 : z 1 = w 1 := by exact_mod_cast h1
  have hz2 : z 2 = w 2 := by exact_mod_cast h2
  funext i; fin_cases i <;> assumption
lemma integer_abs {z : ℤ} (hz : z ≠ 0) : (1 : ℝ) ≤ |(z : ℝ)| := by
  exact_mod_cast (Int.one_le_abs hz)
lemma spacing {t : ℝ} (ht : 1 ≤ t) (z : Fin 3 → ℤ) (hz : z ≠ 0) :
    1 ≤ ‖point t z‖ := by
  have he : ∃ i, z i ≠ 0 := by
    by_contra h; push_neg at h; exact hz (funext h)
  obtain ⟨i, hi⟩ := he
  have hbound := PiLp.norm_apply_le (p := (2 : ENNReal)) (point t z) i
  have ha := integer_abs hi
  fin_cases i
  · change |t * (z 0 : ℝ)| ≤ ‖point t z‖ at hbound
    change 1 ≤ |(z 0 : ℝ)| at ha
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ t)] at hbound
    nlinarith
  · simpa [point, Real.norm_eq_abs] using ha.trans hbound
  · simpa [point, Real.norm_eq_abs] using ha.trans hbound
lemma separation {t : ℝ} (ht : 1 ≤ t) (z w : Fin 3 → ℤ) (hz : z ≠ w) :
    1 ≤ dist (point t z) (point t w) := by
  rw [dist_eq_norm, ← point_sub]
  exact spacing ht (z-w) (sub_ne_zero.mpr hz)
lemma lattice_discrete {t : ℝ} (ht : 1 ≤ t) : DiscreteTopology (lattice t) := by
  apply discreteTopology_iff_singleton_mem_nhds.mpr
  intro x
  apply Metric.mem_nhds_iff.mpr
  refine ⟨1, zero_lt_one, ?_⟩
  intro y hy
  apply Set.mem_singleton_iff.mpr
  by_contra h
  obtain ⟨z,hz⟩ := x.property
  obtain ⟨w,hw⟩ := y.property
  have hzw : w ≠ z := by
    intro he; apply h; apply Subtype.ext
    rw [← hw, ← hz, he]
  have hd := separation ht w z hzw
  have hy' : dist (y : E) (x : E) < 1 := hy
  rw [← hw, ← hz] at hy'
  linarith
def basisVector (t : ℝ) (i : Fin 3) : E := point t (Pi.single i 1)
lemma real_decomposition {t : ℝ} (ht : 1 ≤ t) (x : E) :
    x = (x 0/t) • basisVector t 0 + x 1 • basisVector t 1 + x 2 • basisVector t 2 := by
  have ht0 : t ≠ 0 := by linarith
  ext i; fin_cases i <;> simp [basisVector, point, ht0]
lemma lattice_full_rank {t : ℝ} (ht : 1 ≤ t) : Submodule.span ℝ (lattice t) = ⊤ := by
  have hb (i : Fin 3) : basisVector t i ∈ Submodule.span ℝ (lattice t) :=
    Submodule.subset_span ⟨Pi.single i 1, rfl⟩
  apply top_unique
  intro x _
  rw [real_decomposition ht x]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (hb 0))
    (Submodule.smul_mem _ _ (hb 1))) (Submodule.smul_mem _ _ (hb 2))
lemma packing_geometric {t : ℝ} (ht : 1 ≤ t) (r : ℝ) :
    r ∈ packingRadii t ↔ 0 ≤ r ∧
      ∀ u ∈ lattice t, ∀ v ∈ lattice t, u ≠ v → 2*r ≤ dist u v := by
  constructor
  · rintro ⟨hr,hp⟩
    refine ⟨hr,?_⟩
    rintro u ⟨z,rfl⟩ v ⟨w,rfl⟩ hne
    have hzw : z ≠ w := by intro he; exact hne (congrArg (point t) he)
    rw [dist_eq_norm, ← point_sub]
    exact hp (z-w) (sub_ne_zero.mpr hzw)
  · rintro ⟨hr,hp⟩
    refine ⟨hr,?_⟩
    intro z hz
    have hne : point t z ≠ point t 0 := fun h => hz ((point_injective ht) h)
    have h := hp (point t z) ⟨z,rfl⟩ (point t 0) ⟨0,rfl⟩ hne
    simpa [point_zero, dist_eq_norm] using h
lemma packing_exact {t : ℝ} (ht : 1 ≤ t) : packingRadius t = 1 / 2 := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨by norm_num, ?_⟩, ?_⟩
  · intro z hz; simpa using spacing ht z hz
  · intro r hr
    have hz : (![0,1,0] : Fin 3 → ℤ) ≠ 0 := by
      intro h; have := congrFun h 1; norm_num at this
    have h := hr.2 ![0,1,0] hz
    have he : point t ![0,1,0] = EuclideanSpace.single 1 (1 : ℝ) := by
      ext i; fin_cases i <;> simp [point, EuclideanSpace.single_apply]
    rw [he, EuclideanSpace.norm_single] at h
    norm_num at h; linarith
lemma half_integer (z : ℤ) : (1 / 2 : ℝ) ≤ |1 / 2 - (z : ℝ)| := by
  by_cases hz : z ≤ 0
  · have hc : (z : ℝ) ≤ 0 := by exact_mod_cast hz
    rw [abs_of_nonneg (by linarith)]; linarith
  · have hz1 : 1 ≤ z := by omega
    have hc : (1 : ℝ) ≤ z := by exact_mod_cast hz1
    rw [abs_of_nonpos (by linarith)]; linarith
def centre (t : ℝ) : E := (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![t/2, (1:ℝ)/2, (1:ℝ)/2]
lemma centre_lower {t : ℝ} (ht : 1 ≤ t) (z : Fin 3 → ℤ) :
    Real.sqrt (t^2 + 2) / 2 ≤ ‖centre t - point t z‖ := by
  have h0 := half_integer (z 0)
  have h1 := half_integer (z 1)
  have h2 := half_integer (z 2)
  have hs := norm_sq (centre t - point t z)
  conv_rhs at hs => simp [centre, point]
  have h0sq : (1/2 - (z 0 : ℝ))^2 ≥ (1/2:ℝ)^2 := by
    nlinarith [sq_abs (1/2 - (z 0 : ℝ))]
  have h1sq : (1/2 - (z 1 : ℝ))^2 ≥ (1/2:ℝ)^2 := by
    nlinarith [sq_abs (1/2 - (z 1 : ℝ))]
  have h2sq : (1/2 - (z 2 : ℝ))^2 ≥ (1/2:ℝ)^2 := by
    nlinarith [sq_abs (1/2 - (z 2 : ℝ))]
  have h0scale : (t/2-t*(z 0 : ℝ))^2 = t^2 * (1/2-(z 0 : ℝ))^2 := by ring
  have hm := mul_le_mul_of_nonneg_left h0sq (sq_nonneg t)
  have hr := Real.sq_sqrt (show 0 ≤ t^2+2 by positivity)
  have hp := Real.sqrt_nonneg (t^2+2)
  have hn := norm_nonneg (centre t - point t z)
  nlinarith
lemma covering_attained {t : ℝ} (ht : 1 ≤ t) :
    Real.sqrt (t^2+2)/2 ∈ coveringRadii t := by
  refine ⟨by positivity, ?_⟩
  intro x
  let z : Fin 3 → ℤ := ![round (x 0/t), round (x 1), round (x 2)]
  refine ⟨z, ?_⟩
  have h0 := abs_sub_round (x 0/t)
  have h1 := abs_sub_round (x 1)
  have h2 := abs_sub_round (x 2)
  have ht0 : t ≠ 0 := by linarith
  have hs := norm_sq (x - point t z)
  simp [point, z] at hs
  have h0sq : (x 0/t-(round (x 0/t):ℝ))^2 ≤ (1/2:ℝ)^2 := by
    nlinarith [sq_abs (x 0/t-(round (x 0/t):ℝ)), abs_nonneg (x 0/t-(round (x 0/t):ℝ))]
  have h1sq : (x 1-(round (x 1):ℝ))^2 ≤ (1/2:ℝ)^2 := by
    nlinarith [sq_abs (x 1-(round (x 1):ℝ)), abs_nonneg (x 1-(round (x 1):ℝ))]
  have h2sq : (x 2-(round (x 2):ℝ))^2 ≤ (1/2:ℝ)^2 := by
    nlinarith [sq_abs (x 2-(round (x 2):ℝ)), abs_nonneg (x 2-(round (x 2):ℝ))]
  have he : (x 0-t*(round (x 0/t):ℝ))^2 = t^2*(x 0/t-(round (x 0/t):ℝ))^2 := by
    field_simp
  have hm := mul_le_mul_of_nonneg_left h0sq (sq_nonneg t)
  have hr := Real.sq_sqrt (show 0 ≤ t^2+2 by positivity)
  have hp := Real.sqrt_nonneg (t^2+2)
  have hn := norm_nonneg (x - point t z)
  change ‖x - point t z‖ ^ 2 = _ at hs
  nlinarith
lemma covering_exact {t : ℝ} (ht : 1 ≤ t) :
    coveringRadius t = Real.sqrt (t^2+2)/2 := by
  apply IsLeast.csInf_eq
  refine ⟨covering_attained ht, ?_⟩
  intro r hr
  obtain ⟨z,hz⟩ := hr.2 (centre t)
  exact (centre_lower ht z).trans hz
theorem gap_exact {t : ℝ} (ht : 1 ≤ t) : gap t = Real.sqrt (t^2+2) := by
  rw [gap, covering_exact ht, packing_exact ht]; ring
theorem gap_unbounded (B : ℝ) : ∃ t : ℝ, 1 ≤ t ∧ B < gap t := by
  let t := max 1 (B+1)
  have ht : 1 ≤ t := le_max_left _ _
  refine ⟨t,ht,?_⟩
  rw [gap_exact ht]
  have hB : B+1 ≤ t := le_max_right _ _
  have hs := Real.sq_sqrt (show 0 ≤ t^2+2 by positivity)
  have hp := Real.sqrt_nonneg (t^2+2)
  nlinarith

theorem valid_lattice_unbounded (B : ℝ) : ∃ t : ℝ,
    1 ≤ t ∧ DiscreteTopology (lattice t) ∧
    Submodule.span ℝ (lattice t) = ⊤ ∧ B < gap t := by
  obtain ⟨t,ht,hB⟩ := gap_unbounded B
  exact ⟨t,ht,lattice_discrete ht,lattice_full_rank ht,hB⟩
theorem cubic_gap : gap 1 = Real.sqrt 3 := by
  rw [gap_exact (by norm_num : (1:ℝ) ≤ 1)]
  norm_num
theorem rectangular_exceeds_cubic : gap 1 < gap 4 := by
  rw [cubic_gap, gap_exact (by norm_num : (1:ℝ) ≤ 4)]
  norm_num
theorem no_upper_endpoint : ¬ ∃ B : ℝ, ∀ t : ℝ, 1 ≤ t → gap t ≤ B := by
  rintro ⟨B,h⟩
  obtain ⟨t,ht,hB⟩ := gap_unbounded B
  exact (not_lt_of_ge (h t ht)) hB

#print axioms gap_unbounded
#print axioms valid_lattice_unbounded
#print axioms packing_geometric
#print axioms packing_exact
#print axioms covering_exact
#print axioms rectangular_exceeds_cubic
end
end Conjecture5609

