import Conjecture1030.Icosahedron
import Mathlib.Analysis.InnerProductSpace.Projection

noncomputable section
open scoped BigOperators ENNReal RealInnerProductSpace
open MeasureTheory Metric Set
namespace Conjecture1030

/-- Orthogonal congruence to the displayed twelve distinct unit vectors. -/
def IsIcosahedral (X : Finset S2) : Prop :=
  ∃ U : E ≃ₗᵢ[ℝ] E, X.image (sphereIso U) = ico

/-- The positive off-diagonal inner product of adjacent normalized vertices. -/
def icoAngle : ℝ := icoA * icoB

theorem icoAngle_pos : 0 < icoAngle := mul_pos icoA_pos icoB_pos
theorem icoAngle_sq : icoAngle ^ 2 = 1 / 5 := by
  simpa [icoAngle, mul_pow] using icoA_sq_mul_icoB_sq
theorem icoAngle_lt_one : icoAngle < 1 := by nlinarith [icoAngle_sq, icoAngle_pos]
theorem icoAngle_ne_one : icoAngle ≠ 1 := ne_of_lt icoAngle_lt_one

theorem icoAngle_phi_div : icoAngle = phi / r ^ 2 := by
  unfold icoAngle icoA icoB
  ring

@[simp] theorem ico_inner_canonical :
    ⟪(icoVertex 0 : E), (icoVertex 2 : E)⟫ = icoAngle := ico_canonical_inner

/-- On the unit sphere, inner product minus one characterizes the antipode. -/
theorem sphere_inner_neg_one_iff (x y : S2) :
    ⟪(x : E), (y : E)⟫ = -1 ↔ (y : E) = -(x : E) := by
  constructor
  · intro h
    have hs : ‖(x : E) + (y : E)‖ ^ 2 = 0 := by
      rw [norm_add_sq_real, sphere_norm, sphere_norm, h]
      norm_num
    have he : (x : E) + (y : E) = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hs)
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using he)
  · intro h
    rw [h, inner_neg_right, real_inner_self_eq_norm_sq, sphere_norm]
    norm_num

/-- Independent sign symmetry includes antipodal closure of the coordinate set. -/
theorem ico_antipodal_mem (x y : S2) (hy : (y : E) = -(x : E))
    (hx : x ∈ ico) : y ∈ ico := by
  apply ico_sign_symmetry x y ?_ hx
  intro i
  right
  simpa using congrArg (fun v : E => v i) hy

/-- Two explicitly constructed orthogonal reflections align any canonical-angle pair. -/
theorem ico_pair_alignment (x y : S2)
    (hxy : ⟪(x : E), (y : E)⟫ = icoAngle) :
    ∃ U : E ≃ₗᵢ[ℝ] E,
      U (x : E) = (icoVertex 0 : E) ∧ U (y : E) = (icoVertex 2 : E) := by
  let R₁ : E ≃ₗᵢ[ℝ] E :=
    Submodule.reflection (ℝ ∙ ((x : E) - (icoVertex 0 : E)))ᗮ
  have hx : R₁ (x : E) = (icoVertex 0 : E) :=
    Submodule.reflection_sub (by simp only [LinearIsometryEquiv.norm_map, sphere_norm])
  let R₂ : E ≃ₗᵢ[ℝ] E :=
    Submodule.reflection (ℝ ∙ (R₁ (y : E) - (icoVertex 2 : E)))ᗮ
  have hy : R₂ (R₁ (y : E)) = (icoVertex 2 : E) :=
    Submodule.reflection_sub (by simp only [LinearIsometryEquiv.norm_map, sphere_norm])
  have hfix : R₂ (icoVertex 0 : E) = (icoVertex 0 : E) := by
    apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right]
    have hinner : ⟪(icoVertex 0 : E), R₁ (y : E)⟫ = icoAngle := by
      rw [← hx, R₁.inner_map_map]
      exact hxy
    rw [hinner, ico_inner_canonical]
    exact sub_self _
  refine ⟨R₁.trans R₂, ?_, ?_⟩
  · simpa only [LinearIsometryEquiv.trans_apply, hx] using hfix
  · exact hy

/-- Every upper point, after pair alignment, belongs to the displayed coordinate set. -/
theorem ico_aligned_upper_mem (X : Finset S2)
    (hroot : ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
      ⟪(x : E), (y : E)⟫ = -1 ∨ ⟪(x : E), (y : E)⟫ = icoAngle ∨
        ⟪(x : E), (y : E)⟫ = -icoAngle)
    (x y : S2) (hy : y ∈ X) (hxy : ⟪(x : E), (y : E)⟫ = icoAngle)
    (U : E ≃ₗᵢ[ℝ] E) (hUx : U (x : E) = (icoVertex 0 : E))
    (hUy : U (y : E) = (icoVertex 2 : E))
    (z : S2) (hz : z ∈ X) (hxz : ⟪(x : E), (z : E)⟫ = icoAngle) :
    sphereIso U z ∈ ico := by
  by_cases hzy : z = y
  · have he : sphereIso U z = icoVertex 2 := by
      apply Subtype.ext
      simpa only [sphereIso_coe, hzy] using hUy
    rw [he]
    exact (mem_ico _).2 ⟨2, rfl⟩
  have hyz := hroot y hy z hz (Ne.symm hzy)
  rcases hyz with hyz | hyz
  · have hn := (sphere_inner_neg_one_iff y z).1 hyz
    rw [hn, inner_neg_right, hxy] at hxz
    linarith [icoAngle_pos]
  · apply ico_upper_candidates
    · change ⟪(icoVertex 0 : E), U (z : E)⟫ = icoA * icoB
      rw [← hUx, U.inner_map_map]
      exact hxz
    · change ⟪(icoVertex 2 : E), U (z : E)⟫ = icoA * icoB ∨
        ⟪(icoVertex 2 : E), U (z : E)⟫ = -(icoA * icoB)
      rw [← hUy, U.inner_map_map]
      exact hyz

/-- Antipodal closure reduces lower points to the preceding upper-point exhaustion. -/
theorem ico_aligned_all_mem (X : Finset S2)
    (hanti : ∀ z ∈ X, ∃ z' ∈ X, (z' : E) = -(z : E))
    (hroot : ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
      ⟪(x : E), (y : E)⟫ = -1 ∨ ⟪(x : E), (y : E)⟫ = icoAngle ∨
        ⟪(x : E), (y : E)⟫ = -icoAngle)
    (x y : S2) (hx : x ∈ X) (hy : y ∈ X)
    (hxy : ⟪(x : E), (y : E)⟫ = icoAngle)
    (U : E ≃ₗᵢ[ℝ] E) (hUx : U (x : E) = (icoVertex 0 : E))
    (hUy : U (y : E) = (icoVertex 2 : E))
    (z : S2) (hz : z ∈ X) : sphereIso U z ∈ ico := by
  have hxmem : sphereIso U x ∈ ico := by
    have he : sphereIso U x = icoVertex 0 := Subtype.ext hUx
    rw [he]
    exact (mem_ico _).2 ⟨0, rfl⟩
  by_cases hzx : z = x
  · simpa only [hzx] using hxmem
  rcases hroot x hx z hz (Ne.symm hzx) with hxz | hxz | hxz
  · have hn := (sphere_inner_neg_one_iff x z).1 hxz
    apply ico_antipodal_mem (sphereIso U x) (sphereIso U z) ?_ hxmem
    simp only [sphereIso_coe, hn, map_neg]
  · exact ico_aligned_upper_mem X hroot x y hy hxy U hUx hUy z hz hxz
  · obtain ⟨z', hz', hn⟩ := hanti z hz
    have hxz' : ⟪(x : E), (z' : E)⟫ = icoAngle := by
      rw [hn, inner_neg_right, hxz, neg_neg]
    have hz'mem := ico_aligned_upper_mem X hroot x y hy hxy U hUx hUy z' hz' hxz'
    apply ico_antipodal_mem (sphereIso U z') (sphereIso U z) ?_ hz'mem
    simp only [sphereIso_coe, hn, map_neg, neg_neg]

/-- The numerical equality conditions force orthogonal congruence to the explicit icosahedron. -/
theorem ico_rigidity_of_inner_products (X : Finset S2) (hcard : X.card = 12)
    (hanti : ∀ x ∈ X, ∃ y ∈ X, (y : E) = -(x : E))
    (hroot : ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
      ⟪(x : E), (y : E)⟫ = -1 ∨ ⟪(x : E), (y : E)⟫ = icoAngle ∨
        ⟪(x : E), (y : E)⟫ = -icoAngle) : IsIcosahedral X := by
  classical
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < X.card by omega)
  obtain ⟨xn, hxn, hn⟩ := hanti x hx
  have htwo : ({x, xn} : Finset S2).card < X.card := by
    rw [hcard]
    exact lt_of_le_of_lt Finset.card_le_two (by norm_num)
  obtain ⟨z, hz, hznot⟩ := Finset.exists_mem_not_mem_of_card_lt_card htwo
  have hzx : z ≠ x := by intro he; apply hznot; simp [he]
  have hzn : z ≠ xn := by intro he; apply hznot; simp [he]
  have hp : ∃ y ∈ X, ⟪(x : E), (y : E)⟫ = icoAngle := by
    rcases hroot x hx z hz (Ne.symm hzx) with hxz | hxz | hxz
    · have hzv := (sphere_inner_neg_one_iff x z).1 hxz
      exact False.elim (hzn (Subtype.ext (hzv.trans hn.symm)))
    · exact ⟨z, hz, hxz⟩
    · obtain ⟨zn, hzn, hnz⟩ := hanti z hz
      refine ⟨zn, hzn, ?_⟩
      rw [hnz, inner_neg_right, hxz, neg_neg]
  obtain ⟨y, hy, hxy⟩ := hp
  obtain ⟨U, hUx, hUy⟩ := ico_pair_alignment x y hxy
  refine ⟨U, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    exact ico_aligned_all_mem X hanti hroot x y hx hy hxy U hUx hUy z hz
  · rw [Finset.card_image_of_injective X (sphereIso U).injective, ico_card, hcard]

/-- Orthogonal congruence preserves the cardinality of the displayed coordinate set. -/
theorem IsIcosahedral.card {X : Finset S2} (hX : IsIcosahedral X) : X.card = 12 := by
  classical
  obtain ⟨U, hU⟩ := hX
  have hc := congrArg Finset.card hU
  simpa only [Finset.card_image_of_injective X (sphereIso U).injective, ico_card] using hc

end Conjecture1030
