import Conjecture1030.DesignExactness
import Conjecture1030.IcosahedronRigidity

noncomputable section
open scoped BigOperators ENNReal RealInnerProductSpace
open MeasureTheory Metric Set
namespace Conjecture1030

/-- The explicit twelve-point set is exact for every polynomial of total degree at most five,
against normalized genuine Hausdorff surface measure. -/
theorem ico_is_spherical_five_design : SphericalDesign 5 ico :=
  (designFor_sigma 5 ico).mp (ico_designFor sigma sigma_orthogonallyInvariant)

 theorem twelve_design_antipodal (X : Finset S2) (hX : SphericalDesign 5 X)
    (hcard : X.card = 12) : ∀ x ∈ X, ∃ y ∈ X, (y : E) = -(x : E) := by
  intro x hx
  apply exists_antipode_of_squared_sum X x hx hcard
  · intro y hy hxy
    exact sphere_inner_roots_of_twelve X x y hx hy hxy hcard (design_sum_lpValue X hX x)
  · have h := design_sum_dot_pow X hX x 2 (by norm_num)
    norm_num only [hcard, ite_false, ite_true] at h
    exact h

 theorem twelve_design_inner_products (X : Finset S2) (hX : SphericalDesign 5 X)
    (hcard : X.card = 12) : ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
      ⟪(x : E), (y : E)⟫ = -1 ∨ ⟪(x : E), (y : E)⟫ = icoAngle ∨
        ⟪(x : E), (y : E)⟫ = -icoAngle := by
  intro x hx y hy hxy
  rcases sphere_inner_roots_of_twelve X x y hx hy hxy hcard
    (design_sum_lpValue X hX x) with ht | ht
  · exact Or.inl ht
  · exact Or.inr (sq_eq_sq_iff_eq_or_eq_neg.mp (ht.trans icoAngle_sq.symm))

/-- Equality in the ordinary lower bound is rigid up to actual Euclidean orthogonal congruence. -/
theorem spherical_five_design_twelve_rigidity (X : Finset S2)
    (hX : SphericalDesign 5 X) (hcard : X.card = 12) : IsIcosahedral X :=
  ico_rigidity_of_inner_products X hcard (twelve_design_antipodal X hX hcard)
    (twelve_design_inner_products X hX hcard)

 theorem spherical_five_design_card_twelve_iff (X : Finset S2)
    (hX : SphericalDesign 5 X) : X.card = 12 ↔ IsIcosahedral X :=
  ⟨spherical_five_design_twelve_rigidity X hX, IsIcosahedral.card⟩

/-- If the icosahedral congruence class is excluded, twelve is impossible.
This does not assert that thirteen is attained. -/
theorem nonicosahedral_spherical_five_design_card_ge_thirteen (X : Finset S2)
    (hX : SphericalDesign 5 X) (hn : ¬ IsIcosahedral X) : 13 ≤ X.card := by
  have hb := spherical_five_design_card_ge_twelve X hX
  have he : X.card ≠ 12 := fun h => hn (spherical_five_design_twelve_rigidity X hX h)
  omega

/-- The standard class has attained minimum exactly twelve. -/
theorem spherical_five_design_minimum_twelve :
    (∃ X : Finset S2, SphericalDesign 5 X ∧ X.card = 12) ∧
    (∀ X : Finset S2, SphericalDesign 5 X → 12 ≤ X.card) :=
  ⟨⟨ico, ico_is_spherical_five_design, ico_card⟩, spherical_five_design_card_ge_twelve⟩

/-- Under the exclusion reading, the assertion of an attained minimum of twelve is false. -/
theorem no_twelve_point_nonicosahedral_spherical_five_design :
    ¬ ∃ X : Finset S2, SphericalDesign 5 X ∧ ¬ IsIcosahedral X ∧ X.card = 12 := by
  rintro ⟨X, hX, hn, hc⟩
  exact hn (spherical_five_design_twelve_rigidity X hX hc)

end Conjecture1030
