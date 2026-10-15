import PowerCells
import NoSphere
import K5Rotation

namespace PowerCells6685

/-- The actual five-site facet graph is complete, all sites are visible, all
four-site affine determinants are nonzero, and no K₅ rotation system can have
the face count required by a spherical embedding. The paper explicitly proves
the real-geometric and topological interpretation of these certificates. -/
theorem finite_counterexample_certificates :
    (∀ i j : Fin 5, FacetAdjacent i j ↔ i ≠ j) ∧
    (∀ i k : Fin 5, i ≠ k → power i (site i) < power k (site i)) ∧
    (∀ i j k l : Fin 5,
      i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      orientedVolume i j k l ≠ 0) ∧
    (∀ R : K5Rotation.RotationSystem, ∀ D : K5Rotation.FacialDecomposition R,
      (5 : Int) - 10 + Int.ofNat (K5Rotation.faceCount D) ≠ 2) :=
  ⟨adjacency_complete, own_site_strict, every_four_independent,
    K5Rotation.no_spherical_euler_equation⟩

end PowerCells6685
