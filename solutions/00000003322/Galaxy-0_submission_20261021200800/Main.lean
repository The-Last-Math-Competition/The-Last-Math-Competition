import Principal
import TriangleBetti

namespace TLMC3322

/-- The K2 instance falsifies the equivalence under the literal ideal convention. -/
theorem ideal_convention_false :
    ¬ (Principal.Regularity 1 ↔ Graphs.Bipartite Graphs.K2 ∧ Graphs.Forest Graphs.K2) := by
  intro h
  exact Principal.regularity_not_one (h.mpr ⟨Graphs.K2_bipartite,Graphs.K2_forest⟩)

/-- The K3 instance falsifies the equivalence under the quotient-ring convention. -/
theorem quotient_convention_false :
    ¬ (Triangle.Regularity 1 ↔ Graphs.Bipartite Graphs.K3 ∧ Graphs.Forest Graphs.K3) := by
  intro h
  exact Graphs.K3_not_bipartite (h.mp Triangle.regularity_one).1

/-- Code-independent complete certificates: actual edge ideals and full minimal
resolutions, genuine graph matching numbers, and both normalization disproofs. -/
theorem complete_counterexamples :
    Principal.VerifiedMinimalResolution ∧ Triangle.VerifiedMinimalResolution ∧
    Graphs.Simple Graphs.K2 ∧ Graphs.Simple Graphs.K3 ∧
    Graphs.MatchingNumber Graphs.K2 1 ∧ Graphs.MatchingNumber Graphs.K3 1 ∧
    Principal.Regularity 2 ∧ Triangle.Regularity 1 ∧
    ¬ (Principal.Regularity 1 ↔ Graphs.Bipartite Graphs.K2 ∧ Graphs.Forest Graphs.K2) ∧
    ¬ (Triangle.Regularity 1 ↔ Graphs.Bipartite Graphs.K3 ∧ Graphs.Forest Graphs.K3) :=
  ⟨Principal.verified_minimal_resolution,Triangle.verified_minimal_resolution,
   Graphs.K2_simple,Graphs.K3_simple,Graphs.K2_matching_one,Graphs.K3_matching_one,
   Principal.regularity_two,Triangle.regularity_one,
   ideal_convention_false,quotient_convention_false⟩

end TLMC3322
